"""CLI entry point for the ATP checkers runner."""
from __future__ import annotations

import argparse
import asyncio
import re
import sys
from pathlib import Path

from . import __version__
from .loader import load_jsonl
from .executor import run_batch, DEFAULT_TIMEOUT
from .models import ParseError, LintResult, Provenance
from datetime import datetime, timezone


def main():
    parser = argparse.ArgumentParser(
        description="Run ATP checkers on a dataset of Lean problems",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python -m runner dataset.jsonl --workspace ./linter -o results/
  python -m runner problems.jsonl --workspace ./linter --timeout 60 -o out/
        """,
    )
    parser.add_argument(
        "dataset",
        type=Path,
        help="Path to JSONL dataset file",
    )
    parser.add_argument(
        "--workspace", "-w",
        type=Path,
        required=True,
        help="Path to pre-built Lean workspace with linter",
    )
    parser.add_argument(
        "--output", "-o",
        type=Path,
        required=True,
        help="Output directory for results",
    )
    parser.add_argument(
        "--toolchain",
        type=str,
        default=None,
        help="Lean toolchain string for provenance (default: read from workspace)",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=DEFAULT_TIMEOUT,
        help=f"Timeout per problem in seconds (default: {DEFAULT_TIMEOUT})",
    )
    parser.add_argument(
        "--workers", "-j",
        type=int,
        default=1,
        help="Number of parallel workers (default: 1 = sequential)",
    )
    parser.add_argument(
        "--append",
        action="store_true",
        help="Append to existing results.jsonl instead of failing if it exists",
    )
    parser.add_argument(
        "--skip-existing",
        action="store_true",
        help="Skip problems already in results.jsonl (for resuming interrupted runs). "
             "Assumes same toolchain/linter version; use fresh output dir for new runs.",
    )
    parser.add_argument(
        "--version",
        action="version",
        version=f"%(prog)s {__version__}",
    )

    args = parser.parse_args()

    # Validate inputs
    if not args.dataset.exists():
        print(f"Error: Dataset not found: {args.dataset}", file=sys.stderr)
        sys.exit(1)

    if not args.workspace.exists():
        print(f"Error: Workspace not found: {args.workspace}", file=sys.stderr)
        sys.exit(1)

    # Read toolchain from workspace
    workspace_toolchain = None
    toolchain_file = args.workspace / "lean-toolchain"
    if toolchain_file.exists():
        workspace_toolchain = toolchain_file.read_text().strip()

    # Determine effective toolchain (strict enforcement)
    if args.toolchain is not None:
        toolchain = args.toolchain
        # Fail if it differs from workspace - mismatched toolchains produce unreliable results
        if workspace_toolchain and workspace_toolchain != toolchain:
            print(f"Error: --toolchain '{toolchain}' differs from workspace toolchain '{workspace_toolchain}'", file=sys.stderr)
            print("       The workspace was built with a different toolchain. Results would be unreliable.", file=sys.stderr)
            print("       Either rebuild the workspace with the specified toolchain, or omit --toolchain.", file=sys.stderr)
            sys.exit(1)
    elif workspace_toolchain:
        toolchain = workspace_toolchain
    else:
        print("Error: Could not determine toolchain. Specify --toolchain or ensure workspace has lean-toolchain file.", file=sys.stderr)
        sys.exit(1)

    # Create output directory
    args.output.mkdir(parents=True, exist_ok=True)
    results_file = args.output / "results.jsonl"
    logs_dir = args.output / "logs"

    # Check if results file exists
    if results_file.exists() and not args.append and not args.skip_existing:
        print(f"Error: {results_file} already exists. Use --append to add to it, --skip-existing to resume, or remove the file.", file=sys.stderr)
        sys.exit(1)

    # Load existing problem IDs if resuming
    existing_ids = set()
    if args.skip_existing and results_file.exists():
        import json as json_module
        print(f"Loading existing results from {results_file}...")
        seen_toolchains = set()
        seen_linter_versions = set()
        with open(results_file, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    data = json_module.loads(line)
                    if "problem_id" in data:
                        existing_ids.add(data["problem_id"])
                    # Track provenance for mismatch detection
                    if "provenance" in data:
                        prov = data["provenance"]
                        if "lean_toolchain" in prov:
                            seen_toolchains.add(prov["lean_toolchain"])
                        if "linter_version" in prov:
                            seen_linter_versions.add(prov["linter_version"])
                except json_module.JSONDecodeError:
                    pass  # Skip malformed lines in existing results
        print(f"Found {len(existing_ids)} already-processed problems")

        # Warn about provenance mismatches
        if seen_toolchains and toolchain not in seen_toolchains:
            print(f"Warning: Current toolchain '{toolchain}' differs from existing results: {seen_toolchains}", file=sys.stderr)
            print("         Results may be inconsistent. Consider using a fresh output directory.", file=sys.stderr)
        if len(seen_toolchains) > 1:
            print(f"Warning: Existing results contain mixed toolchains: {seen_toolchains}", file=sys.stderr)
        if len(seen_linter_versions) > 1:
            print(f"Warning: Existing results contain mixed linter versions: {seen_linter_versions}", file=sys.stderr)

    logs_dir.mkdir(exist_ok=True)

    # Load problems (single pass)
    print(f"Loading problems from {args.dataset}...")
    problems, load_errors = load_jsonl(args.dataset)

    if load_errors:
        print(f"Warning: {len(load_errors)} lines could not be parsed:", file=sys.stderr)
        for err in load_errors[:5]:
            print(f"  Line {err.line_number}: {err.error}", file=sys.stderr)
        if len(load_errors) > 5:
            print(f"  ... and {len(load_errors) - 5} more", file=sys.stderr)

    # Filter out already-processed problems if resuming
    if existing_ids:
        original_count = len(problems)
        problems = [p for p in problems if p.id not in existing_ids]
        skipped = original_count - len(problems)
        if skipped > 0:
            print(f"Skipping {skipped} already-processed problems")

    total = len(problems)
    print(f"Loaded {total} problems to process")
    print(f"Workspace: {args.workspace}")
    print(f"Toolchain: {toolchain}")
    print(f"Output: {results_file}")
    print()

    # Track stats
    stats = {"ok": 0, "findings": 0, "compile_error": 0, "timeout": 0, "infra_error": 0}
    processed = 0

    # Emit load errors as infra_error results (so totals match dataset size)
    # Skip if resuming - load errors would have been emitted in the original run
    if load_errors and not existing_ids:
        load_provenance = Provenance(
            runner_version=__version__,
            linter_version="n/a",
            lean_toolchain=toolchain,
            timestamp=datetime.now(timezone.utc).isoformat(),
        )
        with open(results_file, "a", encoding="utf-8") as f:
            for err in load_errors:
                # Use line number as problem ID since we couldn't parse the real ID
                result = LintResult(
                    problem_id=f"_load_error_line_{err.line_number}",
                    source=args.dataset.stem,
                    status="infra_error",
                    findings=[],
                    error_message=f"Failed to load from dataset: {err.error}\nRaw: {err.raw_line[:500]}",
                    duration_ms=0,
                    provenance=load_provenance,
                    metadata={},
                )
                f.write(result.to_jsonl() + "\n")
                stats["infra_error"] += 1
    elif load_errors and existing_ids:
        # Resuming - load errors already emitted, just count them for display
        stats["infra_error"] += len(load_errors)

    if total == 0 and not load_errors:
        print("No problems to process.")
        sys.exit(0)

    def on_result(result):
        nonlocal processed
        processed += 1
        stats[result.status] += 1

        # Progress indicator
        status_char = {
            "ok": ".",
            "findings": "F",
            "compile_error": "E",
            "timeout": "T",
            "infra_error": "!",
        }.get(result.status, "?")
        print(status_char, end="", flush=True)
        if processed % 50 == 0:
            print(f" [{processed}/{total}]")

        # Write result
        with open(results_file, "a", encoding="utf-8") as f:
            f.write(result.to_jsonl() + "\n")

        # Save logs for failures (include source to prevent collisions across datasets)
        if result.status in ("compile_error", "timeout", "infra_error"):
            safe_source = re.sub(r'[^a-zA-Z0-9_\-]', '_', result.source or "unknown")
            safe_pid = re.sub(r'[^a-zA-Z0-9_\-]', '_', result.problem_id)
            log_file = logs_dir / f"{safe_source}_{safe_pid}_{result.status}.log"
            with open(log_file, "w", encoding="utf-8") as f:
                f.write(f"Problem: {result.problem_id}\n")
                f.write(f"Source: {result.source}\n")
                f.write(f"Status: {result.status}\n")
                f.write(f"Duration: {result.duration_ms}ms\n")
                f.write(f"\n--- Error ---\n")
                f.write(result.error_message or "(no error message)")

    # Run
    print(f"Running linter with {args.workers} worker(s)...")
    asyncio.run(run_batch(
        workspace=args.workspace,
        problems=problems,
        toolchain=toolchain,
        timeout=args.timeout,
        on_result=on_result,
        workers=args.workers,
    ))

    # Final summary
    print()
    print()
    print("=" * 40)
    print("Summary")
    print("=" * 40)
    total_processed = total + len(load_errors)  # Problems run + load errors emitted
    print(f"Total:         {total_processed}")
    print(f"OK:            {stats['ok']}")
    print(f"Findings:      {stats['findings']}")
    print(f"Compile Error: {stats['compile_error']}")
    print(f"Timeout:       {stats['timeout']}")
    print(f"Infra Error:   {stats['infra_error']}", end="")
    if load_errors:
        print(f" ({len(load_errors)} from bad dataset lines)")
    else:
        print()
    print()
    print(f"Results written to: {results_file}")
    if stats['compile_error'] + stats['timeout'] + stats['infra_error'] > 0:
        print(f"Logs written to: {logs_dir}/")


if __name__ == "__main__":
    main()
