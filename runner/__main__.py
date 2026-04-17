"""CLI entry point for the ATP checkers runner."""
from __future__ import annotations

import argparse
import asyncio
import json
import logging
import os
import re
import signal
import subprocess
import sys
from collections.abc import Iterable, Iterator
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path

from .data_loader import (
    count_jsonl_entries,
    count_lean_files,
    iter_hf,
    iter_json,
    iter_jsonl,
    iter_lean_dir,
)
from .executor import run_batch as run_batch_subprocess
from .models import (
    DEFAULT_TIMEOUT,
    RESULT_SCHEMA_VERSION,
    LintResult,
    ParseError,
    Problem,
    Provenance,
)
from .persistent import run_batch as run_batch_persistent

# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run ATP checkers on a dataset of Lean problems",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python -m runner dataset.jsonl --workspace ./linter -o results/
  python -m runner proofnet.jsonl -w ./linter -o results/
  python -m runner AI-MO/CombiBench --format hf -w ./linter -o results/
  python -m runner ./lean_dir/ --format lean -w ./linter -o results/
        """,
    )
    parser.add_argument("dataset", type=str,
        help="Dataset source: file path (jsonl/json), directory (lean), or HuggingFace repo ID (hf)")
    parser.add_argument("--format", "-f", type=str, choices=["jsonl", "hf", "json", "lean"],
        default="jsonl", help="Dataset format (default: jsonl)")
    parser.add_argument("--workspace", "-w", type=Path, required=True,
        help="Path to pre-built Lean workspace with linter")
    parser.add_argument("--output", "-o", type=Path, required=True,
        help="Output directory for results")
    parser.add_argument("--header-file", type=Path, default=None,
        help="Path to a .lean file whose contents are prepended to every problem")
    parser.add_argument("--split", type=str, default=None,
        help="Split to use for HuggingFace datasets (default: prefers 'test', then first available)")
    parser.add_argument("--toolchain", type=str, default=None,
        help="Lean toolchain string for provenance (default: read from workspace)")
    parser.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT,
        help=f"Timeout per problem in seconds (default: {DEFAULT_TIMEOUT})")
    parser.add_argument("--workers", "-j", type=int, default=1,
        help="Number of parallel workers (default: 1 = sequential)")
    parser.add_argument("--append", action="store_true",
        help="Append to existing results.jsonl instead of failing if it exists")
    parser.add_argument("--skip-existing", action="store_true",
        help="Skip problems already in results.jsonl (for resuming interrupted runs)")
    parser.add_argument("--backend", type=str, choices=["persistent", "subprocess"],
        default="subprocess",
        help="Execution backend (default: subprocess, resolves lake env once then invokes lean directly; "
             "persistent: keeps REPL processes alive, requires `lake build repl`)")
    return parser


# ---------------------------------------------------------------------------
# Config resolution
# ---------------------------------------------------------------------------


@dataclass
class _ResumeState:
    existing_ids: set[str] = field(default_factory=set)
    seen_load_error_ids: set[str] = field(default_factory=set)
    processed: int = 0
    stats: dict[str, int] = field(default_factory=lambda: {
        "ok": 0, "findings": 0, "compile_error": 0, "timeout": 0, "infra_error": 0,
    })
    compile_errors: int = 0
    compile_errors_with_findings: int = 0
    total_findings: int = 0
    by_category: dict[str, dict[str, int]] = field(default_factory=dict)
    by_confidence: dict[str, int] = field(default_factory=lambda: {"proven": 0, "maybe": 0})
    by_proved_by: dict[str, int] = field(default_factory=dict)

    def seed_from_result_json(self, data: dict) -> None:
        self.processed += 1
        status = data.get("status")
        if status in self.stats:
            self.stats[status] += 1
        compile_error = bool(data.get("compile_error", status == "compile_error"))
        if compile_error:
            self.compile_errors += 1
            if data.get("findings"):
                self.compile_errors_with_findings += 1

        problem_id = str(data.get("problem_id", ""))
        if problem_id.startswith("_load_error_line_"):
            self.seen_load_error_ids.add(problem_id)
        elif problem_id:
            self.existing_ids.add(problem_id)

        for finding in data.get("findings", []):
            category = finding.get("category", "unknown")
            confidence = finding.get("confidence", "maybe")
            proved_by = finding.get("provedBy") or "none"

            self.total_findings += 1
            bucket = self.by_category.setdefault(category, {"total": 0, "proven": 0, "maybe": 0})
            bucket["total"] += 1
            bucket[confidence] = bucket.get(confidence, 0) + 1
            self.by_confidence[confidence] = self.by_confidence.get(confidence, 0) + 1
            self.by_proved_by[proved_by] = self.by_proved_by.get(proved_by, 0) + 1


def _resolve_toolchain(args) -> str:
    workspace_toolchain = None
    toolchain_file = args.workspace / "lean-toolchain"
    if toolchain_file.exists():
        workspace_toolchain = toolchain_file.read_text().strip()

    if args.toolchain is not None:
        if workspace_toolchain and workspace_toolchain != args.toolchain:
            print(f"Error: --toolchain '{args.toolchain}' differs from workspace '{workspace_toolchain}'", file=sys.stderr)
            sys.exit(1)
        return args.toolchain
    if workspace_toolchain:
        return workspace_toolchain
    print("Error: Could not determine toolchain.", file=sys.stderr)
    sys.exit(1)


def _resolve_header(args) -> str | None:
    if not args.header_file:
        return None
    if not args.header_file.exists():
        print(f"Error: Header file not found: {args.header_file}", file=sys.stderr)
        sys.exit(1)
    return args.header_file.read_text(encoding="utf-8")


def _load_existing_state(results_file: Path, toolchain: str) -> _ResumeState:
    state = _ResumeState()
    if not results_file.exists():
        return state
    print(f"Loading existing results from {results_file}...")
    latest_by_key: dict[str, dict] = {}
    with open(results_file, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                data = json.loads(line)
            except json.JSONDecodeError:
                continue

            problem_id = data.get("problem_id")
            if problem_id is None:
                continue
            latest_by_key[str(problem_id)] = data

    seen_toolchains = set()
    for data in latest_by_key.values():
        state.seed_from_result_json(data)
        prov = data.get("provenance", {})
        if "lean_toolchain" in prov:
            seen_toolchains.add(prov["lean_toolchain"])

    print(f"Found {len(state.existing_ids)} already-processed problems")
    if seen_toolchains and toolchain not in seen_toolchains:
        print(f"Warning: toolchain mismatch with existing results: {seen_toolchains}", file=sys.stderr)
    if len(seen_toolchains) > 1:
        print(f"Warning: existing results contain mixed toolchains: {seen_toolchains}", file=sys.stderr)
    return state


# ---------------------------------------------------------------------------
# Dataset loading
# ---------------------------------------------------------------------------

def _count_json_entries(path: Path) -> int | None:
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    except json.JSONDecodeError:
        return 1
    return len(data) if isinstance(data, list) else 1


def _open_dataset_stream(args, header: str | None) -> tuple[Iterator[Problem | ParseError], str, int | None]:
    fmt = args.format

    if fmt == "jsonl":
        path = Path(args.dataset)
        if not path.exists():
            print(f"Error: Dataset not found: {path}", file=sys.stderr)
            sys.exit(1)
        print(f"Loading problems from {path}...")
        return iter_jsonl(path, header=header), path.stem, count_jsonl_entries(path)

    if fmt == "json":
        path = Path(args.dataset)
        if not path.exists():
            print(f"Error: Dataset not found: {path}", file=sys.stderr)
            sys.exit(1)
        print(f"Loading problems from {path} (JSON array)...")
        return iter_json(path, header=header), path.stem, _count_json_entries(path)

    if fmt == "lean":
        path = Path(args.dataset)
        if not path.is_dir():
            print(f"Error: Not a directory: {path}", file=sys.stderr)
            sys.exit(1)
        print(f"Loading .lean files from {path}/...")
        return iter_lean_dir(path, header=header), path.name, max(count_lean_files(path), 1)

    # hf
    print(f"Loading from HuggingFace: {args.dataset}...")
    return iter_hf(repo_id=args.dataset, split=args.split, header=header), args.dataset.replace("/", "_"), None


# ---------------------------------------------------------------------------
# Result tracking (online counters)
# ---------------------------------------------------------------------------

class _ResultTracker:
    def __init__(
        self,
        total_hint: int | None,
        results_fh,
        logs_dir: Path,
        *,
        dataset_name: str = "",
        run_id: str = "",
        resume_state: _ResumeState | None = None,
    ):
        resume_state = resume_state or _ResumeState()
        self.total_hint = total_hint
        self.results_fh = results_fh
        self.logs_dir = logs_dir
        self.dataset_name = dataset_name
        self.run_id = run_id
        self.processed = resume_state.processed
        self.stats = dict(resume_state.stats)
        self.compile_errors = resume_state.compile_errors
        self.compile_errors_with_findings = resume_state.compile_errors_with_findings
        self.total_findings = resume_state.total_findings
        self.by_category = {k: dict(v) for k, v in resume_state.by_category.items()}
        self.by_confidence = dict(resume_state.by_confidence)
        self.by_proved_by = dict(resume_state.by_proved_by)

    def on_result(self, result: LintResult) -> None:
        result.dataset = self.dataset_name
        result.run_id = self.run_id
        self.processed += 1

        # The Lean side emits per-declaration infrastructure failures (grind
        # crashes, maxRecDepth, etc.) as findings with category "Linter
        # Internal Error". These are not semantic findings — treat them as
        # infra errors so they don't inflate the real finding counts.
        internal_error_findings = [f for f in result.findings
                                   if f.category == "Linter Internal Error"]
        semantic_findings = [f for f in result.findings
                             if f.category != "Linter Internal Error"]
        if internal_error_findings and result.status == "findings" and not semantic_findings:
            # Promote to infra_error when the ONLY findings are internal errors
            result.status = "infra_error"
        self.stats[result.status] = self.stats.get(result.status, 0) + 1
        if result.compile_error:
            self.compile_errors += 1
            if semantic_findings:
                self.compile_errors_with_findings += 1

        for f in semantic_findings:
            self.total_findings += 1
            if f.category not in self.by_category:
                self.by_category[f.category] = {"total": 0, "proven": 0, "maybe": 0}
            self.by_category[f.category]["total"] += 1
            self.by_category[f.category][f.confidence] = self.by_category[f.category].get(f.confidence, 0) + 1
            self.by_confidence[f.confidence] = self.by_confidence.get(f.confidence, 0) + 1
            key = f.proved_by or "none"
            self.by_proved_by[key] = self.by_proved_by.get(key, 0) + 1

        # Progress
        char = {"ok": ".", "findings": "F", "compile_error": "E",
                "timeout": "T", "infra_error": "!"}.get(result.status, "?")
        print(char, end="", flush=True)
        if self.processed % 50 == 0:
            if self.total_hint is not None:
                print(f" [{self.processed}/{self.total_hint}]")
            else:
                print(f" [{self.processed}]")

        # Write result
        self.results_fh.write(result.to_jsonl() + "\n")
        self.results_fh.flush()

        # Log failures
        if result.status in ("compile_error", "timeout", "infra_error") or result.compile_error:
            safe_source = re.sub(r'[^a-zA-Z0-9_\-]', '_', result.source or "unknown")
            safe_pid = re.sub(r'[^a-zA-Z0-9_\-]', '_', result.problem_id)
            suffix = result.status
            if result.compile_error and result.status in ("ok", "findings"):
                suffix = "compile_error"
            log_file = self.logs_dir / f"{safe_source}_{safe_pid}_{suffix}.log"
            with open(log_file, "w", encoding="utf-8") as f:
                f.write(
                    f"Problem: {result.problem_id}\n"
                    f"Source: {result.source}\n"
                    f"Status: {result.status}\n"
                    f"Compile Error: {result.compile_error}\n"
                    f"Duration: {result.duration_ms}ms\n"
                )
                if result.compile_error_message is not None:
                    f.write(f"\n--- Compile Error ---\n{result.compile_error_message}")
                if result.error_message is not None:
                    f.write(f"\n\n--- Error ---\n{result.error_message}")

    def summary_dict(self, dataset_source: str, toolchain: str) -> dict:
        return {
            "schema_version": RESULT_SCHEMA_VERSION,
            "run_id": self.run_id,
            "dataset": dataset_source,
            "toolchain": toolchain,
            "total_problems": self.total_hint if self.total_hint is not None else self.processed,
            "status_counts": dict(self.stats),
            "compile_error_counts": {
                "total": self.compile_errors,
                "with_findings": self.compile_errors_with_findings,
                "without_findings": self.compile_errors - self.compile_errors_with_findings,
                "compile_only": self.stats["compile_error"],
            },
            "total_findings": self.total_findings,
            "confidence_counts": self.by_confidence,
            "findings_by_category": dict(sorted(self.by_category.items(), key=lambda x: x[1]["total"], reverse=True)),
            "proved_by_counts": dict(sorted(self.by_proved_by.items(), key=lambda x: x[1], reverse=True)),
        }


def _print_summary(tracker: _ResultTracker) -> None:
    total_processed = tracker.total_hint if tracker.total_hint is not None else tracker.processed
    print()
    print()
    print("=" * 50)
    print("Summary")
    print("=" * 50)
    print(f"Total problems:  {total_processed}")
    print(f"  OK:            {tracker.stats['ok']}")
    print(f"  Findings:      {tracker.stats['findings']}")
    print(f"  Compile Only:  {tracker.stats['compile_error']}")
    print(f"  Timeout:       {tracker.stats['timeout']}")
    print(f"  Infra Error:   {tracker.stats['infra_error']}")
    print(f"  Compile Flag:  {tracker.compile_errors}")
    if tracker.compile_errors:
        print(f"    With Findings:    {tracker.compile_errors_with_findings}")
        print(f"    Without Findings: {tracker.compile_errors - tracker.compile_errors_with_findings}")

    if tracker.total_findings:
        print()
        print(f"Total findings:  {tracker.total_findings}")
        print(f"  Proven:        {tracker.by_confidence.get('proven', 0)}")
        print(f"  Maybe:         {tracker.by_confidence.get('maybe', 0)}")
        print()
        print("Findings by category:")
        for cat, counts in sorted(tracker.by_category.items(), key=lambda x: x[1]["total"], reverse=True):
            print(f"  {cat:<40} {counts['total']:>4}  (proven: {counts['proven']}, maybe: {counts['maybe']})")
        print()
        print("Proved by:")
        for method, count in sorted(tracker.by_proved_by.items(), key=lambda x: x[1], reverse=True):
            print(f"  {method:<20} {count:>4}")


def _make_load_error_result(err: ParseError, dataset_source: str, toolchain: str) -> LintResult:
    return LintResult(
        problem_id=f"_load_error_line_{err.line_number}",
        source=dataset_source,
        status="infra_error",
        findings=[],
        error_message=f"Failed to load: {err.error}\nRaw: {err.raw_line[:500]}",
        duration_ms=0,
        provenance=Provenance(
            lean_toolchain=toolchain,
            timestamp=datetime.now(timezone.utc).isoformat(),
        ),
        metadata={},
    )


def _iter_runnable_problems(
    items: Iterable[Problem | ParseError],
    tracker: _ResultTracker,
    dataset_source: str,
    toolchain: str,
    resume_state: _ResumeState,
) -> Iterator[Problem]:
    for item in items:
        if isinstance(item, ParseError):
            result = _make_load_error_result(item, dataset_source, toolchain)
            if result.problem_id not in resume_state.seen_load_error_ids:
                tracker.on_result(result)
            continue

        if item.id in resume_state.existing_ids:
            continue

        yield item


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def _kill_surviving_lean_children() -> None:
    """Best-effort kill of any surviving lean/lake subprocesses we spawned.

    Subprocesses are created with start_new_session=True, which puts them
    in their own session/process group so they don't receive SIGINT via
    the tty. They remain our direct children by ppid, so a ps-based scan
    finds them reliably.
    """
    try:
        out = subprocess.run(
            ["ps", "-axo", "pid=,ppid=,comm="],
            capture_output=True,
            text=True,
            timeout=5,
            check=False,
        ).stdout
    except (OSError, subprocess.SubprocessError):
        return

    our_pid = os.getpid()
    victims: list[int] = []
    for line in out.splitlines():
        parts = line.strip().split(None, 2)
        if len(parts) < 3:
            continue
        try:
            pid, ppid = int(parts[0]), int(parts[1])
        except ValueError:
            continue
        comm = parts[2]
        if ppid == our_pid and ("lean" in comm or "lake" in comm):
            victims.append(pid)

    for pid in victims:
        try:
            os.kill(pid, signal.SIGKILL)
        except OSError:
            pass
    if victims:
        print(f"[interrupted] killed {len(victims)} surviving Lean subprocess(es)",
              file=sys.stderr)


def main():
    args = _build_parser().parse_args()
    logging.basicConfig(level=logging.INFO, format="%(levelname)s: %(message)s")

    if not args.workspace.exists():
        print(f"Error: Workspace not found: {args.workspace}", file=sys.stderr)
        sys.exit(1)

    toolchain = _resolve_toolchain(args)
    header = _resolve_header(args)

    # Output setup
    args.output.mkdir(parents=True, exist_ok=True)
    results_file = args.output / "results.jsonl"
    logs_dir = args.output / "logs"
    logs_dir.mkdir(exist_ok=True)

    if results_file.exists() and not args.append and not args.skip_existing:
        print(f"Error: {results_file} already exists. Use --append or --skip-existing.", file=sys.stderr)
        sys.exit(1)

    resuming = args.skip_existing and results_file.exists()
    resume_state = _load_existing_state(results_file, toolchain) if resuming else _ResumeState()

    items, dataset_source, total_hint = _open_dataset_stream(args, header)
    run_started_at = datetime.now(timezone.utc).isoformat()
    run_id = f"{args.output.name}:{run_started_at}"
    if total_hint == 0:
        print("No problems to process.")
        sys.exit(0)

    if resume_state.existing_ids:
        print(f"Resuming with {len(resume_state.existing_ids)} previously processed problems")
    if total_hint is not None:
        print(f"Loaded dataset with {total_hint} entries")
    else:
        print("Loaded dataset stream")
    print(f"Workspace: {args.workspace}")
    print(f"Toolchain: {toolchain}")
    print(f"Output: {results_file}")
    print()

    run_manifest = {
        "schema_version": RESULT_SCHEMA_VERSION,
        "run_id": run_id,
        "started_at": run_started_at,
        "dataset": {
            "input": args.dataset,
            "resolved_name": dataset_source,
            "format": args.format,
            "split": args.split,
            "header_file": str(args.header_file) if args.header_file else None,
            "total_hint": total_hint,
        },
        "execution": {
            "workspace": str(args.workspace),
            "toolchain": toolchain,
            "backend": args.backend,
            "workers": args.workers,
            "timeout": args.timeout,
            "output_dir": str(args.output),
            "resuming": resuming,
        },
    }
    run_file = args.output / "run.json"
    with open(run_file, "w", encoding="utf-8") as f:
        json.dump(run_manifest, f, indent=2, ensure_ascii=False)

    # Run
    mode = f"persistent REPL ({args.workers} worker(s))" if args.backend == "persistent" \
        else f"subprocess ({args.workers} worker(s))"
    print(f"Running linter [{mode}]...")

    with open(results_file, "a", encoding="utf-8") as results_fh:
        tracker = _ResultTracker(
            total_hint,
            results_fh,
            logs_dir,
            dataset_name=dataset_source,
            run_id=run_id,
            resume_state=resume_state,
        )
        problems = _iter_runnable_problems(items, tracker, dataset_source, toolchain, resume_state)

        try:
            if args.backend == "persistent":
                asyncio.run(run_batch_persistent(
                    workspace=args.workspace, problems=problems, toolchain=toolchain,
                    timeout=args.timeout, on_result=tracker.on_result, workers=args.workers,
                    collect_results=False,
                ))
            else:
                asyncio.run(run_batch_subprocess(
                    workspace=args.workspace, problems=problems, toolchain=toolchain,
                    timeout=args.timeout, on_result=tracker.on_result, workers=args.workers,
                    collect_results=False,
                ))
        except KeyboardInterrupt:
            # On Ctrl-C, asyncio.run cancels tasks which cancels run_batch's
            # in-flight windows (see the BaseException handlers in
            # executor/persistent run_batch). That reaches the individual
            # lint_problem calls, which kill their subprocesses in finally
            # blocks. Still: some children spawned with start_new_session
            # may outlive their parent; best-effort kill-on-exit.
            print("\n[interrupted] cancelling; killing any surviving Lean children...",
                  file=sys.stderr)
            _kill_surviving_lean_children()
            raise

    # Summary
    summary = tracker.summary_dict(dataset_source, toolchain)
    summary_file = args.output / "summary.json"
    with open(summary_file, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2, ensure_ascii=False)

    _print_summary(tracker)
    print()
    print(f"Results:  {results_file}")
    print(f"Run:      {run_file}")
    print(f"Summary:  {summary_file}")
    if tracker.compile_errors + tracker.stats["timeout"] + tracker.stats["infra_error"] > 0:
        print(f"Logs:     {logs_dir}/")


if __name__ == "__main__":
    main()
