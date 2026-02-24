"""Lean execution logic for the ATP checkers runner."""
from __future__ import annotations

import asyncio
import hashlib
import json
import os
import re
import signal
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional, Tuple

from .models import Problem, Finding, LintResult, Provenance


# Sentinel prefixes used by the Lean linter
SENTINEL_LINT = "ATP_LINT:"
SENTINEL_DONE = "ATP_DONE"

DEFAULT_TIMEOUT = 30  # seconds


def _sanitize_id_for_lean(problem_id: str) -> str:
    """Convert problem ID to a valid Lean module name component.

    Lean module names can only contain alphanumerics and underscores,
    and cannot start with a digit.

    Appends a short hash of the original ID to prevent collisions
    (e.g., 'a-b' and 'a_b' both sanitize to 'a_b' but get different hashes).
    """
    # Replace any non-alphanumeric with underscore
    safe = re.sub(r'[^a-zA-Z0-9]', '_', problem_id)
    # Ensure it doesn't start with a digit
    if safe and safe[0].isdigit():
        safe = '_' + safe
    safe = safe or '_empty_'
    # Append short hash of original ID to prevent collisions
    id_hash = hashlib.sha256(problem_id.encode()).hexdigest()[:8]
    return f"{safe}_{id_hash}"


def wrap_with_linter(lean_code: str) -> str:
    """Wrap problem code with linter import and check command."""
    return f"""import AtpLinter

{lean_code}

#check_atp_all
"""


def parse_lint_output(stdout: str) -> Tuple[list[Finding], list[str]]:
    """
    Parse linter output from stdout.

    Returns:
        (findings, parse_errors)
    """
    findings = []
    parse_errors = []

    for line in stdout.splitlines():
        if line.startswith(SENTINEL_LINT):
            json_str = line[len(SENTINEL_LINT):]
            try:
                data = json.loads(json_str)
                findings.append(Finding.from_dict(data))
            except json.JSONDecodeError as e:
                parse_errors.append(f"Malformed ATP_LINT JSON: {e} in: {json_str[:100]}")

    return findings, parse_errors


def has_done_sentinel(stdout: str) -> Tuple[bool, Optional[dict]]:
    """
    Check if ATP_DONE sentinel is present and parse its metadata.

    Returns:
        (found, metadata_dict)
    """
    for line in stdout.splitlines():
        if line.startswith(SENTINEL_DONE):
            # Try to parse the JSON metadata after ATP_DONE:
            rest = line[len(SENTINEL_DONE):]
            if rest.startswith(":"):
                try:
                    return True, json.loads(rest[1:])
                except json.JSONDecodeError:
                    return True, None
            return True, None
    return False, None


async def lint_problem(
    workspace: Path,
    problem: Problem,
    toolchain: str,
    timeout: int = DEFAULT_TIMEOUT,
    row_index: int = 0,
) -> LintResult:
    """
    Lint a single problem.

    Args:
        workspace: Path to pre-built Lean workspace
        problem: The problem to lint
        toolchain: Lean toolchain string (for provenance)
        timeout: Timeout per problem in seconds
        row_index: Unique row index to prevent temp file collisions

    Returns:
        LintResult with status and findings
    """
    start_time = time.monotonic()

    # Write problem to temp file (sanitize ID for valid Lean module name)
    safe_id = _sanitize_id_for_lean(problem.id)
    file_stem = f"_Problem_{row_index}_{safe_id}"
    problem_file = workspace / f"{file_stem}.lean"
    try:
        problem_file.write_text(wrap_with_linter(problem.lean_code), encoding="utf-8")
    except (OSError, IOError) as e:
        duration_ms = int((time.monotonic() - start_time) * 1000)
        return LintResult(
            problem_id=problem.id,
            source=problem.source,
            status="infra_error",
            findings=[],
            error_message=f"Failed to write problem file: {e}",
            duration_ms=duration_ms,
            provenance=_make_provenance(toolchain),
            metadata=problem.metadata,
        )

    try:
        # Run Lean with timeout, in its own process group
        try:
            proc = await asyncio.create_subprocess_exec(
                "lake", "env", "lean", problem_file.name,
                cwd=workspace,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
                start_new_session=True,
            )
        except (OSError, FileNotFoundError) as e:
            duration_ms = int((time.monotonic() - start_time) * 1000)
            return LintResult(
                problem_id=problem.id,
                source=problem.source,
                status="infra_error",
                findings=[],
                error_message=f"Failed to spawn lake process: {e}",
                duration_ms=duration_ms,
                provenance=_make_provenance(toolchain),
                metadata=problem.metadata,
            )

        try:
            stdout_bytes, stderr_bytes = await asyncio.wait_for(
                proc.communicate(),
                timeout=timeout,
            )
        except asyncio.TimeoutError:
            # Kill entire process group and wait for cleanup
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
                await asyncio.sleep(0.5)
                os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                pass
            # Wait for process to actually terminate to avoid zombies
            try:
                await asyncio.wait_for(proc.wait(), timeout=2.0)
            except asyncio.TimeoutError:
                pass

            duration_ms = int((time.monotonic() - start_time) * 1000)
            return LintResult(
                problem_id=problem.id,
                source=problem.source,
                status="timeout",
                findings=[],
                error_message=f"Exceeded {timeout}s timeout",
                duration_ms=duration_ms,
                provenance=_make_provenance(toolchain),
                metadata=problem.metadata,
            )

        stdout_str = stdout_bytes.decode("utf-8", errors="replace")
        stderr_str = stderr_bytes.decode("utf-8", errors="replace")

        duration_ms = int((time.monotonic() - start_time) * 1000)

        # Parse linter output
        findings, parse_errors = parse_lint_output(stdout_str)
        done, done_meta = has_done_sentinel(stdout_str)

        # Check for truncated output by comparing expected vs actual findings count
        truncation_error = None
        if done and done_meta and "findings" in done_meta:
            expected_findings = done_meta["findings"]
            actual_findings = len(findings)
            if expected_findings != actual_findings:
                truncation_error = f"Output may be truncated: ATP_DONE reports {expected_findings} findings but only {actual_findings} were parsed"

        # If we had parse errors or truncation, treat as infra_error
        if parse_errors or truncation_error:
            # Combine stdout and stderr for diagnostics
            errors_section = ""
            if truncation_error:
                errors_section += f"=== TRUNCATION ===\n{truncation_error}\n\n"
            if parse_errors:
                errors_section += "=== PARSE ERRORS ===\n" + "\n".join(parse_errors)
            combined_output = f"=== STDOUT ===\n{stdout_str[:3000]}\n\n=== STDERR ===\n{stderr_str[:1000]}\n\n{errors_section}"
            return LintResult(
                problem_id=problem.id,
                source=problem.source,
                status="infra_error",
                findings=findings,  # Include any findings we did parse
                error_message=combined_output[:4000],
                duration_ms=duration_ms,
                provenance=_make_provenance(toolchain),
                metadata=problem.metadata,
            )

        # Determine status
        if proc.returncode < 0:
            # Negative return code means killed by signal (OOM, SIGKILL, etc.) - infrastructure issue
            signal_num = -proc.returncode
            combined_output = f"Process killed by signal {signal_num}\n\n=== STDOUT ===\n{stdout_str[:2000]}\n\n=== STDERR ===\n{stderr_str[:2000]}"
            return LintResult(
                problem_id=problem.id,
                source=problem.source,
                status="infra_error",
                findings=[],
                error_message=combined_output[:4000],
                duration_ms=duration_ms,
                provenance=_make_provenance(toolchain),
                metadata=problem.metadata,
            )
        elif proc.returncode > 0:
            # Positive return code means Lean compilation error - dataset issue
            combined_output = f"=== STDOUT ===\n{stdout_str[:2000]}\n\n=== STDERR ===\n{stderr_str[:2000]}"
            return LintResult(
                problem_id=problem.id,
                source=problem.source,
                status="compile_error",
                findings=[],
                error_message=combined_output[:4000],
                duration_ms=duration_ms,
                provenance=_make_provenance(toolchain),
                metadata=problem.metadata,
            )
        elif not done:
            combined_output = f"Linter did not complete (no ATP_DONE sentinel)\n\n=== STDOUT ===\n{stdout_str[:2000]}\n\n=== STDERR ===\n{stderr_str[:1000]}"
            return LintResult(
                problem_id=problem.id,
                source=problem.source,
                status="infra_error",
                findings=[],
                error_message=combined_output[:4000],
                duration_ms=duration_ms,
                provenance=_make_provenance(toolchain),
                metadata=problem.metadata,
            )
        else:
            return LintResult(
                problem_id=problem.id,
                source=problem.source,
                status="findings" if findings else "ok",
                findings=findings,
                error_message=None,
                duration_ms=duration_ms,
                provenance=_make_provenance(toolchain),
                metadata=problem.metadata,
            )

    finally:
        # Cleanup temp file and build artifacts
        _cleanup_problem_artifacts(workspace, file_stem)


def _cleanup_problem_artifacts(workspace: Path, file_stem: str):
    """Remove temp .lean file and any generated build artifacts."""
    # Remove the .lean file
    problem_file = workspace / f"{file_stem}.lean"
    try:
        problem_file.unlink(missing_ok=True)
    except Exception:
        pass

    # Remove build artifacts (.olean, .ilean, .trace)
    # Lake puts these in .lake/build/lib/ with the same base name
    build_lib = workspace / ".lake" / "build" / "lib"
    if build_lib.exists():
        for ext in [".olean", ".ilean", ".trace", ".c", ".o"]:
            artifact = build_lib / f"{file_stem}{ext}"
            try:
                artifact.unlink(missing_ok=True)
            except Exception:
                pass

    # Also clean up IR artifacts in .lake/build/ir/
    build_ir = workspace / ".lake" / "build" / "ir"
    if build_ir.exists():
        for ext in [".c", ".c.trace"]:
            artifact = build_ir / f"{file_stem}{ext}"
            try:
                artifact.unlink(missing_ok=True)
            except Exception:
                pass


def _make_provenance(toolchain: str) -> Provenance:
    """Create provenance record."""
    return Provenance(
        lean_toolchain=toolchain,
        timestamp=datetime.now(timezone.utc).isoformat(),
    )


async def run_batch(
    workspace: Path,
    problems: list[Problem],
    toolchain: str,
    timeout: int = DEFAULT_TIMEOUT,
    on_result: Optional[callable] = None,
    workers: int = 1,
) -> list[LintResult]:
    """
    Run linter on a batch of problems with optional parallelism.

    Args:
        workspace: Path to pre-built Lean workspace
        problems: Problems to lint
        toolchain: Lean toolchain string
        timeout: Timeout per problem in seconds
        on_result: Optional callback called with each result
        workers: Number of parallel workers (default 1 = sequential)

    Returns:
        List of LintResults
    """
    if workers <= 1:
        # Sequential execution
        results = []
        for idx, problem in enumerate(problems):
            result = await lint_problem(workspace, problem, toolchain, timeout, row_index=idx)
            results.append(result)
            if on_result:
                on_result(result)
        return results
    else:
        # Parallel execution with semaphore
        semaphore = asyncio.Semaphore(workers)
        results = []
        results_lock = asyncio.Lock()

        async def process_one(idx: int, problem: Problem):
            async with semaphore:
                result = await lint_problem(workspace, problem, toolchain, timeout, row_index=idx)
                async with results_lock:
                    results.append(result)
                    if on_result:
                        on_result(result)
                return result

        await asyncio.gather(*[process_one(i, p) for i, p in enumerate(problems)])
        return results
