"""Subprocess backend for the ATP checkers runner (fallback/debug).

Spawns a fresh Lean process per problem. It resolves the workspace environment
once via `lake env` and then invokes the Lean binary directly, falling back to
`lake env lean` if env resolution fails. Still slow for Mathlib-heavy datasets
due to repeated import cost, but much cheaper than wrapping every problem in a
fresh `lake env` shell.
"""
from __future__ import annotations

import asyncio
import hashlib
import json
import logging
import os
import re
import shutil
import signal
import subprocess
import threading
import time
from collections.abc import Callable, Iterable
from pathlib import Path

from .models import (
    DEFAULT_TIMEOUT,
    LintResult,
    Problem,
    has_done_sentinel,
    make_provenance,
    parse_lint_output,
)
from .preamble import normalize_imports, partition_preamble, render_problem_source, split_preamble

log = logging.getLogger(__name__)

_FAILURE_RETRY_SECONDS = 30.0

_LEAN_ENV_LOCK = threading.Lock()
_LEAN_ENV_CACHE: dict[Path, tuple[tuple[str, ...], dict[str, str]]] = {}
_LEAN_ENV_FAILURES: dict[Path, float] = {}
_IMPORT_CACHE_LOCK = threading.Lock()
_IMPORT_MODULE_CACHE: dict[tuple[Path, tuple[str, ...], tuple[str, ...]], str] = {}
_IMPORT_MODULE_FAILURES: dict[tuple[Path, tuple[str, ...], tuple[str, ...]], float] = {}
_IMPORT_MODULE_LOCKS: dict[tuple[Path, tuple[str, ...], tuple[str, ...]], threading.Lock] = {}


def _cache_root(workspace: Path) -> Path:
    return workspace.resolve() / ".atp_import_cache"


def _normalize_extra_lean_paths(extra_paths: object) -> tuple[str, ...]:
    if not isinstance(extra_paths, (list, tuple)):
        return ()
    normalized: list[str] = []
    for item in extra_paths:
        if not isinstance(item, str):
            continue
        path = item.strip()
        if path:
            normalized.append(path)
    return tuple(normalized)


def _env_extra_lean_paths() -> tuple[str, ...]:
    raw = os.environ.get("ATP_EXTRA_LEAN_PATHS", "")
    if not raw:
        return ()
    return tuple(path for path in raw.split(os.pathsep) if path)


def _augment_lean_env(
    workspace: Path,
    env: dict[str, str],
    extra_paths: tuple[str, ...] = (),
) -> dict[str, str]:
    augmented = dict(env)
    cache_root = str(_cache_root(workspace))
    lean_path = augmented.get("LEAN_PATH", "")
    existing_paths = [p for p in lean_path.split(os.pathsep) if p]
    merged: list[str] = []
    for path in (cache_root, *extra_paths, *existing_paths):
        if path not in merged:
            merged.append(path)
    augmented["LEAN_PATH"] = os.pathsep.join(merged)
    return augmented


def _bundle_module_name(imports: tuple[str, ...]) -> str:
    digest = hashlib.sha256("\n".join(imports).encode("utf-8")).hexdigest()[:16]
    return f"AtpCache.Imports_{digest}"


def _ensure_import_bundle(
    workspace: Path,
    imports: tuple[str, ...],
    lean_cmd: tuple[str, ...] | None,
    lean_env: dict[str, str] | None,
    extra_paths: tuple[str, ...] = (),
) -> str | None:
    if lean_cmd is None or lean_env is None or len(lean_cmd) != 1:
        log.debug("Skipping import-bundle cache: unsupported Lean command %r", lean_cmd)
        return None

    lean_path = lean_cmd[0]
    resolved_lean = lean_path if os.path.isabs(lean_path) else shutil.which(lean_path)
    if not resolved_lean:
        log.debug("Skipping import-bundle cache: could not resolve Lean binary %r", lean_path)
        return None

    workspace = workspace.resolve()
    normalized_imports = normalize_imports(imports)
    key = (workspace, normalized_imports, extra_paths)
    now = time.monotonic()
    with _IMPORT_CACHE_LOCK:
        cached = _IMPORT_MODULE_CACHE.get(key)
        if cached is not None:
            return cached
        failed_until = _IMPORT_MODULE_FAILURES.get(key)
        if failed_until is not None:
            if failed_until > now:
                return None
            _IMPORT_MODULE_FAILURES.pop(key, None)
        lock = _IMPORT_MODULE_LOCKS.setdefault(key, threading.Lock())

    with lock:
        with _IMPORT_CACHE_LOCK:
            cached = _IMPORT_MODULE_CACHE.get(key)
            if cached is not None:
                return cached
            failed_until = _IMPORT_MODULE_FAILURES.get(key)
            if failed_until is not None:
                if failed_until > time.monotonic():
                    return None
                _IMPORT_MODULE_FAILURES.pop(key, None)

        module_name = _bundle_module_name(normalized_imports)
        cache_root = _cache_root(workspace)
        source_path = cache_root / Path(*module_name.split(".")).with_suffix(".lean")
        olean_path = source_path.with_suffix(".olean")
        source_path.parent.mkdir(parents=True, exist_ok=True)
        source_text = "\n".join(["import AtpLinter", *normalized_imports]) + "\n"

        source_changed = True
        if source_path.exists():
            existing = source_path.read_text(encoding="utf-8")
            source_changed = existing != source_text
        if source_changed:
            source_path.write_text(source_text, encoding="utf-8")
            olean_path.unlink(missing_ok=True)

        if not olean_path.exists():
            proc = subprocess.run(
                [resolved_lean, "-o", str(olean_path), str(source_path)],
                cwd=workspace,
                env=lean_env,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True, check=False,
            )
            if proc.returncode != 0:
                log.warning(
                    "Import-bundle cache compile failed for %s: %s",
                    module_name,
                    (proc.stderr or proc.stdout or "unknown error")[:400],
                )
                with _IMPORT_CACHE_LOCK:
                    _IMPORT_MODULE_FAILURES[key] = time.monotonic() + _FAILURE_RETRY_SECONDS
                return None

        with _IMPORT_CACHE_LOCK:
            _IMPORT_MODULE_CACHE[key] = module_name
        return module_name


def _resolve_direct_lean(workspace: Path) -> tuple[tuple[str, ...], dict[str, str]] | None:
    """Resolve a workspace-specific Lean command and environment once.

    Uses `lake env python` to capture the effective Lean environment, then caches
    the direct Lean binary path from the `LEAN` variable.
    """
    workspace = workspace.resolve()
    with _LEAN_ENV_LOCK:
        cached = _LEAN_ENV_CACHE.get(workspace)
        if cached is not None:
            return cached
        failed_until = _LEAN_ENV_FAILURES.get(workspace)
        if failed_until is not None:
            if failed_until > time.monotonic():
                return None
            _LEAN_ENV_FAILURES.pop(workspace, None)

    try:
        raw_env = subprocess.check_output(
            [
                "lake",
                "env",
                "python",
                "-c",
                "import json, os; print(json.dumps(dict(os.environ)))",
            ],
            cwd=workspace,
            text=True,
        )
        env = json.loads(raw_env)
        lean = env.get("LEAN")
        if not isinstance(lean, str) or not lean:
            raise RuntimeError("lake env did not expose LEAN")
        env = _augment_lean_env(workspace, env)
        resolved = ((lean,), env)
    except (OSError, subprocess.SubprocessError, json.JSONDecodeError, RuntimeError) as exc:
        log.warning("Direct Lean resolution failed for %s: %s", workspace, exc)
        with _LEAN_ENV_LOCK:
            _LEAN_ENV_FAILURES[workspace] = time.monotonic() + _FAILURE_RETRY_SECONDS
        return None

    with _LEAN_ENV_LOCK:
        _LEAN_ENV_CACHE[workspace] = resolved
    return resolved


async def _resolve_direct_lean_async(workspace: Path) -> tuple[tuple[str, ...], dict[str, str]] | None:
    return await asyncio.to_thread(_resolve_direct_lean, workspace)


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


def _problem_extra_lean_paths(problem: Problem) -> tuple[str, ...]:
    merged: list[str] = []
    for path in (*_env_extra_lean_paths(), *_normalize_extra_lean_paths(problem.metadata.get("extra_lean_paths"))):
        if path not in merged:
            merged.append(path)
    return tuple(merged)


def wrap_with_linter(lean_code: str) -> str:
    """Wrap problem code with linter import and check command.

    If the code ends with 'by' (common in benchmark datasets that omit the proof),
    append 'sorry' so that '#check_atp_all' isn't parsed as a tactic.
    """
    return render_problem_source(lean_code)



async def lint_problem(
    workspace: Path,
    problem: Problem,
    toolchain: str,
    timeout: int = DEFAULT_TIMEOUT,
    row_index: int = 0,
    lean_cmd: tuple[str, ...] | None = None,
    lean_env: dict[str, str] | None = None,
) -> LintResult:
    """
    Lint a single problem.

    Args:
        workspace: Path to pre-built Lean workspace
        problem: The problem to lint
        toolchain: Lean toolchain string (for provenance)
        timeout: Timeout per problem in seconds
        row_index: Unique row index to prevent temp file collisions
        lean_cmd: Optional resolved Lean command (workspace-specific)
        lean_env: Optional environment for direct Lean execution

    Returns:
        LintResult with status and findings
    """
    start_time = time.monotonic()

    # Write problem to temp file (sanitize ID for valid Lean module name)
    safe_id = _sanitize_id_for_lean(problem.id)
    file_stem = f"_Problem_{row_index}_{safe_id}"
    problem_file = workspace / f"{file_stem}.lean"
    preamble, _body = split_preamble(problem.lean_code)
    imports, _directives = partition_preamble(preamble)
    import_module = None
    extra_paths = _problem_extra_lean_paths(problem)
    problem_lean_env = None
    if lean_cmd is not None and lean_env is not None:
        problem_lean_env = _augment_lean_env(workspace, lean_env, extra_paths)
        import_module = await asyncio.to_thread(
            _ensure_import_bundle,
            workspace,
            imports,
            lean_cmd,
            problem_lean_env,
            extra_paths,
        )
    try:
        problem_file.write_text(render_problem_source(problem.lean_code, import_module=import_module), encoding="utf-8")
    except OSError as e:
        duration_ms = int((time.monotonic() - start_time) * 1000)
        return LintResult(
            problem_id=problem.id,
            source=problem.source,
            status="infra_error",
            findings=[],
            error_message=f"Failed to write problem file: {e}",
            duration_ms=duration_ms,
            provenance=make_provenance(toolchain),
            metadata=problem.metadata,
        )

    try:
        # Run Lean with timeout, in its own process group
        if lean_cmd is None:
            resolved = await _resolve_direct_lean_async(workspace)
            if resolved is not None:
                lean_cmd, lean_env = resolved
        if lean_env is not None:
            problem_lean_env = _augment_lean_env(workspace, lean_env, extra_paths)
        if lean_cmd is None:
            lean_cmd = ("lake", "env", "lean")
            if extra_paths:
                problem_lean_env = _augment_lean_env(workspace, dict(os.environ), extra_paths)
                log.debug("Extra Lean paths injected into lake env lean fallback: %s", extra_paths)

        try:
            proc = await asyncio.create_subprocess_exec(
                *lean_cmd, problem_file.name,
                cwd=workspace,
                env=problem_lean_env,
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
                error_message=f"Failed to spawn Lean process: {e}",
                duration_ms=duration_ms,
                provenance=make_provenance(toolchain),
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
                provenance=make_provenance(toolchain),
                metadata=problem.metadata,
            )

        stdout_str = stdout_bytes.decode("utf-8", errors="replace")
        stderr_str = stderr_bytes.decode("utf-8", errors="replace")
        if proc.returncode is None:
            duration_ms = int((time.monotonic() - start_time) * 1000)
            return LintResult(
                problem_id=problem.id,
                source=problem.source,
                status="infra_error",
                findings=[],
                error_message="Lean process completed without a return code",
                duration_ms=duration_ms,
                provenance=make_provenance(toolchain),
                metadata=problem.metadata,
            )
        returncode = proc.returncode

        duration_ms = int((time.monotonic() - start_time) * 1000)

        # Parse linter output
        findings, parse_errors = parse_lint_output(stdout_str)
        done, done_meta = has_done_sentinel(stdout_str)
        compile_error = returncode > 0
        compile_error_message = None
        if compile_error:
            compile_error_message = (
                f"=== STDOUT ===\n{stdout_str[:2000]}\n\n=== STDERR ===\n{stderr_str[:2000]}"
            )[:4000]

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
                provenance=make_provenance(toolchain),
                compile_error=compile_error,
                compile_error_message=compile_error_message,
                metadata=problem.metadata,
            )

        # Determine status
        if returncode < 0:
            # Negative return code means killed by signal (OOM, SIGKILL, etc.) - infrastructure issue
            signal_num = -returncode
            combined_output = f"Process killed by signal {signal_num}\n\n=== STDOUT ===\n{stdout_str[:2000]}\n\n=== STDERR ===\n{stderr_str[:2000]}"
            return LintResult(
                problem_id=problem.id,
                source=problem.source,
                status="infra_error",
                findings=[],
                error_message=combined_output[:4000],
                duration_ms=duration_ms,
                provenance=make_provenance(toolchain),
                metadata=problem.metadata,
            )
        if returncode > 0:
            if done:
                return LintResult(
                    problem_id=problem.id,
                    source=problem.source,
                    status="findings" if findings else "ok",
                    findings=findings,
                    error_message=None,
                    duration_ms=duration_ms,
                    provenance=make_provenance(toolchain),
                    compile_error=True,
                    compile_error_message=compile_error_message,
                    metadata=problem.metadata,
                )
            return LintResult(
                problem_id=problem.id,
                source=problem.source,
                status="compile_error",
                findings=[],
                error_message=compile_error_message,
                duration_ms=duration_ms,
                provenance=make_provenance(toolchain),
                compile_error=True,
                compile_error_message=compile_error_message,
                metadata=problem.metadata,
            )
        if not done:
            combined_output = f"Linter did not complete (no ATP_DONE sentinel)\n\n=== STDOUT ===\n{stdout_str[:2000]}\n\n=== STDERR ===\n{stderr_str[:1000]}"
            return LintResult(
                problem_id=problem.id,
                source=problem.source,
                status="infra_error",
                findings=[],
                error_message=combined_output[:4000],
                duration_ms=duration_ms,
                provenance=make_provenance(toolchain),
                compile_error=compile_error,
                compile_error_message=compile_error_message,
                metadata=problem.metadata,
            )
        return LintResult(
            problem_id=problem.id,
            source=problem.source,
            status="findings" if findings else "ok",
            findings=findings,
            error_message=None,
            duration_ms=duration_ms,
            provenance=make_provenance(toolchain),
            compile_error=compile_error,
            compile_error_message=compile_error_message,
            metadata=problem.metadata,
        )

    finally:
        # Cleanup temp file and build artifacts
        _cleanup_problem_artifacts(workspace, file_stem)


def _cleanup_problem_artifacts(workspace: Path, file_stem: str):
    """Remove the temp .lean file used for a subprocess run.

    Direct `lean` execution does not emit build artifacts for these ad hoc files,
    so avoid scanning `.lake/build` on every row.
    """
    # Remove the .lean file
    problem_file = workspace / f"{file_stem}.lean"
    try:
        problem_file.unlink(missing_ok=True)
    except Exception:
        pass



async def run_batch(
    workspace: Path,
    problems: Iterable[Problem],
    toolchain: str,
    timeout: int = DEFAULT_TIMEOUT,
    on_result: Callable | None = None,
    workers: int = 1,
    collect_results: bool = True,
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
        results: list[LintResult] = []
        resolved = await _resolve_direct_lean_async(workspace)
        lean_cmd = resolved[0] if resolved is not None else None
        lean_env = resolved[1] if resolved is not None else None
        for idx, problem in enumerate(problems):
            result = await lint_problem(
                workspace,
                problem,
                toolchain,
                timeout,
                row_index=idx,
                lean_cmd=lean_cmd,
                lean_env=lean_env,
            )
            if collect_results:
                results.append(result)
            if on_result:
                on_result(result)
        return results
    # Parallel execution with a bounded in-flight window, streaming results in dataset order.
    # Keep the in-flight count aligned with the requested worker count so `-j N`
    # does not fan out into many more concurrent Lean processes than expected.
    window = max(1, workers)
    resolved = await _resolve_direct_lean_async(workspace)
    lean_cmd = resolved[0] if resolved is not None else None
    lean_env = resolved[1] if resolved is not None else None
    result_slots: dict[int, LintResult] = {}
    next_emit = 0
    results: list[LintResult] = []
    in_flight: set[asyncio.Task] = set()
    problem_iter = iter(problems)
    next_idx = 0
    exhausted = False

    async def process_one(idx: int, problem: Problem):
        result_slots[idx] = await lint_problem(
            workspace,
            problem,
            toolchain,
            timeout,
            row_index=idx,
            lean_cmd=lean_cmd,
            lean_env=lean_env,
        )

    def emit_ready() -> None:
        nonlocal next_emit
        while next_emit in result_slots:
            result = result_slots.pop(next_emit)
            if collect_results:
                results.append(result)
            if on_result:
                on_result(result)
            next_emit += 1

    while not exhausted or in_flight:
        while not exhausted and len(in_flight) < window:
            try:
                problem = next(problem_iter)
            except StopIteration:
                exhausted = True
                break
            task = asyncio.create_task(process_one(next_idx, problem))
            in_flight.add(task)
            next_idx += 1

        if in_flight:
            done, in_flight = await asyncio.wait(in_flight, return_when=asyncio.FIRST_COMPLETED)
            for task in done:
                task.result()
            emit_ready()

    emit_ready()
    return results
