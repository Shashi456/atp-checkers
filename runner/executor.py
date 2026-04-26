"""Subprocess execution for the ATP checkers runner.

Spawns a fresh Lean process per problem. It resolves the workspace environment
once via `lake env` and then invokes the Lean binary directly, falling back to
`lake env lean` if env resolution fails. Still slow for Mathlib-heavy datasets
due to repeated import cost, but much cheaper than wrapping every problem in a
fresh `lake env` shell.
"""
from __future__ import annotations

import concurrent.futures
import hashlib
import json
import logging
import os
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
from collections.abc import Callable, Iterable
from dataclasses import dataclass
from pathlib import Path

from .models import (
    DEFAULT_TIMEOUT,
    LintResult,
    Problem,
    classify_lint_execution,
    make_provenance,
)
from .preamble import (
    normalize_imports,
    partition_preamble,
    render_problem_source,
    split_preamble,
)

log = logging.getLogger(__name__)

_CACHE_FAILURE_RETRY_SECONDS = 30.0

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
    if not isinstance(extra_paths, list | tuple):
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
    """Return a cached import-bundle module when the optimization is available.

    Import bundles are opportunistic startup optimization. Failure to compile
    one must fall back to the original problem source, not affect result status.
    """
    if lean_cmd is None or lean_env is None or len(lean_cmd) != 1:
        log.debug("Skipping import-bundle cache: unsupported Lean command %r", lean_cmd)
        return None

    lean_path = lean_cmd[0]
    resolved_lean = lean_path if Path(lean_path).is_absolute() else shutil.which(lean_path)
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
                capture_output=True,
                text=True, check=False,
            )
            if proc.returncode != 0:
                log.debug(
                    "Import-bundle cache compile failed for %s: %s",
                    module_name,
                    (proc.stderr or proc.stdout or "unknown error")[:400],
                )
                with _IMPORT_CACHE_LOCK:
                    _IMPORT_MODULE_FAILURES[key] = (
                        time.monotonic() + _CACHE_FAILURE_RETRY_SECONDS
                    )
                return None

        with _IMPORT_CACHE_LOCK:
            _IMPORT_MODULE_CACHE[key] = module_name
        return module_name


def _resolve_direct_lean(workspace: Path) -> tuple[tuple[str, ...], dict[str, str]] | None:
    """Resolve a workspace-specific Lean command and environment once.

    Uses the current Python executable under `lake env` to capture the effective
    Lean environment, then caches the direct Lean binary path from `LEAN`.
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
                sys.executable,
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
            _LEAN_ENV_FAILURES[workspace] = (
                time.monotonic() + _CACHE_FAILURE_RETRY_SECONDS
            )
        return None

    with _LEAN_ENV_LOCK:
        _LEAN_ENV_CACHE[workspace] = resolved
    return resolved


@dataclass(frozen=True)
class _LeanProcessResult:
    returncode: int | None
    stdout: bytes
    stderr: bytes
    timed_out: bool = False
    spawn_error: str | None = None
    cancelled: bool = False


class _RunCancellation:
    """Track subprocesses owned by one batch so interrupts can stop them."""

    def __init__(self) -> None:
        self._event = threading.Event()
        self._lock = threading.Lock()
        self._processes: set[subprocess.Popen[bytes]] = set()

    def is_set(self) -> bool:
        return self._event.is_set()

    def register(self, proc: subprocess.Popen[bytes]) -> None:
        with self._lock:
            if not self._event.is_set():
                self._processes.add(proc)
                return

        _terminate_process_group_now(proc)

    def unregister(self, proc: subprocess.Popen[bytes]) -> None:
        with self._lock:
            self._processes.discard(proc)

    def cancel(self) -> None:
        with self._lock:
            self._event.set()
            processes = tuple(self._processes)

        for proc in processes:
            _terminate_process_group_now(proc)


def _kill_process_group(proc: subprocess.Popen[bytes]) -> None:
    try:
        pgid = os.getpgid(proc.pid)
    except (ProcessLookupError, PermissionError):
        return

    for sig, wait_seconds in ((signal.SIGTERM, 0.5), (signal.SIGKILL, 2.0)):
        try:
            os.killpg(pgid, sig)
        except (ProcessLookupError, PermissionError):
            return
        try:
            proc.wait(timeout=wait_seconds)
            return
        except subprocess.TimeoutExpired:
            continue


def _terminate_process_group_now(proc: subprocess.Popen[bytes]) -> None:
    try:
        pgid = os.getpgid(proc.pid)
    except (ProcessLookupError, PermissionError):
        return

    for sig in (signal.SIGTERM, signal.SIGKILL):
        try:
            os.killpg(pgid, sig)
        except (ProcessLookupError, PermissionError):
            return


def _run_lean_process_sync(
    lean_cmd: tuple[str, ...],
    problem_file_name: str,
    workspace: Path,
    env: dict[str, str] | None,
    timeout: int,
    cancellation: _RunCancellation | None = None,
) -> _LeanProcessResult:
    """Run Lean with subprocess primitives that behave reliably under threads."""
    if cancellation is not None and cancellation.is_set():
        return _LeanProcessResult(
            returncode=None,
            stdout=b"",
            stderr=b"",
            cancelled=True,
        )

    try:
        proc = subprocess.Popen(
            [*lean_cmd, problem_file_name],
            cwd=workspace,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            start_new_session=True,
        )
    except (OSError, FileNotFoundError) as exc:
        return _LeanProcessResult(
            returncode=None,
            stdout=b"",
            stderr=b"",
            spawn_error=str(exc),
        )

    if cancellation is not None:
        cancellation.register(proc)

    try:
        stdout, stderr = proc.communicate(timeout=timeout)
        return _LeanProcessResult(
            proc.returncode,
            stdout,
            stderr,
            cancelled=cancellation.is_set() if cancellation is not None else False,
        )
    except subprocess.TimeoutExpired as exc:
        _kill_process_group(proc)
        try:
            stdout, stderr = proc.communicate(timeout=2.0)
        except subprocess.TimeoutExpired:
            stdout = exc.output or b""
            stderr = exc.stderr or b""
        return _LeanProcessResult(
            returncode=proc.returncode,
            stdout=stdout or b"",
            stderr=stderr or b"",
            timed_out=True,
        )
    except BaseException:
        _kill_process_group(proc)
        raise
    finally:
        if cancellation is not None:
            cancellation.unregister(proc)


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
    for path in (
        *_env_extra_lean_paths(),
        *_normalize_extra_lean_paths(problem.metadata.get("extra_lean_paths")),
    ):
        if path not in merged:
            merged.append(path)
    return tuple(merged)


def _elapsed_ms(start_time: float) -> int:
    return int((time.monotonic() - start_time) * 1000)


def _infra_error_result(
    problem: Problem,
    toolchain: str,
    start_time: float,
    message: str,
) -> LintResult:
    return LintResult(
        problem_id=problem.id,
        source=problem.source,
        status="infra_error",
        findings=[],
        error_message=message,
        duration_ms=_elapsed_ms(start_time),
        provenance=make_provenance(toolchain),
        metadata=problem.metadata,
    )


def wrap_with_linter(lean_code: str) -> str:
    """Wrap problem code with linter import and check command.

    If the code ends with 'by' (common in benchmark datasets that omit the proof),
    append 'sorry' so that '#check_atp_all' isn't parsed as a tactic.
    """
    return render_problem_source(lean_code)


def _lint_problem_sync(
    workspace: Path,
    problem: Problem,
    toolchain: str,
    timeout: int = DEFAULT_TIMEOUT,
    row_index: int = 0,
    lean_cmd: tuple[str, ...] | None = None,
    lean_env: dict[str, str] | None = None,
    cancellation: _RunCancellation | None = None,
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
        import_module = _ensure_import_bundle(
            workspace,
            imports,
            lean_cmd,
            problem_lean_env,
            extra_paths,
        )
    try:
        problem_file.write_text(
            render_problem_source(problem.lean_code, import_module=import_module),
            encoding="utf-8",
        )
    except OSError as e:
        return _infra_error_result(
            problem,
            toolchain,
            start_time,
            f"Failed to write problem file: {e}",
        )

    try:
        # Run Lean with timeout, in its own process group
        if lean_cmd is None:
            resolved = _resolve_direct_lean(workspace)
            if resolved is not None:
                lean_cmd, lean_env = resolved
        if lean_env is not None:
            problem_lean_env = _augment_lean_env(workspace, lean_env, extra_paths)
        if lean_cmd is None:
            lean_cmd = ("lake", "env", "lean")
            if extra_paths:
                problem_lean_env = _augment_lean_env(
                    workspace,
                    dict(os.environ),
                    extra_paths,
                )
                log.debug(
                    "Extra Lean paths injected into lake env lean fallback: %s",
                    extra_paths,
                )

        if cancellation is None:
            proc_result = _run_lean_process_sync(
                lean_cmd,
                problem_file.name,
                workspace,
                problem_lean_env,
                timeout,
            )
        else:
            proc_result = _run_lean_process_sync(
                lean_cmd,
                problem_file.name,
                workspace,
                problem_lean_env,
                timeout,
                cancellation=cancellation,
            )
        if proc_result.spawn_error is not None:
            return _infra_error_result(
                problem,
                toolchain,
                start_time,
                f"Failed to spawn Lean process: {proc_result.spawn_error}",
            )
        if proc_result.cancelled:
            return _infra_error_result(
                problem,
                toolchain,
                start_time,
                "Lean process cancelled",
            )
        if proc_result.timed_out:
            return LintResult(
                problem_id=problem.id,
                source=problem.source,
                status="timeout",
                findings=[],
                error_message=f"Exceeded {timeout}s timeout",
                duration_ms=_elapsed_ms(start_time),
                provenance=make_provenance(toolchain),
                metadata=problem.metadata,
            )

        if proc_result.returncode is None:
            return _infra_error_result(
                problem,
                toolchain,
                start_time,
                "Lean process completed without a return code",
            )
        return classify_lint_execution(
            problem=problem,
            toolchain=toolchain,
            duration_ms=_elapsed_ms(start_time),
            stdout=proc_result.stdout.decode("utf-8", errors="replace"),
            stderr=proc_result.stderr.decode("utf-8", errors="replace"),
            returncode=proc_result.returncode,
        )

    finally:
        # Cleanup temp file and build artifacts
        _cleanup_problem_artifacts(workspace, file_stem)


async def lint_problem(
    workspace: Path,
    problem: Problem,
    toolchain: str,
    timeout: int = DEFAULT_TIMEOUT,
    row_index: int = 0,
    lean_cmd: tuple[str, ...] | None = None,
    lean_env: dict[str, str] | None = None,
) -> LintResult:
    return _lint_problem_sync(
        workspace,
        problem,
        toolchain,
        timeout=timeout,
        row_index=row_index,
        lean_cmd=lean_cmd,
        lean_env=lean_env,
    )


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



def _run_batch_sync(
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
    resolved = _resolve_direct_lean(workspace)
    lean_cmd = resolved[0] if resolved is not None else None
    lean_env = resolved[1] if resolved is not None else None
    cancellation = _RunCancellation()

    if workers <= 1:
        # Sequential execution
        results: list[LintResult] = []
        try:
            for idx, problem in enumerate(problems):
                result = _lint_problem_sync(
                    workspace,
                    problem,
                    toolchain,
                    timeout,
                    row_index=idx,
                    lean_cmd=lean_cmd,
                    lean_env=lean_env,
                    cancellation=cancellation,
                )
                if collect_results:
                    results.append(result)
                if on_result:
                    on_result(result)
        except BaseException:
            cancellation.cancel()
            raise
        return results

    # Parallel execution with a bounded in-flight window, streaming results in dataset order.
    # Keep the in-flight count aligned with the requested worker count so `-j N`
    # does not fan out into many more concurrent Lean processes than expected.
    window = max(1, workers)
    result_slots: dict[int, LintResult] = {}
    next_emit = 0
    results: list[LintResult] = []
    in_flight: dict[concurrent.futures.Future[LintResult], int] = {}
    problem_iter = iter(problems)
    next_idx = 0
    exhausted = False

    def process_one(idx: int, problem: Problem) -> LintResult:
        return _lint_problem_sync(
            workspace,
            problem,
            toolchain,
            timeout,
            row_index=idx,
            lean_cmd=lean_cmd,
            lean_env=lean_env,
            cancellation=cancellation,
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

    completed = False
    pool = concurrent.futures.ThreadPoolExecutor(max_workers=window)
    try:
        while not exhausted or in_flight:
            while not exhausted and len(in_flight) < window:
                try:
                    problem = next(problem_iter)
                except StopIteration:
                    exhausted = True
                    break
                future = pool.submit(process_one, next_idx, problem)
                in_flight[future] = next_idx
                next_idx += 1

            if in_flight:
                done, _pending = concurrent.futures.wait(
                    in_flight,
                    return_when=concurrent.futures.FIRST_COMPLETED,
                )
                for future in done:
                    idx = in_flight.pop(future)
                    result_slots[idx] = future.result()
                emit_ready()

        emit_ready()
        completed = True
        return results
    finally:
        if completed:
            pool.shutdown(wait=True)
        else:
            cancellation.cancel()
            for future in in_flight:
                future.cancel()
            pool.shutdown(wait=False, cancel_futures=True)


async def run_batch(
    workspace: Path,
    problems: Iterable[Problem],
    toolchain: str,
    timeout: int = DEFAULT_TIMEOUT,
    on_result: Callable | None = None,
    workers: int = 1,
    collect_results: bool = True,
) -> list[LintResult]:
    """Async compatibility wrapper around the synchronous subprocess backend."""
    return _run_batch_sync(
        workspace,
        problems,
        toolchain,
        timeout=timeout,
        on_result=on_result,
        workers=workers,
        collect_results=collect_results,
    )
