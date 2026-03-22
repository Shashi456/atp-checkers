"""Persistent REPL backend for the ATP checkers runner.

Keeps Lean REPL processes alive across problems, caching preamble environments.
workers=1 is serial; workers>1 spawns additional REPL processes lazily with
sticky preamble ownership.

Requires `lake build repl` in the workspace.
"""
from __future__ import annotations

import asyncio
import itertools
import json
import os
import signal
import subprocess
import time
from pathlib import Path
from typing import Callable, Iterable, Optional

from .executor import lint_problem as lint_problem_subprocess
from .executor import run_batch as run_batch_subprocess
from .models import Problem, LintResult
from .models import parse_lint_output, has_done_sentinel, make_provenance, DEFAULT_TIMEOUT
from .preamble import build_env_cmd as _build_env_cmd
from .preamble import build_problem_cmd as _build_problem_cmd
from .preamble import split_preamble as _split_preamble


_SUBPROCESS_FALLBACK_ROWS = itertools.count()


# ---------------------------------------------------------------------------
# Exceptions
# ---------------------------------------------------------------------------

class ReplTimeoutError(TimeoutError):
    pass

class ReplProtocolError(RuntimeError):
    pass


# ---------------------------------------------------------------------------
# REPL message helpers
# ---------------------------------------------------------------------------

def _has_error_messages(messages: list[dict]) -> bool:
    return any(msg.get("severity") == "error" for msg in messages)


def _message_text(messages: list[dict]) -> str:
    parts = []
    for msg in messages:
        data = msg.get("data")
        if not data:
            continue
        severity = msg.get("severity", "info").upper()
        pos = msg.get("pos") or {}
        if "line" in pos and "column" in pos:
            parts.append(f"{severity} {pos['line']}:{pos['column']}: {data}")
        else:
            parts.append(f"{severity}: {data}")
    return "\n".join(parts)


def _infra_result(problem: Problem, toolchain: str, error_message: str) -> LintResult:
    return LintResult(
        problem_id=problem.id,
        source=problem.source,
        status="infra_error",
        findings=[],
        error_message=error_message,
        duration_ms=0,
        provenance=make_provenance(toolchain),
        metadata=problem.metadata,
    )


def _duration_ms(start: float) -> int:
    return int((time.monotonic() - start) * 1000)


def _make_result(
    problem: Problem, status: str, toolchain: str, start: float,
    *, findings=None, error_message=None, compile_error=False, compile_error_message=None,
) -> LintResult:
    return LintResult(
        problem_id=problem.id,
        source=problem.source,
        status=status,
        findings=findings or [],
        error_message=error_message,
        duration_ms=_duration_ms(start),
        provenance=make_provenance(toolchain),
        compile_error=compile_error,
        compile_error_message=compile_error_message,
        metadata=problem.metadata,
    )


# ---------------------------------------------------------------------------
# LeanRepl — single persistent REPL process
# ---------------------------------------------------------------------------

class LeanRepl:
    """A single persistent Lean REPL process with cached preamble environments."""

    def __init__(
        self,
        workspace: Path,
        toolchain: str,
        *,
        warmup_lock: asyncio.Lock | None = None,
        max_cached_envs: int = 4,
        max_problem_runs: int = 12,
        max_tree_rss_mb: float = 9000.0,
    ):
        self.workspace = workspace
        self.toolchain = toolchain
        self.proc: Optional[asyncio.subprocess.Process] = None
        self._env_cache: dict[tuple[str, ...], int] = {}
        self._warmup_lock = warmup_lock
        self.max_cached_envs = max(1, max_cached_envs)
        self.max_problem_runs = max(1, max_problem_runs)
        self.max_tree_rss_mb = max_tree_rss_mb
        self.problem_runs = 0
        self.restart_count = 0
        self._rss_check_interval = 4
        self._last_rss_mb = 0.0
        self._last_rss_problem_runs = 0

    async def _run_warmup_cmd(self, cmd: str, timeout: int) -> dict:
        if self._warmup_lock is None:
            return await self._send_cmd(cmd, timeout=timeout)
        async with self._warmup_lock:
            return await self._send_cmd(cmd, timeout=timeout)

    async def start(self) -> None:
        if self.proc and self.proc.returncode is None:
            return
        self._env_cache.clear()
        self.problem_runs = 0
        self._last_rss_mb = 0.0
        self._last_rss_problem_runs = 0
        self.proc = await asyncio.create_subprocess_exec(
            "lake", "exe", "repl",
            cwd=self.workspace,
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            start_new_session=True,
        )
        try:
            resp = await self._run_warmup_cmd("import AtpLinter", timeout=300)
            if resp.get("message"):
                raise RuntimeError(resp["message"])
            msgs = resp.get("messages", [])
            if _has_error_messages(msgs):
                raise RuntimeError(_message_text(msgs) or "Failed to import AtpLinter")
            env = resp.get("env")
            if not isinstance(env, int):
                raise RuntimeError(f"REPL did not return an environment: {json.dumps(resp)[:1000]}")
            self._env_cache[tuple()] = env
        except Exception:
            await self.stop()
            raise

    async def stop(self) -> None:
        self._env_cache.clear()
        if self.proc:
            try:
                if self.proc.stdin and not self.proc.stdin.is_closing():
                    self.proc.stdin.close()
                os.killpg(os.getpgid(self.proc.pid), signal.SIGTERM)
                await asyncio.wait_for(self.proc.wait(), timeout=5)
            except (ProcessLookupError, PermissionError, asyncio.TimeoutError):
                try:
                    os.killpg(os.getpgid(self.proc.pid), signal.SIGKILL)
                except (ProcessLookupError, PermissionError):
                    pass
            self.proc = None

    async def _restart(self) -> Optional[str]:
        try:
            await self.stop()
            await self.start()
            self.restart_count += 1
        except Exception as exc:
            return f"REPL restart failed: {exc}"
        return None

    async def _ensure_started(self) -> None:
        if self.proc is None or self.proc.returncode is not None:
            await self.start()

    async def _read_exit_stderr(self) -> str:
        if not self.proc or self.proc.stderr is None or self.proc.returncode is None:
            return ""
        try:
            data = await asyncio.wait_for(self.proc.stderr.read(), timeout=0.2)
        except asyncio.TimeoutError:
            return ""
        return data.decode("utf-8", errors="replace").strip()

    async def _send_cmd(self, cmd: str, timeout: int = 300, env: Optional[int] = None) -> dict:
        if not self.proc or self.proc.stdin is None or self.proc.stdout is None:
            raise ReplProtocolError("REPL is not running")
        if self.proc.returncode is not None:
            stderr = await self._read_exit_stderr()
            detail = f"REPL exited with code {self.proc.returncode}"
            if stderr:
                detail += f"\n{stderr}"
            raise ReplProtocolError(detail)

        payload: dict[str, object] = {"cmd": cmd}
        if env is not None:
            payload["env"] = env
        self.proc.stdin.write((json.dumps(payload) + "\n\n").encode("utf-8"))
        await self.proc.stdin.drain()

        lines = []
        try:
            while True:
                raw = await asyncio.wait_for(self.proc.stdout.readline(), timeout=timeout)
                if not raw:
                    stderr = await self._read_exit_stderr()
                    detail = "REPL closed stdout"
                    if self.proc.returncode is not None:
                        detail += f" (exit code {self.proc.returncode})"
                    if stderr:
                        detail += f"\n{stderr}"
                    raise ReplProtocolError(detail)
                decoded = raw.decode("utf-8", errors="replace").rstrip("\n")
                if decoded == "":
                    if lines:
                        break
                    continue
                lines.append(decoded)
        except asyncio.TimeoutError as exc:
            raise ReplTimeoutError(f"REPL command exceeded {timeout}s") from exc

        try:
            return json.loads("\n".join(lines))
        except json.JSONDecodeError as exc:
            raise ReplProtocolError(
                f"Malformed REPL JSON: {exc}\n{''.join(lines)[:1000]}"
            ) from exc

    async def _get_or_create_env(
        self, preamble: tuple[str, ...], timeout: int,
    ) -> tuple[Optional[int], Optional[str], Optional[str], Optional[str]]:
        cached = self._env_cache.get(preamble)
        if cached is not None:
            return cached, None, None, None
        resp = await self._run_warmup_cmd(_build_env_cmd(preamble), timeout=max(timeout, 300))
        if resp.get("message"):
            return None, "infra_error", resp["message"], None
        msgs = resp.get("messages", [])
        if _has_error_messages(msgs):
            msg = (_message_text(msgs) or json.dumps(resp))[:4000]
            return None, "compile_error", msg, msg
        env = resp.get("env")
        if not isinstance(env, int):
            return None, "infra_error", f"No env returned: {json.dumps(resp)[:1000]}", None
        self._env_cache[preamble] = env
        return env, None, None, None

    def current_tree_rss_mb(self) -> float:
        if self.proc is None or self.proc.returncode is not None:
            return 0.0
        try:
            out = subprocess.check_output(["ps", "-axo", "pid,ppid,rss"], text=True)
        except (OSError, subprocess.SubprocessError):
            return 0.0

        rows: dict[int, tuple[int, int]] = {}
        for line in out.splitlines():
            stripped = line.lstrip()
            if not stripped or not stripped[0].isdigit():
                continue
            parts = stripped.split(None, 2)
            if len(parts) < 3:
                continue
            try:
                pid = int(parts[0])
                rows[pid] = (int(parts[1]), int(parts[2]))
            except ValueError:
                continue

        children: dict[int, list[int]] = {}
        for pid, (ppid, _rss) in rows.items():
            children.setdefault(ppid, []).append(pid)

        total_kb = 0
        stack = [self.proc.pid]
        seen: set[int] = set()
        while stack:
            pid = stack.pop()
            if pid in seen:
                continue
            seen.add(pid)
            meta = rows.get(pid)
            if meta is not None:
                total_kb += meta[1]
            stack.extend(children.get(pid, []))
        return total_kb / 1024.0

    async def recycle_reason(self) -> Optional[str]:
        if len(self._env_cache) >= self.max_cached_envs:
            return f"cached_envs={len(self._env_cache)}>={self.max_cached_envs}"
        if self.problem_runs >= self.max_problem_runs:
            return f"problem_runs={self.problem_runs}>={self.max_problem_runs}"
        if self.max_tree_rss_mb > 0:
            if self.problem_runs == 1 or (self.problem_runs - self._last_rss_problem_runs) >= self._rss_check_interval:
                self._last_rss_mb = await asyncio.to_thread(self.current_tree_rss_mb)
                self._last_rss_problem_runs = self.problem_runs
            rss_mb = self._last_rss_mb
            if rss_mb >= self.max_tree_rss_mb:
                return f"rss_mb={rss_mb:.1f}>={self.max_tree_rss_mb:.1f}"
        return None

    async def run_problem(self, problem: Problem, timeout: int = 60,
                          _presplit: tuple[tuple[str, ...], str] | None = None) -> LintResult:
        start = time.monotonic()
        self.problem_runs += 1

        try:
            await self._ensure_started()
        except Exception as exc:
            return _make_result(problem, "infra_error", self.toolchain, start, error_message=str(exc))

        preamble, body = _presplit if _presplit else _split_preamble(problem.lean_code)

        try:
            env, status, error, compile_error_message = await self._get_or_create_env(preamble, timeout)
        except ReplTimeoutError:
            restart_err = await self._restart()
            msg = f"Exceeded {timeout}s timeout loading preamble"
            if restart_err:
                msg += f"\n\n{restart_err}"
            return _make_result(problem, "timeout", self.toolchain, start, error_message=msg)
        except ReplProtocolError as exc:
            restart_err = await self._restart()
            msg = f"REPL error loading preamble: {exc}"
            if restart_err:
                msg += f"\n\n{restart_err}"
            return _make_result(problem, "infra_error", self.toolchain, start, error_message=msg)

        if status is not None:
            return _make_result(
                problem,
                status,
                self.toolchain,
                start,
                error_message=error,
                compile_error=(status == "compile_error"),
                compile_error_message=compile_error_message,
            )

        assert env is not None

        try:
            resp = await self._send_cmd(_build_problem_cmd(body), timeout=timeout, env=env)
        except ReplTimeoutError:
            restart_err = await self._restart()
            msg = f"Exceeded {timeout}s timeout"
            if restart_err:
                msg += f"\n\n{restart_err}"
            return _make_result(problem, "timeout", self.toolchain, start, error_message=msg)
        except Exception as exc:
            restart_err = await self._restart()
            msg = f"REPL error: {exc}"
            if restart_err:
                msg += f"\n\n{restart_err}"
            return _make_result(problem, "infra_error", self.toolchain, start, error_message=msg)

        if resp.get("message"):
            restart_err = await self._restart()
            msg = f"REPL error: {resp['message']}"
            if restart_err:
                msg += f"\n\n{restart_err}"
            return _make_result(problem, "infra_error", self.toolchain, start, error_message=msg)

        # Classify from REPL messages
        messages = resp.get("messages", [])
        full_output = "\n".join(m.get("data", "") for m in messages if m.get("data"))
        compile_error = _has_error_messages(messages)
        compile_error_message = _message_text(messages)[:4000] if compile_error else None

        findings, parse_errors = parse_lint_output(full_output)
        done, done_meta = has_done_sentinel(full_output)

        truncation_error = None
        if done and done_meta and "findings" in done_meta:
            if done_meta["findings"] != len(findings):
                truncation_error = (
                    f"Output may be truncated: ATP_DONE reports {done_meta['findings']} "
                    f"findings but only {len(findings)} were parsed"
                )

        if parse_errors or truncation_error:
            parts = []
            if truncation_error:
                parts.append(f"=== TRUNCATION ===\n{truncation_error}")
            if parse_errors:
                parts.append("=== PARSE ERRORS ===\n" + "\n".join(parse_errors))
            return _make_result(
                problem, "infra_error", self.toolchain, start,
                findings=findings,
                error_message=("\n\n".join(parts))[:4000],
                compile_error=compile_error,
                compile_error_message=compile_error_message,
            )

        if compile_error and not done:
            return _make_result(
                problem, "compile_error", self.toolchain, start,
                error_message=compile_error_message,
                compile_error=True,
                compile_error_message=compile_error_message,
            )

        if not done:
            return _make_result(
                problem, "infra_error", self.toolchain, start,
                error_message=f"No ATP_DONE sentinel\n\n{full_output[:2000]}"[:4000],
            )

        return _make_result(
            problem, "findings" if findings else "ok", self.toolchain, start,
            findings=findings,
            compile_error=compile_error,
            compile_error_message=compile_error_message,
        )


# ---------------------------------------------------------------------------
# Worker pool
# ---------------------------------------------------------------------------

class _Worker:
    def __init__(self, workspace: Path, toolchain: str, timeout: int, warmup_lock: asyncio.Lock):
        self.repl = LeanRepl(workspace, toolchain, warmup_lock=warmup_lock)
        self.toolchain = toolchain
        self.workspace = workspace
        self.timeout = timeout
        self.pending = 0
        self.queue: asyncio.Queue[tuple[Problem, tuple[tuple[str, ...], str], asyncio.Future[LintResult]] | None] = asyncio.Queue()
        self._task: Optional[asyncio.Task] = None
        self._start_lock = asyncio.Lock()
        self._start_error: Optional[str] = None

    @property
    def is_started(self) -> bool:
        return self._task is not None

    @property
    def has_failed_start(self) -> bool:
        return self._start_error is not None

    async def start(self) -> None:
        if self._task is not None:
            return
        if self._start_error is not None:
            raise RuntimeError(self._start_error)
        async with self._start_lock:
            if self._task is not None:
                return
            if self._start_error is not None:
                raise RuntimeError(self._start_error)
            try:
                await self.repl.start()
            except Exception as exc:
                self._start_error = f"Failed to start worker REPL: {exc}"
                raise RuntimeError(self._start_error) from exc
            self._task = asyncio.create_task(self._loop())

    async def _loop(self) -> None:
        while True:
            item = await self.queue.get()
            if item is None:
                self.queue.task_done()
                break
            problem, presplit, future = item
            try:
                result = await self.repl.run_problem(problem, timeout=self.timeout, _presplit=presplit)
                if result.status in {"infra_error", "timeout"}:
                    await self.repl._restart()
                    result = await lint_problem_subprocess(
                        self.workspace,
                        problem,
                        self.toolchain,
                        timeout=self.timeout,
                        row_index=next(_SUBPROCESS_FALLBACK_ROWS),
                    )
                    result.metadata = dict(result.metadata)
                    result.metadata["backend_fallback"] = "subprocess"

                recycle_reason = await self.repl.recycle_reason()
                if recycle_reason is not None:
                    await self.repl._restart()
            except Exception as exc:
                if not future.done():
                    future.set_exception(exc)
            else:
                if not future.done():
                    future.set_result(result)
            finally:
                self.pending -= 1
                self.queue.task_done()

    async def submit(self, problem: Problem, presplit: tuple[tuple[str, ...], str]) -> LintResult:
        future: asyncio.Future[LintResult] = asyncio.get_running_loop().create_future()
        self.pending += 1
        await self.queue.put((problem, presplit, future))
        return await future

    async def stop(self) -> None:
        if self._task is None:
            return
        await self.queue.put(None)
        await self._task
        self._task = None
        await self.repl.stop()


class _Pool:
    _SPAWN_THRESHOLD = 2

    def __init__(self, workspace: Path, toolchain: str, timeout: int, workers: int):
        self.toolchain = toolchain
        self._warmup_lock = asyncio.Lock()
        self._workers = [_Worker(workspace, toolchain, timeout, self._warmup_lock) for _ in range(max(1, workers))]
        self._key_owner: dict[tuple[str, ...], _Worker] = {}
        self._lock = asyncio.Lock()

    async def start(self) -> None:
        await self._workers[0].start()

    async def stop(self) -> None:
        self._key_owner.clear()
        await asyncio.gather(*(w.stop() for w in self._workers if w.is_started))

    async def _pick(self, key: tuple[str, ...]) -> _Worker:
        while True:
            candidate: _Worker | None = None
            fallback: _Worker | None = None

            async with self._lock:
                owner = self._key_owner.get(key)
                if owner is not None:
                    return owner

                started = [w for w in self._workers if w.is_started]
                if not started:
                    candidate = self._workers[0]
                else:
                    best = min(started, key=lambda w: w.pending)
                    unstarted = next(
                        (w for w in self._workers if not w.is_started and not w.has_failed_start),
                        None,
                    )
                    if unstarted and best.pending >= self._SPAWN_THRESHOLD:
                        candidate = unstarted
                        fallback = best
                    else:
                        self._key_owner[key] = best
                        return best

            assert candidate is not None

            try:
                await candidate.start()
            except Exception:
                async with self._lock:
                    owner = self._key_owner.get(key)
                    if owner is not None:
                        return owner

                    started = [w for w in self._workers if w.is_started]
                    if started:
                        chosen = fallback if fallback is not None and fallback.is_started else min(started, key=lambda w: w.pending)
                        self._key_owner[key] = chosen
                        return chosen
                raise

            async with self._lock:
                owner = self._key_owner.get(key)
                if owner is not None:
                    return owner
                if candidate.is_started:
                    self._key_owner[key] = candidate
                    return candidate

    async def run_problem(self, problem: Problem) -> LintResult:
        presplit = _split_preamble(problem.lean_code)
        key = presplit[0]
        try:
            worker = await self._pick(key)
            return await worker.submit(problem, presplit)
        except Exception as exc:
            return _infra_result(problem, self.toolchain, f"Worker crashed: {exc}")


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

async def run_batch(
    workspace: Path,
    problems: Iterable[Problem],
    toolchain: str,
    timeout: int = DEFAULT_TIMEOUT,
    on_result: Optional[Callable] = None,
    workers: int = 1,
    collect_results: bool = True,
) -> list[LintResult]:
    """Run linter using persistent REPL worker pool.

    workers=1 is serial. workers>1 spawns REPL processes lazily.
    Uses a bounded window to avoid creating one coroutine per problem.
    """
    pool = _Pool(workspace, toolchain, timeout, workers)
    results: list[LintResult] = []

    try:
        await pool.start()
    except (FileNotFoundError, RuntimeError, ReplProtocolError, ReplTimeoutError) as exc:
        return await run_batch_subprocess(
            workspace,
            problems,
            toolchain,
            timeout=timeout,
            on_result=on_result,
            workers=workers,
            collect_results=collect_results,
        )

    try:
        if workers <= 1:
            for problem in problems:
                r = await pool.run_problem(problem)
                if collect_results:
                    results.append(r)
                if on_result:
                    on_result(r)
        else:
            # Bounded parallel: at most `window` in-flight at a time,
            # emit results in dataset order.
            window = max(1, workers)
            slots: dict[int, LintResult] = {}
            next_emit = 0
            in_flight: set[asyncio.Task] = set()
            feed_idx = 0
            problem_iter = iter(problems)
            exhausted = False

            async def _process(idx: int, problem: Problem) -> None:
                slots[idx] = await pool.run_problem(problem)

            def _emit() -> None:
                nonlocal next_emit
                while next_emit in slots:
                    r = slots.pop(next_emit)
                    if collect_results:
                        results.append(r)
                    if on_result:
                        on_result(r)
                    next_emit += 1

            while not exhausted or in_flight:
                # Fill window
                while not exhausted and len(in_flight) < window:
                    try:
                        problem = next(problem_iter)
                    except StopIteration:
                        exhausted = True
                        break
                    task = asyncio.create_task(_process(feed_idx, problem))
                    in_flight.add(task)
                    feed_idx += 1

                # Wait for at least one to finish
                if in_flight:
                    done, in_flight = await asyncio.wait(in_flight, return_when=asyncio.FIRST_COMPLETED)
                    for task in done:
                        task.result()  # propagate exceptions
                    _emit()

            _emit()  # flush remaining
    finally:
        await pool.stop()

    return results
