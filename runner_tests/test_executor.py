import asyncio
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest.mock import patch

import runner.executor as executor_module
from runner.executor import (
    _ensure_import_bundle,
    _resolve_direct_lean,
    lint_problem,
    run_batch,
    wrap_with_linter,
)
from runner.models import (
    LintResult,
    Problem,
    Provenance,
    has_done_sentinel,
    parse_lint_output,
)
from runner.preamble import split_preamble


def _mk_result(problem: Problem) -> LintResult:
    return LintResult(
        problem_id=problem.id,
        source=problem.source,
        status="ok",
        findings=[],
        error_message=None,
        duration_ms=1,
        provenance=Provenance(
            lean_toolchain="leanprover/lean4:v4.24.0",
            timestamp="2026-02-24T00:00:00+00:00",
        ),
        metadata=problem.metadata,
    )


def _mk_proc_result(
    stdout: str,
    stderr: str = "",
    returncode: int | None = 0,
    timed_out: bool = False,
    spawn_error: str | None = None,
    cancelled: bool = False,
) -> executor_module._LeanProcessResult:
    return executor_module._LeanProcessResult(
        returncode=returncode,
        stdout=stdout.encode("utf-8"),
        stderr=stderr.encode("utf-8"),
        timed_out=timed_out,
        spawn_error=spawn_error,
        cancelled=cancelled,
    )


class ExecutorParsingTests(unittest.TestCase):
    def setUp(self):
        executor_module._LEAN_ENV_CACHE.clear()
        executor_module._LEAN_ENV_FAILURES.clear()
        executor_module._IMPORT_MODULE_CACHE.clear()
        executor_module._IMPORT_MODULE_FAILURES.clear()
        executor_module._IMPORT_MODULE_LOCKS.clear()

    def test_wrap_with_linter(self):
        wrapped = wrap_with_linter("def x : Nat := 1")
        self.assertIn("import AtpLinter", wrapped)
        self.assertIn("#check_atp_all", wrapped)
        self.assertIn("def x : Nat := 1", wrapped)

    def test_wrap_with_linter_appends_sorry_after_by_comment(self):
        wrapped = wrap_with_linter("example : True := by -- placeholder")
        self.assertIn("sorry", wrapped)

    def test_split_preamble_ignores_import_inside_block_comment(self):
        preamble, body = split_preamble("/- import Mathlib -/\nexample : True := by trivial\n")
        self.assertEqual((), preamble)
        self.assertIn("import Mathlib", body)

    def test_parse_lint_output_collects_findings_and_malformed_json(self):
        stdout = "\n".join([
            'ATP_LINT:{"category":"Potential Division by Zero","severity":"WARNING","declaration":"d","message":"m","confidence":"maybe","provedBy":null}',
            "ATP_LINT:{bad-json",
        ])
        findings, errors = parse_lint_output(stdout)
        self.assertEqual(1, len(findings))
        self.assertEqual("Potential Division by Zero", findings[0].category)
        self.assertEqual(1, len(errors))
        self.assertIn("Malformed ATP_LINT JSON", errors[0])

    def test_has_done_sentinel_parses_metadata(self):
        done, meta, parse_error = has_done_sentinel('x\nATP_DONE:{"declarations":2,"findings":3}\n')
        self.assertTrue(done)
        self.assertIsNone(parse_error)
        self.assertEqual(2, meta["declarations"])
        self.assertEqual(3, meta["findings"])


class ExecutorAsyncTests(unittest.TestCase):
    def setUp(self):
        executor_module._LEAN_ENV_CACHE.clear()
        executor_module._LEAN_ENV_FAILURES.clear()
        executor_module._IMPORT_MODULE_CACHE.clear()
        executor_module._IMPORT_MODULE_FAILURES.clear()
        executor_module._IMPORT_MODULE_LOCKS.clear()

    def run_async(self, coro):
        loop = asyncio.new_event_loop()
        try:
            asyncio.set_event_loop(loop)
            return loop.run_until_complete(coro)
        finally:
            asyncio.set_event_loop(None)
            loop.close()

    def test_lint_problem_status_findings(self):
        async def run():
            stdout = "\n".join([
                'ATP_LINT:{"category":"Potential Division by Zero","severity":"WARNING","declaration":"d","message":"m","confidence":"maybe","provedBy":null}',
                'ATP_DONE:{"declarations":1,"findings":1}',
            ])

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                problem = Problem(id="p1", source="s", lean_code="def d : Nat := 1", metadata={})
                with patch("runner.executor._resolve_direct_lean", return_value=None), \
                     patch("runner.executor._run_lean_process_sync", return_value=_mk_proc_result(stdout)):
                    result = await lint_problem(workspace, problem, "leanprover/lean4:v4.24.0", timeout=1, row_index=7)

            self.assertEqual("findings", result.status)
            self.assertEqual(1, len(result.findings))
            self.assertEqual("Potential Division by Zero", result.findings[0].category)
            self.assertFalse(result.compile_error)
            self.assertIsNone(result.compile_error_message)

        self.run_async(run())

    def test_ensure_import_bundle_compiles_once(self):
        class CompletedProc:
            def __init__(self):
                self.returncode = 0
                self.stdout = ""
                self.stderr = ""

        with tempfile.TemporaryDirectory() as td:
            workspace = Path(td)
            fake_lean = workspace / "lean"
            fake_lean.write_text("", encoding="utf-8")
            calls = []

            def fake_run(args, cwd, env, capture_output, text, check=False):
                calls.append(args)
                self.assertTrue(capture_output)
                self.assertFalse(check)
                Path(args[2]).write_text("compiled", encoding="utf-8")
                return CompletedProc()

            with patch("runner.executor.subprocess.run", side_effect=fake_run):
                first = _ensure_import_bundle(
                    workspace,
                    ("import Mathlib",),
                    (str(fake_lean),),
                    {"LEAN": str(fake_lean), "LEAN_PATH": ""},
                )
                second = _ensure_import_bundle(
                    workspace,
                    ("import Mathlib",),
                    (str(fake_lean),),
                    {"LEAN": str(fake_lean), "LEAN_PATH": ""},
                )

        self.assertIsNotNone(first)
        self.assertEqual(first, second)
        self.assertEqual(1, len(calls))
        assert first is not None
        self.assertTrue(first.startswith("AtpCache.Imports_"))

    def test_resolve_direct_lean_caches_workspace_env(self):
        with tempfile.TemporaryDirectory() as td:
            workspace = Path(td)
            payload = '{"LEAN": "/tmp/lean", "LEAN_PATH": "/tmp/path"}'
            with patch("runner.executor.subprocess.check_output", return_value=payload) as mock_check:
                first = _resolve_direct_lean(workspace)
                second = _resolve_direct_lean(workspace)

        self.assertIsNotNone(first)
        assert first is not None
        self.assertEqual(first, second)
        self.assertEqual(1, mock_check.call_count)
        self.assertEqual(
            str(workspace.resolve() / ".atp_import_cache"),
            first[1]["LEAN_PATH"].split(":", 1)[0],
        )

    def test_lint_problem_status_ok(self):
        async def run():
            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                problem = Problem(id="p2", source="s", lean_code="def ok : Nat := 1", metadata={})
                with patch("runner.executor._resolve_direct_lean", return_value=None), \
                     patch(
                    "runner.executor._run_lean_process_sync",
                    return_value=_mk_proc_result('ATP_DONE:{"declarations":1,"findings":0}'),
                ):
                    result = await lint_problem(workspace, problem, "leanprover/lean4:v4.24.0", timeout=1)

            self.assertEqual("ok", result.status)
            self.assertEqual(0, len(result.findings))
            self.assertFalse(result.compile_error)
            self.assertIsNone(result.compile_error_message)

        self.run_async(run())

    def test_lint_problem_uses_direct_lean_when_resolved(self):
        async def run():
            seen = {}

            def fake_run(lean_cmd, problem_file_name, workspace, env, timeout):
                seen["lean_cmd"] = lean_cmd
                seen["problem_file_name"] = problem_file_name
                seen["env"] = env
                return _mk_proc_result('ATP_DONE:{"declarations":1,"findings":0}')

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                problem = Problem(id="p2", source="s", lean_code="def ok : Nat := 1", metadata={})
                with patch("runner.executor._run_lean_process_sync", side_effect=fake_run), \
                     patch("runner.executor._ensure_import_bundle", return_value=None):
                    result = await lint_problem(
                        workspace,
                        problem,
                        "leanprover/lean4:v4.24.0",
                        timeout=1,
                        lean_cmd=("/tmp/lean",),
                        lean_env={"LEAN": "/tmp/lean"},
                    )

            self.assertEqual("ok", result.status)
            self.assertEqual(("/tmp/lean",), seen["lean_cmd"])
            self.assertTrue(seen["problem_file_name"].startswith("_Problem_0_p2_"))
            self.assertTrue(seen["problem_file_name"].endswith(".lean"))
            self.assertEqual("/tmp/lean", seen["env"]["LEAN"])
            self.assertIn(".atp_import_cache", seen["env"].get("LEAN_PATH", ""))

        self.run_async(run())

    def test_lint_problem_status_compile_error(self):
        async def run():
            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                problem = Problem(id="p3", source="s", lean_code="def bad := ", metadata={})
                with patch("runner.executor._resolve_direct_lean", return_value=None), \
                     patch(
                    "runner.executor._run_lean_process_sync",
                    return_value=_mk_proc_result("", stderr="compile failed", returncode=1),
                ):
                    result = await lint_problem(workspace, problem, "leanprover/lean4:v4.24.0", timeout=1)

            self.assertEqual("compile_error", result.status)
            self.assertTrue(result.compile_error)
            self.assertIn("compile failed", result.error_message)
            self.assertIn("compile failed", result.compile_error_message)

        self.run_async(run())

    def test_lint_problem_keeps_findings_when_compile_error_has_done(self):
        async def run():
            stdout = "\n".join([
                "bad.lean:1:1: error: parse failed",
                'ATP_LINT:{"category":"Potential Division by Zero","severity":"WARNING","declaration":"d","message":"m","confidence":"maybe","provedBy":null}',
                'ATP_DONE:{"declarations":1,"findings":1}',
            ])

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                problem = Problem(id="p3b", source="s", lean_code="def bad := ", metadata={})
                with patch("runner.executor._resolve_direct_lean", return_value=None), \
                     patch(
                    "runner.executor._run_lean_process_sync",
                    return_value=_mk_proc_result(stdout, stderr="compile failed", returncode=1),
                ):
                    result = await lint_problem(workspace, problem, "leanprover/lean4:v4.24.0", timeout=1)

            self.assertEqual("findings", result.status)
            self.assertTrue(result.compile_error)
            self.assertEqual(1, len(result.findings))
            self.assertIn("compile failed", result.compile_error_message)
            self.assertIsNone(result.error_message)

        self.run_async(run())

    def test_lint_problem_status_infra_error_without_done(self):
        async def run():
            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                problem = Problem(id="p4", source="s", lean_code="def x : Nat := 0", metadata={})
                with patch("runner.executor._resolve_direct_lean", return_value=None), \
                     patch(
                    "runner.executor._run_lean_process_sync",
                    return_value=_mk_proc_result("ATP_LINT:{}"),
                ):
                    result = await lint_problem(workspace, problem, "leanprover/lean4:v4.24.0", timeout=1)

            self.assertEqual("infra_error", result.status)
            self.assertIn("no ATP_DONE sentinel", result.error_message)

        self.run_async(run())

    def test_lint_problem_status_infra_error_on_truncation_mismatch(self):
        async def run():
            stdout = "\n".join([
                'ATP_LINT:{"category":"Potential Division by Zero","severity":"WARNING","declaration":"d","message":"m","confidence":"maybe","provedBy":null}',
                'ATP_DONE:{"declarations":1,"findings":2}',
            ])

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                problem = Problem(id="p5", source="s", lean_code="def x : Nat := 0", metadata={})
                with patch("runner.executor._resolve_direct_lean", return_value=None), \
                     patch("runner.executor._run_lean_process_sync", return_value=_mk_proc_result(stdout)):
                    result = await lint_problem(workspace, problem, "leanprover/lean4:v4.24.0", timeout=1)

            self.assertEqual("infra_error", result.status)
            self.assertIn("Output may be truncated", result.error_message)
            self.assertEqual(1, len(result.findings))

        self.run_async(run())

    def test_lint_problem_status_timeout(self):
        async def run():
            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                problem = Problem(id="p6", source="s", lean_code="def x : Nat := 0", metadata={})
                with patch("runner.executor._resolve_direct_lean", return_value=None), \
                     patch(
                    "runner.executor._run_lean_process_sync",
                    return_value=_mk_proc_result("", returncode=None, timed_out=True),
                ):
                    result = await lint_problem(workspace, problem, "leanprover/lean4:v4.24.0", timeout=0.01)

            self.assertEqual("timeout", result.status)
            self.assertIn("Exceeded", result.error_message)

        self.run_async(run())

    def test_run_cancellation_terminates_registered_process_group(self):
        class FakeProc:
            pid = 123

        cancellation = executor_module._RunCancellation()
        proc = FakeProc()

        with patch("runner.executor.os.getpgid", return_value=456), \
             patch("runner.executor.os.killpg") as mock_killpg:
            cancellation.register(proc)
            cancellation.cancel()

        self.assertEqual(
            [
                (456, executor_module.signal.SIGTERM),
                (456, executor_module.signal.SIGKILL),
            ],
            [call.args for call in mock_killpg.call_args_list],
        )

    def test_run_batch_sequential_passes_row_index(self):
        async def run():
            problems = [
                Problem(id="a", source="src", lean_code="def a : Nat := 0", metadata={}),
                Problem(id="b", source="src", lean_code="def b : Nat := 0", metadata={}),
                Problem(id="c", source="src", lean_code="def c : Nat := 0", metadata={}),
            ]
            calls = []

            def fake_lint(workspace, problem, toolchain, timeout, row_index=0, **_kwargs):
                calls.append(row_index)
                return _mk_result(problem)

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                with patch("runner.executor._lint_problem_sync", side_effect=fake_lint), \
                     patch("runner.executor._resolve_direct_lean", return_value=None):
                    results = await run_batch(workspace, problems, "leanprover/lean4:v4.24.0", workers=1)

            self.assertEqual(3, len(results))
            self.assertEqual([0, 1, 2], calls)

        self.run_async(run())

    def test_run_batch_parallel_interrupt_signals_running_jobs(self):
        async def run():
            problems = [
                Problem(id="wait", source="src", lean_code="def wait : Nat := 0", metadata={}),
                Problem(id="boom", source="src", lean_code="def boom : Nat := 0", metadata={}),
            ]
            wait_started = threading.Event()
            cancel_seen = threading.Event()

            def fake_run_lean(
                lean_cmd,
                problem_file_name,
                workspace,
                env,
                timeout,
                cancellation=None,
            ):
                if "_wait_" in problem_file_name:
                    wait_started.set()
                    deadline = time.time() + 2.0
                    while time.time() < deadline:
                        if cancellation is not None and cancellation.is_set():
                            cancel_seen.set()
                            return _mk_proc_result(
                                "",
                                returncode=None,
                                cancelled=True,
                            )
                        time.sleep(0.005)
                    raise AssertionError("running worker was not cancelled")

                self.assertIn("_boom_", problem_file_name)
                self.assertTrue(wait_started.wait(1.0))
                raise KeyboardInterrupt

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                with patch("runner.executor._resolve_direct_lean", return_value=None), \
                     patch("runner.executor._ensure_import_bundle", return_value=None), \
                     patch("runner.executor._run_lean_process_sync", side_effect=fake_run_lean), \
                     self.assertRaises(KeyboardInterrupt):
                    await run_batch(
                        workspace,
                        problems,
                        "leanprover/lean4:v4.24.0",
                        workers=2,
                    )

            self.assertTrue(cancel_seen.wait(1.0))

        self.run_async(run())

    def test_run_batch_parallel_passes_row_index(self):
        async def run():
            problems = [
                Problem(id="a", source="src", lean_code="def a : Nat := 0", metadata={}),
                Problem(id="b", source="src", lean_code="def b : Nat := 0", metadata={}),
                Problem(id="c", source="src", lean_code="def c : Nat := 0", metadata={}),
            ]
            calls = []

            def fake_lint(workspace, problem, toolchain, timeout, row_index=0, **_kwargs):
                calls.append(row_index)
                return _mk_result(problem)

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                with patch("runner.executor._lint_problem_sync", side_effect=fake_lint), \
                     patch("runner.executor._resolve_direct_lean", return_value=None):
                    results = await run_batch(workspace, problems, "leanprover/lean4:v4.24.0", workers=2)

            self.assertEqual(3, len(results))
            self.assertEqual({0, 1, 2}, set(calls))

        self.run_async(run())

    def test_run_batch_parallel_emits_results_in_input_order(self):
        async def run():
            problems = [
                Problem(id="a", source="src", lean_code="def a : Nat := 0", metadata={}),
                Problem(id="b", source="src", lean_code="def b : Nat := 0", metadata={}),
                Problem(id="c", source="src", lean_code="def c : Nat := 0", metadata={}),
            ]
            delays = {"a": 0.03, "b": 0.0, "c": 0.01}

            def fake_lint(workspace, problem, toolchain, timeout, row_index=0, **_kwargs):
                time.sleep(delays[problem.id])
                return _mk_result(problem)

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                with patch("runner.executor._lint_problem_sync", side_effect=fake_lint), \
                     patch("runner.executor._resolve_direct_lean", return_value=None):
                    results = await run_batch(workspace, problems, "leanprover/lean4:v4.24.0", workers=3)

            self.assertEqual(["a", "b", "c"], [result.problem_id for result in results])

        self.run_async(run())

    def test_run_batch_parallel_respects_worker_limit(self):
        async def run():
            problems = [
                Problem(id=str(i), source="src", lean_code="def x : Nat := 0", metadata={})
                for i in range(6)
            ]
            current = 0
            max_seen = 0
            state_lock = threading.Lock()

            def fake_lint(workspace, problem, toolchain, timeout, row_index=0, **_kwargs):
                nonlocal current, max_seen
                with state_lock:
                    current += 1
                    max_seen = max(max_seen, current)
                time.sleep(0.03)
                with state_lock:
                    current -= 1
                return _mk_result(problem)

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                with patch("runner.executor._lint_problem_sync", side_effect=fake_lint), \
                     patch("runner.executor._resolve_direct_lean", return_value=None):
                    results = await run_batch(workspace, problems, "leanprover/lean4:v4.24.0", workers=2)
                    with state_lock:
                        self.assertEqual(2, max_seen)

            self.assertEqual(6, len(results))

        self.run_async(run())

    def test_run_batch_collect_results_false_streams_only(self):
        async def run():
            problems = [
                Problem(id="a", source="src", lean_code="def a : Nat := 0", metadata={}),
                Problem(id="b", source="src", lean_code="def b : Nat := 0", metadata={}),
            ]
            seen = []

            def fake_lint(workspace, problem, toolchain, timeout, row_index=0, **_kwargs):
                return _mk_result(problem)

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                with patch("runner.executor._lint_problem_sync", side_effect=fake_lint), \
                     patch("runner.executor._resolve_direct_lean", return_value=None):
                    results = await run_batch(
                        workspace,
                        problems,
                        "leanprover/lean4:v4.24.0",
                        workers=1,
                        on_result=seen.append,
                        collect_results=False,
                    )

            self.assertEqual([], results)
            self.assertEqual(["a", "b"], [result.problem_id for result in seen])

        self.run_async(run())


if __name__ == "__main__":
    unittest.main()
