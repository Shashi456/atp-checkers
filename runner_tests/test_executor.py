import asyncio
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from runner.executor import (
    has_done_sentinel,
    lint_problem,
    parse_lint_output,
    run_batch,
    wrap_with_linter,
)
from runner.models import LintResult, Problem, Provenance


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


class FakeProc:
    def __init__(self, stdout: str, stderr: str = "", returncode: int = 0):
        self._stdout = stdout.encode("utf-8")
        self._stderr = stderr.encode("utf-8")
        self.returncode = returncode
        self.pid = 4242

    async def communicate(self):
        return self._stdout, self._stderr

    async def wait(self):
        return self.returncode


class SlowProc(FakeProc):
    def __init__(self):
        super().__init__(stdout="", stderr="", returncode=0)
        self._gate = asyncio.Event()

    async def communicate(self):
        await self._gate.wait()
        return b"", b""


class ExecutorParsingTests(unittest.TestCase):
    def test_wrap_with_linter(self):
        wrapped = wrap_with_linter("def x : Nat := 1")
        self.assertIn("import AtpLinter", wrapped)
        self.assertIn("#check_atp_all", wrapped)
        self.assertIn("def x : Nat := 1", wrapped)

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
        done, meta = has_done_sentinel('x\nATP_DONE:{"declarations":2,"findings":3}\n')
        self.assertTrue(done)
        self.assertEqual(2, meta["declarations"])
        self.assertEqual(3, meta["findings"])


class ExecutorAsyncTests(unittest.TestCase):
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

            async def fake_create(*_args, **_kwargs):
                return FakeProc(stdout=stdout, returncode=0)

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                problem = Problem(id="p1", source="s", lean_code="def d : Nat := 1", metadata={})
                with patch("runner.executor.asyncio.create_subprocess_exec", side_effect=fake_create):
                    result = await lint_problem(workspace, problem, "leanprover/lean4:v4.24.0", timeout=1, row_index=7)

            self.assertEqual("findings", result.status)
            self.assertEqual(1, len(result.findings))
            self.assertEqual("Potential Division by Zero", result.findings[0].category)

        self.run_async(run())

    def test_lint_problem_status_ok(self):
        async def run():
            async def fake_create(*_args, **_kwargs):
                return FakeProc(stdout='ATP_DONE:{"declarations":1,"findings":0}', returncode=0)

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                problem = Problem(id="p2", source="s", lean_code="def ok : Nat := 1", metadata={})
                with patch("runner.executor.asyncio.create_subprocess_exec", side_effect=fake_create):
                    result = await lint_problem(workspace, problem, "leanprover/lean4:v4.24.0", timeout=1)

            self.assertEqual("ok", result.status)
            self.assertEqual(0, len(result.findings))

        self.run_async(run())

    def test_lint_problem_status_compile_error(self):
        async def run():
            async def fake_create(*_args, **_kwargs):
                return FakeProc(stdout="", stderr="compile failed", returncode=1)

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                problem = Problem(id="p3", source="s", lean_code="def bad := ", metadata={})
                with patch("runner.executor.asyncio.create_subprocess_exec", side_effect=fake_create):
                    result = await lint_problem(workspace, problem, "leanprover/lean4:v4.24.0", timeout=1)

            self.assertEqual("compile_error", result.status)
            self.assertIn("compile failed", result.error_message)

        self.run_async(run())

    def test_lint_problem_status_infra_error_without_done(self):
        async def run():
            async def fake_create(*_args, **_kwargs):
                return FakeProc(stdout="ATP_LINT:{}", returncode=0)

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                problem = Problem(id="p4", source="s", lean_code="def x : Nat := 0", metadata={})
                with patch("runner.executor.asyncio.create_subprocess_exec", side_effect=fake_create):
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

            async def fake_create(*_args, **_kwargs):
                return FakeProc(stdout=stdout, returncode=0)

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                problem = Problem(id="p5", source="s", lean_code="def x : Nat := 0", metadata={})
                with patch("runner.executor.asyncio.create_subprocess_exec", side_effect=fake_create):
                    result = await lint_problem(workspace, problem, "leanprover/lean4:v4.24.0", timeout=1)

            self.assertEqual("infra_error", result.status)
            self.assertIn("Output may be truncated", result.error_message)
            self.assertEqual(1, len(result.findings))

        self.run_async(run())

    def test_lint_problem_status_timeout(self):
        async def run():
            async def fake_create(*_args, **_kwargs):
                return SlowProc()

            async def fast_sleep(_seconds):
                return None

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                problem = Problem(id="p6", source="s", lean_code="def x : Nat := 0", metadata={})
                with patch("runner.executor.asyncio.create_subprocess_exec", side_effect=fake_create), \
                     patch("runner.executor.os.getpgid", return_value=4242), \
                     patch("runner.executor.os.killpg"), \
                     patch("runner.executor.asyncio.sleep", new=fast_sleep):
                    result = await lint_problem(workspace, problem, "leanprover/lean4:v4.24.0", timeout=0.01)

            self.assertEqual("timeout", result.status)
            self.assertIn("Exceeded", result.error_message)

        self.run_async(run())

    def test_run_batch_sequential_passes_row_index(self):
        async def run():
            problems = [
                Problem(id="a", source="src", lean_code="def a : Nat := 0", metadata={}),
                Problem(id="b", source="src", lean_code="def b : Nat := 0", metadata={}),
                Problem(id="c", source="src", lean_code="def c : Nat := 0", metadata={}),
            ]
            calls = []

            async def fake_lint(workspace, problem, toolchain, timeout, row_index=0):
                calls.append(row_index)
                return _mk_result(problem)

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                with patch("runner.executor.lint_problem", side_effect=fake_lint):
                    results = await run_batch(workspace, problems, "leanprover/lean4:v4.24.0", workers=1)

            self.assertEqual(3, len(results))
            self.assertEqual([0, 1, 2], calls)

        self.run_async(run())

    def test_run_batch_parallel_passes_row_index(self):
        async def run():
            problems = [
                Problem(id="a", source="src", lean_code="def a : Nat := 0", metadata={}),
                Problem(id="b", source="src", lean_code="def b : Nat := 0", metadata={}),
                Problem(id="c", source="src", lean_code="def c : Nat := 0", metadata={}),
            ]
            calls = []

            async def fake_lint(workspace, problem, toolchain, timeout, row_index=0):
                calls.append(row_index)
                return _mk_result(problem)

            with tempfile.TemporaryDirectory() as td:
                workspace = Path(td)
                with patch("runner.executor.lint_problem", side_effect=fake_lint):
                    results = await run_batch(workspace, problems, "leanprover/lean4:v4.24.0", workers=2)

            self.assertEqual(3, len(results))
            self.assertEqual({0, 1, 2}, set(calls))

        self.run_async(run())


if __name__ == "__main__":
    unittest.main()
