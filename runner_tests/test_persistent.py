import asyncio
import unittest
from datetime import datetime, timezone
from pathlib import Path
from unittest.mock import patch

from runner.models import LintResult, Problem, Provenance
from runner.persistent import LeanRepl, _Pool, run_batch


class _FakeWorker:
    def __init__(self, *, started: bool = False, pending: int = 0, start_error: str | None = None):
        self._started = started
        self.pending = pending
        self._start_error_message = start_error
        self.start_calls = 0
        self.has_failed_start = False

    @property
    def is_started(self) -> bool:
        return self._started

    async def start(self) -> None:
        self.start_calls += 1
        if self._start_error_message is not None:
            self.has_failed_start = True
            raise RuntimeError(self._start_error_message)
        self._started = True


class PersistentPoolTests(unittest.TestCase):
    def run_async(self, coro):
        loop = asyncio.new_event_loop()
        try:
            asyncio.set_event_loop(loop)
            return loop.run_until_complete(coro)
        finally:
            asyncio.set_event_loop(None)
            loop.close()

    def test_pick_falls_back_to_started_worker_when_lazy_start_fails(self):
        async def run():
            pool = _Pool(Path("."), "lean/v1", timeout=30, workers=2)
            started = _FakeWorker(started=True, pending=pool._SPAWN_THRESHOLD)
            failing = _FakeWorker(start_error="boom")
            pool._workers = [started, failing]

            first = await pool._pick(("import Mathlib",))
            second = await pool._pick(("open scoped BigOperators",))

            self.assertIs(first, started)
            self.assertIs(second, started)
            self.assertEqual(1, failing.start_calls)
            self.assertIs(pool._key_owner[("import Mathlib",)], started)
            self.assertIs(pool._key_owner[("open scoped BigOperators",)], started)

        self.run_async(run())

    def test_repl_run_problem_keeps_findings_when_compile_error_has_done(self):
        async def run():
            repl = LeanRepl(Path("."), "lean/v1")
            problem = Problem(id="p1", source="src", lean_code="def x : Nat := 0", metadata={})

            async def fake_ensure_started():
                return None

            async def fake_get_or_create_env(_preamble, _timeout):
                return 7, None, None, None

            async def fake_send_cmd(_cmd, timeout=300, env=None):
                return {
                    "env": 8,
                    "messages": [
                        {"severity": "error", "data": "unknown identifier", "pos": {"line": 1, "column": 1}},
                        {
                            "severity": "info",
                            "data": 'ATP_LINT:{"category":"Potential Division by Zero","severity":"WARNING","declaration":"x","message":"m","confidence":"maybe","provedBy":null}',
                        },
                        {
                            "severity": "info",
                            "data": 'ATP_DONE:{"declarations":1,"findings":1}',
                        },
                    ],
                }

            repl._ensure_started = fake_ensure_started  # type: ignore[method-assign]
            repl._get_or_create_env = fake_get_or_create_env  # type: ignore[method-assign]
            repl._send_cmd = fake_send_cmd  # type: ignore[method-assign]

            result = await repl.run_problem(problem, timeout=30)

            self.assertEqual("findings", result.status)
            self.assertTrue(result.compile_error)
            self.assertEqual(1, len(result.findings))
            self.assertIn("unknown identifier", result.compile_error_message)
            self.assertIsNone(result.error_message)

        self.run_async(run())

    def test_pool_run_problem_returns_infra_error_when_pick_raises(self):
        async def run():
            pool = _Pool(Path("."), "lean/v1", timeout=30, workers=4)
            problem = Problem(id="p1", source="src", lean_code="def x : Nat := 0", metadata={})

            async def fake_pick(_key):
                raise RuntimeError("boom")

            pool._pick = fake_pick  # type: ignore[method-assign]

            result = await pool.run_problem(problem)

            self.assertEqual("infra_error", result.status)
            self.assertIn("Worker crashed: boom", result.error_message)

        self.run_async(run())

    def test_run_batch_parallel_returns_results_when_pick_raises(self):
        async def run():
            problems = [
                Problem(id="a", source="src", lean_code="def a : Nat := 0", metadata={}),
                Problem(id="b", source="src", lean_code="def b : Nat := 0", metadata={}),
            ]

            async def fake_start(self):
                return None

            async def fake_stop(self):
                return None

            async def fake_pick(self, _key):
                raise RuntimeError("boom")

            with patch.object(_Pool, "start", new=fake_start), \
                 patch.object(_Pool, "stop", new=fake_stop), \
                 patch.object(_Pool, "_pick", new=fake_pick):
                results = await run_batch(Path("."), problems, "lean/v1", workers=4)

            self.assertEqual(2, len(results))
            self.assertTrue(all(result.status == "infra_error" for result in results))
            self.assertTrue(all("Worker crashed: boom" in (result.error_message or "") for result in results))

        self.run_async(run())

    def test_run_batch_falls_back_to_subprocess_when_start_fails(self):
        async def run():
            problems = [Problem(id="a", source="src", lean_code="def a : Nat := 0", metadata={})]

            async def fake_start(self):
                raise RuntimeError("no repl")

            async def fake_subprocess(*_args, **_kwargs):
                return [
                    LintResult(
                        problem_id="a",
                        source="src",
                        status="ok",
                        findings=[],
                        error_message=None,
                        duration_ms=1,
                        provenance=Provenance(
                            lean_toolchain="lean/v1",
                            timestamp=datetime.now(timezone.utc).isoformat(),
                        ),
                    )
                ]

            with patch.object(_Pool, "start", new=fake_start), \
                 patch("runner.persistent.run_batch_subprocess", new=fake_subprocess):
                results = await run_batch(Path("."), problems, "lean/v1", workers=2)

            self.assertEqual(1, len(results))
            self.assertEqual("ok", results[0].status)

        self.run_async(run())

    def test_repl_recycle_reason_uses_problem_threshold_before_rss(self):
        async def run():
            repl = LeanRepl(Path("."), "lean/v1", max_problem_runs=3, max_tree_rss_mb=1.0)
            repl.problem_runs = 3
            reason = await repl.recycle_reason()
            self.assertIn("problem_runs=3>=3", reason)

        self.run_async(run())


if __name__ == "__main__":
    unittest.main()
