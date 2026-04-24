"""End-to-end tests that run the linter against the project workspace.

These tests use the repo itself as the workspace (requires `lake build` first).
Skipped if the workspace isn't built.

To run:  python -m pytest runner_tests/test_e2e.py -v
"""
import asyncio
import unittest
from pathlib import Path

from runner.executor import lint_problem, wrap_with_linter
from runner.models import Problem

WORKSPACE = Path(__file__).resolve().parent.parent
BUILT = (WORKSPACE / ".lake" / "build" / "lib").exists()


class WrapWithLinterTests(unittest.TestCase):
    """Unit tests for the sorry-insertion logic."""

    def test_appends_sorry_when_code_ends_with_by(self):
        code = "theorem foo : 1 = 1 := by"
        wrapped = wrap_with_linter(code)
        self.assertIn("sorry", wrapped)
        self.assertLess(wrapped.index("sorry"), wrapped.index("#check_atp_all"))

    def test_appends_sorry_when_code_ends_with_indented_by(self):
        code = "theorem foo (x : Nat) :\n    x = x := by"
        wrapped = wrap_with_linter(code)
        self.assertIn("sorry", wrapped)

    def test_appends_sorry_when_code_ends_with_by_and_trailing_whitespace(self):
        code = "theorem foo : 1 = 1 := by  \n  "
        wrapped = wrap_with_linter(code)
        self.assertIn("sorry", wrapped)

    def test_no_sorry_when_code_has_proof(self):
        code = "theorem foo : 1 = 1 := by rfl"
        wrapped = wrap_with_linter(code)
        self.assertNotIn("sorry", wrapped)

    def test_no_sorry_for_def(self):
        code = "def x : Nat := 42"
        wrapped = wrap_with_linter(code)
        self.assertNotIn("sorry", wrapped)


@unittest.skipUnless(BUILT, "Workspace not built (run `lake build` first)")
class EndToEndTests(unittest.TestCase):
    """Run real problems through the linter and verify output."""

    def run_async(self, coro):
        return asyncio.new_event_loop().run_until_complete(coro)

    def _toolchain(self) -> str:
        return (WORKSPACE / "lean-toolchain").read_text().strip()

    def test_clean_code_no_findings(self):
        problem = Problem(
            id="e2e_safe", source="test",
            lean_code="def addOne (a : Nat) : Nat := a + 1",
            metadata={},
        )
        result = self.run_async(
            lint_problem(WORKSPACE, problem, self._toolchain(), timeout=30)
        )
        self.assertEqual("ok", result.status, result.error_message)
        self.assertEqual(0, len(result.findings))

    def test_unguarded_division_produces_finding(self):
        problem = Problem(
            id="e2e_unguarded", source="test",
            lean_code="def maybeDiv (a b : Nat) : Nat := a / b",
            metadata={},
        )
        result = self.run_async(
            lint_problem(WORKSPACE, problem, self._toolchain(), timeout=30)
        )
        self.assertEqual("findings", result.status, result.error_message)
        categories = [f.category for f in result.findings]
        self.assertTrue(any("Division" in c for c in categories), categories)

    def test_literal_zero_division_proven(self):
        problem = Problem(
            id="e2e_zero", source="test",
            lean_code="def zeroDiv (a : Nat) : Nat := a / 0",
            metadata={},
        )
        result = self.run_async(
            lint_problem(WORKSPACE, problem, self._toolchain(), timeout=30)
        )
        self.assertEqual("findings", result.status, result.error_message)
        div = [f for f in result.findings if "Division" in f.category]
        self.assertTrue(len(div) > 0)
        self.assertEqual("proven", div[0].confidence)

    def test_theorem_ending_with_by_compiles(self):
        problem = Problem(
            id="e2e_by_ending", source="test",
            lean_code="theorem foo (a b : Nat) : a / b = a / b := by",
            metadata={},
        )
        result = self.run_async(
            lint_problem(WORKSPACE, problem, self._toolchain(), timeout=30)
        )
        self.assertNotEqual("compile_error", result.status, result.error_message)


if __name__ == "__main__":
    unittest.main()
