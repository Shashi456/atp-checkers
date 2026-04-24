import io
import json
import tempfile
import unittest
from contextlib import redirect_stderr
from pathlib import Path

from runner.__main__ import (
    _enforce_toolchain_consistency,
    _load_existing_state,
    _ResultTracker,
    _scan_existing_results,
)


class ResumeStateTests(unittest.TestCase):
    def test_scan_and_load_seeds_counters(self):
        with tempfile.TemporaryDirectory() as td:
            results_file = Path(td) / "results.jsonl"
            rows = [
                {
                    "problem_id": "p1",
                    "source": "src",
                    "status": "ok",
                    "findings": [],
                    "error_message": None,
                    "duration_ms": 1,
                    "provenance": {"lean_toolchain": "lean/v1", "timestamp": "t"},
                    "metadata": {},
                },
                {
                    "problem_id": "_load_error_line_2",
                    "source": "dataset",
                    "status": "infra_error",
                    "findings": [],
                    "error_message": "bad row",
                    "duration_ms": 0,
                    "provenance": {"lean_toolchain": "lean/v1", "timestamp": "t"},
                    "metadata": {},
                },
                {
                    "problem_id": "p2",
                    "source": "src",
                    "status": "findings",
                    "compile_error": True,
                    "compile_error_message": "bad syntax",
                    "findings": [
                        {
                            "category": "Potential Division by Zero",
                            "severity": "WARNING",
                            "declaration": "d",
                            "message": "m",
                            "suggestion": None,
                            "confidence": "maybe",
                            "provedBy": "omega",
                        }
                    ],
                    "error_message": None,
                    "duration_ms": 2,
                    "provenance": {"lean_toolchain": "lean/v1", "timestamp": "t"},
                    "metadata": {},
                },
            ]
            results_file.write_text(
                "\n".join(json.dumps(row) for row in rows) + "\n",
                encoding="utf-8",
            )

            latest_by_key, seen_toolchains = _scan_existing_results(results_file)
            state = _load_existing_state(results_file, latest_by_key)

        self.assertEqual({"lean/v1"}, seen_toolchains)
        self.assertEqual({"p1", "p2"}, state.existing_ids)
        self.assertEqual(3, state.processed)
        self.assertEqual(1, state.stats["ok"])
        self.assertEqual(1, state.stats["findings"])
        self.assertEqual(1, state.stats["infra_error"])
        self.assertEqual(1, state.compile_errors)
        self.assertEqual(1, state.compile_errors_with_findings)
        self.assertEqual(1, state.total_findings)
        self.assertEqual(1, state.by_category["Potential Division by Zero"]["total"])
        self.assertEqual(1, state.by_confidence["maybe"])
        self.assertEqual(1, state.by_proved_by["omega"])

    def test_enforce_toolchain_consistency_refuses_mismatch_by_default(self):
        stderr = io.StringIO()
        with redirect_stderr(stderr), self.assertRaises(SystemExit) as cm:
            _enforce_toolchain_consistency(
                "lean/v2", {"lean/v1"}, allow_mismatch=False
            )
        self.assertEqual(cm.exception.code, 1)
        self.assertIn("Toolchain mismatch", stderr.getvalue())

    def test_enforce_toolchain_consistency_refuses_mixed_existing(self):
        stderr = io.StringIO()
        with redirect_stderr(stderr), self.assertRaises(SystemExit):
            _enforce_toolchain_consistency(
                "lean/v1", {"lean/v1", "lean/v2"}, allow_mismatch=False
            )
        self.assertIn("mixed toolchains", stderr.getvalue())

    def test_enforce_toolchain_consistency_allows_with_flag(self):
        stderr = io.StringIO()
        with redirect_stderr(stderr):
            _enforce_toolchain_consistency(
                "lean/v2", {"lean/v1"}, allow_mismatch=True
            )
        self.assertIn("Warning", stderr.getvalue())
        self.assertIn("Toolchain mismatch", stderr.getvalue())

    def test_enforce_toolchain_consistency_passes_when_match(self):
        # No exception, no output
        stderr = io.StringIO()
        with redirect_stderr(stderr):
            _enforce_toolchain_consistency(
                "lean/v1", {"lean/v1"}, allow_mismatch=False
            )
        self.assertEqual("", stderr.getvalue())

    def test_enforce_toolchain_consistency_passes_when_empty(self):
        # Empty seen set (no prior results) should never fire.
        _enforce_toolchain_consistency("lean/v1", set(), allow_mismatch=False)

    def test_load_existing_state_dedupes_latest_row_per_problem(self):
        with tempfile.TemporaryDirectory() as td:
            results_file = Path(td) / "results.jsonl"
            rows = [
                {
                    "problem_id": "p1",
                    "source": "src",
                    "status": "ok",
                    "findings": [],
                    "error_message": None,
                    "duration_ms": 1,
                    "provenance": {"lean_toolchain": "lean/v1", "timestamp": "t1"},
                    "metadata": {},
                },
                {
                    "problem_id": "p1",
                    "source": "src",
                    "status": "findings",
                    "compile_error": True,
                    "compile_error_message": "bad syntax",
                    "findings": [
                        {
                            "category": "Unused Quantified Variable",
                            "severity": "WARNING",
                            "declaration": "d",
                            "message": "m",
                            "suggestion": None,
                            "confidence": "proven",
                            "provedBy": "simp",
                        }
                    ],
                    "error_message": None,
                    "duration_ms": 2,
                    "provenance": {"lean_toolchain": "lean/v2", "timestamp": "t2"},
                    "metadata": {},
                },
                {
                    "problem_id": "_load_error_line_3",
                    "source": "dataset",
                    "status": "infra_error",
                    "findings": [],
                    "error_message": "bad row",
                    "duration_ms": 0,
                    "provenance": {"lean_toolchain": "lean/v2", "timestamp": "t2"},
                    "metadata": {},
                },
                {
                    "problem_id": "_load_error_line_3",
                    "source": "dataset",
                    "status": "infra_error",
                    "findings": [],
                    "error_message": "bad row updated",
                    "duration_ms": 0,
                    "provenance": {"lean_toolchain": "lean/v2", "timestamp": "t3"},
                    "metadata": {},
                },
            ]
            results_file.write_text(
                "\n".join(json.dumps(row) for row in rows) + "\n",
                encoding="utf-8",
            )

            latest_by_key, _seen = _scan_existing_results(results_file)
            state = _load_existing_state(results_file, latest_by_key)

        self.assertEqual({"p1"}, state.existing_ids)
        self.assertEqual({"_load_error_line_3"}, state.seen_load_error_ids)
        self.assertEqual(2, state.processed)
        self.assertEqual(0, state.stats["ok"])
        self.assertEqual(1, state.stats["findings"])
        self.assertEqual(1, state.stats["infra_error"])
        self.assertEqual(1, state.compile_errors)
        self.assertEqual(1, state.compile_errors_with_findings)
        self.assertEqual(1, state.total_findings)
        self.assertEqual(1, state.by_confidence["proven"])
        self.assertEqual(1, state.by_proved_by["simp"])

    def test_result_tracker_starts_from_resume_state(self):
        with tempfile.TemporaryDirectory() as td:
            results_fh = io.StringIO()
            logs_dir = Path(td)
            state = _load_existing_state(Path(td) / "missing.jsonl", {})
            state.processed = 3
            state.stats["ok"] = 2
            state.stats["infra_error"] = 1
            state.compile_errors = 2
            state.compile_errors_with_findings = 1
            state.total_findings = 4
            state.by_confidence["maybe"] = 4
            tracker = _ResultTracker(10, results_fh, logs_dir, resume_state=state)

        self.assertEqual(3, tracker.processed)
        self.assertEqual(2, tracker.stats["ok"])
        self.assertEqual(1, tracker.stats["infra_error"])
        self.assertEqual(2, tracker.compile_errors)
        self.assertEqual(1, tracker.compile_errors_with_findings)
        self.assertEqual(4, tracker.total_findings)
        self.assertEqual(4, tracker.by_confidence["maybe"])


if __name__ == "__main__":
    unittest.main()
