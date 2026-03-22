import io
import json
import tempfile
import unittest
from contextlib import redirect_stderr
from pathlib import Path

from runner.__main__ import _ResultTracker, _load_existing_state


class ResumeStateTests(unittest.TestCase):
    def test_load_existing_state_seeds_counters_and_warns_on_mixed_toolchains(self):
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
                    "provenance": {"lean_toolchain": "lean/v2", "timestamp": "t"},
                    "metadata": {},
                },
            ]
            results_file.write_text(
                "\n".join(json.dumps(row) for row in rows) + "\n",
                encoding="utf-8",
            )

            stderr = io.StringIO()
            with redirect_stderr(stderr):
                state = _load_existing_state(results_file, "lean/v1")

        self.assertEqual({"p1", "p2"}, state.existing_ids)
        self.assertEqual(3, state.processed)
        self.assertEqual(1, state.stats["ok"])
        self.assertEqual(1, state.stats["findings"])
        self.assertEqual(1, state.stats["infra_error"])
        self.assertEqual(1, state.total_findings)
        self.assertEqual(1, state.by_category["Potential Division by Zero"]["total"])
        self.assertEqual(1, state.by_confidence["maybe"])
        self.assertEqual(1, state.by_proved_by["omega"])
        self.assertIn("mixed toolchains", stderr.getvalue())

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

            state = _load_existing_state(results_file, "lean/v2")

        self.assertEqual({"p1"}, state.existing_ids)
        self.assertEqual({"_load_error_line_3"}, state.seen_load_error_ids)
        self.assertEqual(2, state.processed)
        self.assertEqual(0, state.stats["ok"])
        self.assertEqual(1, state.stats["findings"])
        self.assertEqual(1, state.stats["infra_error"])
        self.assertEqual(1, state.total_findings)
        self.assertEqual(1, state.by_confidence["proven"])
        self.assertEqual(1, state.by_proved_by["simp"])

    def test_result_tracker_starts_from_resume_state(self):
        with tempfile.TemporaryDirectory() as td:
            results_fh = io.StringIO()
            logs_dir = Path(td)
            state = _load_existing_state(Path(td) / "missing.jsonl", "lean/v1")
            state.processed = 3
            state.stats["ok"] = 2
            state.stats["infra_error"] = 1
            state.total_findings = 4
            state.by_confidence["maybe"] = 4
            tracker = _ResultTracker(10, results_fh, logs_dir, resume_state=state)

        self.assertEqual(3, tracker.processed)
        self.assertEqual(2, tracker.stats["ok"])
        self.assertEqual(1, tracker.stats["infra_error"])
        self.assertEqual(4, tracker.total_findings)
        self.assertEqual(4, tracker.by_confidence["maybe"])


if __name__ == "__main__":
    unittest.main()
