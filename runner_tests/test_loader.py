import tempfile
import unittest
from pathlib import Path

from runner.loader import load_jsonl


class LoaderTests(unittest.TestCase):
    def test_load_jsonl_parses_valid_and_collects_errors(self):
        with tempfile.TemporaryDirectory() as td:
            dataset = Path(td) / "mixed.jsonl"
            dataset.write_text(
                "\n".join([
                    '{"id":"ok_1","lean_code":"def a : Nat := 1","natural_language":"x"}',
                    '{"id":"missing_code"}',
                    '{"id":"bad_code_type","lean_code":123}',
                    '{"lean_code":"def z : Nat := 0"}',
                    '{"id":"ok_2","lean_code":"theorem t : True := trivial"}',
                    '{not json}',
                ]),
                encoding="utf-8",
            )

            problems, errors = load_jsonl(dataset)

        self.assertEqual(2, len(problems))
        self.assertEqual("ok_1", problems[0].id)
        self.assertEqual("ok_2", problems[1].id)
        self.assertEqual("mixed", problems[0].source)
        self.assertEqual("x", problems[0].metadata.get("natural_language"))

        self.assertEqual(4, len(errors))
        messages = [e.error for e in errors]
        self.assertTrue(any("Missing 'lean_code' field" in m for m in messages))
        self.assertTrue(any("'lean_code' must be string" in m for m in messages))
        self.assertTrue(any("Missing 'id' field" in m for m in messages))
        self.assertTrue(any("Invalid JSON" in m for m in messages))


if __name__ == "__main__":
    unittest.main()
