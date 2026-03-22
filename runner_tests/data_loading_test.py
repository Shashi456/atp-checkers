"""Tests for data loading: field resolver, JSONL, JSON, lean dir, and HF loaders."""
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import MagicMock, patch

from runner.data_loader import (
    resolve_row,
    load_jsonl,
    load_json,
    load_lean_dir,
    load_hf,
    ResolvedRow,
)


# ---------------------------------------------------------------------------
# resolve_row tests
# ---------------------------------------------------------------------------

class TestResolveRow(unittest.TestCase):

    def test_canonical_schema(self):
        row = {"id": "p1", "lean_code": "def x := 1", "extra": "data"}
        r = resolve_row(row)
        self.assertEqual("p1", r.id)
        self.assertEqual("def x := 1", r.lean_code)
        self.assertEqual("lean_code", r.strategy)
        self.assertIn("extra", r.metadata)
        self.assertNotIn("id", r.metadata)
        self.assertNotIn("lean_code", r.metadata)

    def test_deepseek_schema(self):
        row = {
            "name": "thm1",
            "header": "import Mathlib\n",
            "formal_statement": "theorem t := sorry",
        }
        r = resolve_row(row)
        self.assertEqual("thm1", r.id)
        self.assertIn("import Mathlib", r.lean_code)
        self.assertIn("theorem t := sorry", r.lean_code)
        self.assertEqual("header+formal_statement", r.strategy)

    def test_combibench_schema(self):
        row = {
            "theorem_name": "cb1",
            "formal_statement": "import Mathlib\ntheorem cb := sorry",
            "natural_language": "NL text",
        }
        r = resolve_row(row)
        self.assertEqual("cb1", r.id)
        self.assertEqual("formal_statement", r.strategy)
        self.assertEqual("NL text", r.natural_language)

    def test_proofnetsharp_schema(self):
        row = {
            "id": "pns1",
            "lean4_src_header": "import Mathlib\n",
            "lean4_formalization": "theorem t := sorry",
            "nl_statement": "NL",
        }
        r = resolve_row(row)
        self.assertEqual("pns1", r.id)
        self.assertIn("import Mathlib", r.lean_code)
        self.assertIn("theorem t := sorry", r.lean_code)
        self.assertEqual("lean4_src_header+lean4_formalization", r.strategy)
        self.assertEqual("NL", r.natural_language)

    def test_mobench_lean4_code_wins(self):
        """lean4_code takes priority over header+formal_statement."""
        row = {
            "name": "m1",
            "lean4_code": "full code here",
            "header": "h",
            "formal_statement": "fs",
        }
        r = resolve_row(row)
        self.assertEqual("full code here", r.lean_code)
        self.assertEqual("lean4_code", r.strategy)

    def test_justincasher_formal(self):
        row = {"id": "j1", "formal": "theorem t := sorry", "natural": "NL", "name": "thm"}
        r = resolve_row(row)
        self.assertEqual("j1", r.id)  # id beats name
        self.assertEqual("formal", r.strategy)
        self.assertEqual("NL", r.natural_language)

    def test_numina_uuid_becomes_id(self):
        row = {"uuid": "u-123", "formal_statement": "import Mathlib\ntheorem t : True := by trivial"}
        r = resolve_row(row)
        self.assertEqual("u-123", r.id)
        self.assertEqual("formal_statement", r.strategy)

    def test_formalmath_autoformalization_schema(self):
        row = {
            "theorem_names": "algebra_1",
            "autoformalization": "import Mathlib\ntheorem t : True := by trivial",
            "refined_statement": "Prove true.",
        }
        r = resolve_row(row)
        self.assertEqual("algebra_1", r.id)
        self.assertEqual("autoformalization", r.strategy)
        self.assertEqual("Prove true.", r.natural_language)

    def test_header_prepended(self):
        row = {"id": "h1", "formal": "theorem t := sorry"}
        r = resolve_row(row, header="import Mathlib\n")
        self.assertTrue(r.lean_code.startswith("import Mathlib"))
        self.assertIn("theorem t := sorry", r.lean_code)

    def test_fallback_id_from_row_index(self):
        row = {"lean_code": "def x := 1"}
        r = resolve_row(row, row_index=42)
        self.assertEqual("row_42", r.id)

    def test_no_code_raises(self):
        row = {"id": "bad", "unrelated": "data"}
        with self.assertRaises(ValueError) as ctx:
            resolve_row(row)
        self.assertIn("no code field found", str(ctx.exception))

    def test_nl_priority(self):
        """natural_language > nl_statement > informal_prefix > natural."""
        row = {"id": "nl1", "lean_code": "x", "nl_statement": "A", "informal_prefix": "B"}
        r = resolve_row(row)
        self.assertEqual("A", r.natural_language)

    def test_empty_code_field_falls_through(self):
        """Empty string code fields are skipped."""
        row = {"id": "e1", "lean_code": "", "formal_statement": "theorem t := sorry"}
        r = resolve_row(row)
        self.assertEqual("formal_statement", r.strategy)

    def test_id_priority(self):
        """id > name > theorem_name > problem_id."""
        row = {"name": "n1", "theorem_name": "tn1", "lean_code": "x"}
        r = resolve_row(row)
        self.assertEqual("n1", r.id)


# ---------------------------------------------------------------------------
# load_jsonl tests
# ---------------------------------------------------------------------------

class TestLoadJsonl(unittest.TestCase):

    def test_canonical_schema(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "test.jsonl"
            p.write_text(
                '{"id":"ok_1","lean_code":"def a := 1","natural_language":"x"}\n'
                '{"id":"ok_2","lean_code":"theorem t := trivial"}\n',
                encoding="utf-8",
            )
            problems, errors = load_jsonl(p)

        self.assertEqual(2, len(problems))
        self.assertEqual("ok_1", problems[0].id)
        self.assertEqual("ok_2", problems[1].id)
        self.assertEqual(0, len(errors))

    def test_deepseek_schema_auto_resolved(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "ds.jsonl"
            p.write_text(
                '{"name":"thm1","header":"import Mathlib\\n","formal_statement":"theorem t := sorry"}\n',
                encoding="utf-8",
            )
            problems, errors = load_jsonl(p)

        self.assertEqual(1, len(problems))
        self.assertEqual("thm1", problems[0].id)
        self.assertIn("import Mathlib", problems[0].lean_code)
        self.assertIn("theorem t := sorry", problems[0].lean_code)
        self.assertEqual(0, len(errors))

    def test_header_param_prepended(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "headerless.jsonl"
            p.write_text(
                '{"id":"h1","formal":"theorem t := sorry"}\n',
                encoding="utf-8",
            )
            problems, errors = load_jsonl(p, header="import Mathlib\n")

        self.assertEqual(1, len(problems))
        self.assertTrue(problems[0].lean_code.startswith("import Mathlib"))

    def test_error_collection(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "bad.jsonl"
            p.write_text(
                '{not json}\n'
                '{"id":"no_code","unrelated":"x"}\n'
                '{"id":"ok","lean_code":"def x := 1"}\n',
                encoding="utf-8",
            )
            problems, errors = load_jsonl(p)

        self.assertEqual(1, len(problems))
        self.assertEqual(2, len(errors))

    def test_backwards_compat_with_old_test(self):
        """Replicate the original test_loader.py test to confirm backwards compat."""
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

        # The resolver now accepts rows without "id" (fallback to row index),
        # so {"lean_code":"def z"} succeeds as row_4.
        # bad_code_type has lean_code=123 (non-string) → resolver skips it → no code → error.
        self.assertEqual(3, len(problems))  # ok_1, row_4, ok_2
        self.assertEqual("ok_1", problems[0].id)
        self.assertEqual("row_4", problems[1].id)
        self.assertEqual("ok_2", problems[2].id)
        self.assertEqual("mixed", problems[0].source)
        self.assertEqual("x", problems[0].metadata.get("natural_language"))

        self.assertEqual(3, len(errors))  # missing_code, bad_code_type, invalid JSON


# ---------------------------------------------------------------------------
# load_json tests
# ---------------------------------------------------------------------------

class TestLoadJson(unittest.TestCase):

    def test_json_array(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "test.json"
            data = [
                {"id": "p1", "lean_code": "def a := 1"},
                {"id": "p2", "lean_code": "def b := 2"},
            ]
            p.write_text(json.dumps(data), encoding="utf-8")
            problems, errors = load_json(p)

        self.assertEqual(2, len(problems))
        self.assertEqual("p1", problems[0].id)
        self.assertEqual(0, len(errors))

    def test_not_array_is_error(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "bad.json"
            p.write_text('{"id": "single"}', encoding="utf-8")
            problems, errors = load_json(p)

        self.assertEqual(0, len(problems))
        self.assertEqual(1, len(errors))
        self.assertIn("Expected JSON array", errors[0].error)

    def test_mixed_schemas_in_array(self):
        with tempfile.TemporaryDirectory() as td:
            p = Path(td) / "mixed.json"
            data = [
                {"name": "thm1", "header": "import M\n", "formal_statement": "thm t := sorry"},
                {"id": "p2", "lean_code": "def b := 2"},
            ]
            p.write_text(json.dumps(data), encoding="utf-8")
            problems, errors = load_json(p)

        self.assertEqual(2, len(problems))
        self.assertEqual("thm1", problems[0].id)
        self.assertEqual("p2", problems[1].id)


# ---------------------------------------------------------------------------
# load_lean_dir tests
# ---------------------------------------------------------------------------

class TestLoadLeanDir(unittest.TestCase):

    def test_loads_lean_files(self):
        with tempfile.TemporaryDirectory() as td:
            d = Path(td) / "lean_problems"
            d.mkdir()
            (d / "problem_1.lean").write_text("theorem t1 := sorry", encoding="utf-8")
            (d / "problem_2.lean").write_text("theorem t2 := sorry", encoding="utf-8")
            (d / "not_lean.txt").write_text("ignore me", encoding="utf-8")

            problems, errors = load_lean_dir(d)

        self.assertEqual(2, len(problems))
        ids = {p.id for p in problems}
        self.assertEqual({"problem_1", "problem_2"}, ids)
        self.assertEqual(0, len(errors))

    def test_empty_dir_is_error(self):
        with tempfile.TemporaryDirectory() as td:
            d = Path(td) / "empty"
            d.mkdir()
            problems, errors = load_lean_dir(d)

        self.assertEqual(0, len(problems))
        self.assertEqual(1, len(errors))
        self.assertIn("No .lean files", errors[0].error)

    def test_header_prepended_to_lean_files(self):
        with tempfile.TemporaryDirectory() as td:
            d = Path(td) / "leans"
            d.mkdir()
            (d / "p.lean").write_text("theorem t := sorry", encoding="utf-8")

            problems, errors = load_lean_dir(d, header="import Mathlib\n")

        self.assertEqual(1, len(problems))
        self.assertTrue(problems[0].lean_code.startswith("import Mathlib"))

    def test_empty_file_skipped(self):
        with tempfile.TemporaryDirectory() as td:
            d = Path(td) / "leans"
            d.mkdir()
            (d / "empty.lean").write_text("", encoding="utf-8")
            (d / "ok.lean").write_text("def x := 1", encoding="utf-8")

            problems, errors = load_lean_dir(d)

        self.assertEqual(1, len(problems))
        self.assertEqual(1, len(errors))
        self.assertIn("Empty file", errors[0].error)


# ---------------------------------------------------------------------------
# load_hf tests (mocked)
# ---------------------------------------------------------------------------

class TestLoadHf(unittest.TestCase):

    def test_load_hf_with_mock(self):
        """Test HF loading with mocked datasets library."""
        mock_ds_module = MagicMock()
        mock_ds_module.get_dataset_split_names.return_value = ["train", "test"]
        mock_ds_module.load_dataset.return_value = iter([
            {"name": "thm1", "header": "import M\n", "formal_statement": "theorem t1 := sorry"},
            {"name": "thm2", "header": "import M\n", "formal_statement": "theorem t2 := sorry"},
        ])

        with patch.dict("sys.modules", {"datasets": mock_ds_module}):
            problems, errors = load_hf("test-org/test-dataset", split="test")

        self.assertEqual(2, len(problems))
        self.assertEqual("thm1", problems[0].id)
        self.assertEqual("thm2", problems[1].id)
        self.assertIn("import M", problems[0].lean_code)
        mock_ds_module.load_dataset.assert_called_once_with(
            "test-org/test-dataset",
            split="test",
            streaming=True,
            trust_remote_code=True,
        )

    def test_load_hf_auto_selects_test_split_via_metadata(self):
        mock_ds_module = MagicMock()
        mock_ds_module.get_dataset_split_names.return_value = ["validation", "test"]
        mock_ds_module.load_dataset.return_value = iter([
            {"name": "thm1", "header": "import M\n", "formal_statement": "theorem t1 := sorry"},
        ])

        with patch.dict("sys.modules", {"datasets": mock_ds_module}):
            problems, errors = load_hf("test-org/test-dataset")

        self.assertEqual(1, len(problems))
        self.assertEqual(0, len(errors))
        mock_ds_module.get_dataset_split_names.assert_called_once_with(
            "test-org/test-dataset",
            trust_remote_code=True,
        )
        mock_ds_module.load_dataset.assert_called_once_with(
            "test-org/test-dataset",
            split="test",
            streaming=True,
            trust_remote_code=True,
        )


if __name__ == "__main__":
    unittest.main()
