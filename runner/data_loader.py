"""Dataset loaders for the ATP checkers runner.

Supports multiple input formats and schema auto-detection:
- JSONL files (canonical or benchmark-specific schemas)
- JSON array files
- Directories of .lean files
- HuggingFace datasets (requires `pip install datasets`)
"""
from __future__ import annotations

import json
import logging
from collections.abc import Iterator
from dataclasses import dataclass
from pathlib import Path
from typing import cast

from .models import ParseError, Problem

log = logging.getLogger(__name__)

DatasetItem = Problem | ParseError


# ---------------------------------------------------------------------------
# Field resolver
# ---------------------------------------------------------------------------

@dataclass
class ResolvedRow:
    """Result of resolving a raw dict into canonical fields."""
    id: str
    lean_code: str
    natural_language: str | None
    strategy: str          # human-readable label of matched code strategy
    metadata: dict         # all unconsumed fields


# Ordered candidate lists
_ID_KEYS = ("id", "name", "theorem_name", "problem_id", "uuid", "theorem_names")

# Each entry: tuple of field names.
#   len == 1  →  use that field as-is
#   len == 2  →  concatenate field[0] + "\n" + field[1]
_CODE_STRATEGIES: list[tuple[str, ...]] = [
    ("lean_code",),
    ("lean4_code",),
    ("header", "formal_statement"),
    ("lean4_src_header", "lean4_formalization"),
    ("autoformalization",),
    ("formal_statement",),
    ("formal",),
]

_NL_KEYS = (
    "natural_language",
    "nl_statement",
    "informal_prefix",
    "natural",
    "refined_statement",
    "problem",
)


def resolve_row(
    row: dict,
    row_index: int = 0,
    header: str | None = None,
) -> ResolvedRow:
    """Resolve a raw dict into canonical Problem fields.

    Args:
        row: Raw dict from any data source.
        row_index: Fallback ID if no ID field is found.
        header: Optional Lean header to prepend to resolved code.

    Returns:
        ResolvedRow with id, lean_code, natural_language, strategy, metadata.

    Raises:
        ValueError: If no recognizable code field is found.
    """
    consumed: set[str] = set()

    # --- ID ---
    problem_id = None
    for key in _ID_KEYS:
        if key in row and row[key] is not None:
            problem_id = str(row[key])
            consumed.add(key)
            break
    if problem_id is None:
        problem_id = f"row_{row_index}"

    # --- Code ---
    lean_code = None
    strategy_label = None
    for fields in _CODE_STRATEGIES:
        if len(fields) == 1:
            key = fields[0]
            if key in row and isinstance(row[key], str) and row[key].strip():
                lean_code = row[key]
                strategy_label = key
                consumed.add(key)
                break
        else:
            k1, k2 = fields
            if (k1 in row and isinstance(row[k1], str)
                    and k2 in row and isinstance(row[k2], str)
                    and row[k2].strip()):
                lean_code = row[k1].rstrip() + "\n" + row[k2]
                strategy_label = f"{k1}+{k2}"
                consumed.add(k1)
                consumed.add(k2)
                break

    if lean_code is None:
        raise ValueError(
            f"Row {problem_id}: no code field found. "
            f"Available keys: {list(row.keys())}"
        )
    if strategy_label is None:
        raise ValueError(f"Row {problem_id}: matched code without a strategy label")

    # --- Prepend header ---
    if header:
        lean_code = header.rstrip() + "\n" + lean_code

    # --- NL ---
    natural_language = None
    for key in _NL_KEYS:
        if key in row and isinstance(row[key], str) and row[key].strip():
            natural_language = row[key]
            consumed.add(key)
            break

    # --- Metadata (unconsumed keys) ---
    metadata = {k: v for k, v in row.items() if k not in consumed}

    return ResolvedRow(
        id=problem_id,
        lean_code=lean_code,
        natural_language=natural_language,
        strategy=cast(str, strategy_label),
        metadata=metadata,
    )


def _resolved_to_problem(resolved: ResolvedRow, source: str) -> Problem:
    """Convert a ResolvedRow into a Problem."""
    meta = dict(resolved.metadata)
    if resolved.natural_language:
        meta["natural_language"] = resolved.natural_language
    return Problem(
        id=resolved.id,
        source=source,
        lean_code=resolved.lean_code,
        metadata=meta,
    )


def _collect_items(items: Iterator[DatasetItem]) -> tuple[list[Problem], list[ParseError]]:
    problems: list[Problem] = []
    errors: list[ParseError] = []
    for item in items:
        if isinstance(item, Problem):
            problems.append(item)
        else:
            errors.append(item)
    return problems, errors


# ---------------------------------------------------------------------------
# JSONL loader
# ---------------------------------------------------------------------------

def load_jsonl(
    path: Path,
    source: str | None = None,
    on_error: str = "skip",
    header: str | None = None,
) -> tuple[list[Problem], list[ParseError]]:
    """Load problems from a JSONL file.

    Supports any schema recognized by the field resolver.

    Args:
        path: Path to JSONL file.
        source: Dataset source name (defaults to filename stem).
        on_error: "skip", "raise", or "include".
        header: Optional Lean header prepended to every problem.

    Returns:
        (problems, errors)
    """
    return _collect_items(iter_jsonl(path, source=source, on_error=on_error, header=header))


def iter_jsonl(
    path: Path,
    source: str | None = None,
    on_error: str = "skip",
    header: str | None = None,
) -> Iterator[DatasetItem]:
    """Iterate over a JSONL dataset, yielding Problem or ParseError in file order."""
    if source is None:
        source = path.stem

    first_strategy = None

    with open(path, encoding="utf-8") as f:
        for line_num, line in enumerate(f, start=1):
            line = line.strip()
            if not line:
                continue

            try:
                data = json.loads(line)
            except json.JSONDecodeError as e:
                err = ParseError(line_num, f"Invalid JSON: {e}", line[:200])
                if on_error == "raise":
                    raise ValueError(f"{path}:{line_num}: {err.error}")
                yield err
                continue

            try:
                resolved = resolve_row(data, row_index=line_num, header=header)
            except ValueError as e:
                err = ParseError(line_num, str(e), line[:200])
                if on_error == "raise":
                    raise ValueError(f"{path}:{line_num}: {err.error}")
                yield err
                continue

            if first_strategy is None:
                first_strategy = resolved.strategy
                log.info("Detected schema: %s (from %s)", resolved.strategy, path.name)

            yield _resolved_to_problem(resolved, source)


def count_jsonl_entries(path: Path) -> int:
    """Count non-empty JSONL lines for progress reporting."""
    with open(path, encoding="utf-8") as f:
        return sum(1 for line in f if line.strip())



# ---------------------------------------------------------------------------
# JSON array loader
# ---------------------------------------------------------------------------

def load_json(
    path: Path,
    source: str | None = None,
    header: str | None = None,
) -> tuple[list[Problem], list[ParseError]]:
    """Load problems from a JSON file containing an array of objects.

    Args:
        path: Path to JSON file.
        source: Dataset source name (defaults to filename stem).
        header: Optional Lean header prepended to every problem.

    Returns:
        (problems, errors)
    """
    return _collect_items(iter_json(path, source=source, header=header))


def iter_json(
    path: Path,
    source: str | None = None,
    header: str | None = None,
) -> Iterator[DatasetItem]:
    """Iterate over a JSON array dataset, yielding Problem or ParseError in array order."""
    if source is None:
        source = path.stem

    with open(path, encoding="utf-8") as f:
        try:
            data = json.load(f)
        except json.JSONDecodeError as e:
            yield ParseError(0, f"Invalid JSON file: {e}", "")
            return

    if not isinstance(data, list):
        yield ParseError(0, f"Expected JSON array, got {type(data).__name__}", "")
        return

    first_strategy = None

    for idx, row in enumerate(data):
        if not isinstance(row, dict):
            yield ParseError(idx + 1, f"Expected object at index {idx}, got {type(row).__name__}", str(row)[:200])
            continue

        try:
            resolved = resolve_row(row, row_index=idx, header=header)
        except ValueError as e:
            yield ParseError(idx + 1, str(e), str(row)[:200])
            continue

        if first_strategy is None:
            first_strategy = resolved.strategy
            log.info("Detected schema: %s (from %s)", resolved.strategy, path.name)

        yield _resolved_to_problem(resolved, source)


# ---------------------------------------------------------------------------
# Lean directory loader
# ---------------------------------------------------------------------------

def load_lean_dir(
    directory: Path,
    source: str | None = None,
    header: str | None = None,
) -> tuple[list[Problem], list[ParseError]]:
    """Load problems from a directory of .lean files.

    Each .lean file becomes one Problem. The filename stem is the ID.

    Args:
        directory: Path to directory containing .lean files.
        source: Dataset source name (defaults to directory name).
        header: Optional Lean header prepended to every problem.

    Returns:
        (problems, errors)
    """
    return _collect_items(iter_lean_dir(directory, source=source, header=header))


def iter_lean_dir(
    directory: Path,
    source: str | None = None,
    header: str | None = None,
) -> Iterator[DatasetItem]:
    """Iterate over a directory of .lean files in sorted filename order."""
    if source is None:
        source = directory.name

    lean_files = sorted(directory.glob("*.lean"))
    if not lean_files:
        yield ParseError(0, f"No .lean files found in {directory}", "")
        return

    loaded = 0
    for idx, lean_file in enumerate(lean_files):
        try:
            lean_code = lean_file.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as e:
            yield ParseError(idx + 1, f"Failed to read {lean_file.name}: {e}", "")
            continue

        if not lean_code.strip():
            yield ParseError(idx + 1, f"Empty file: {lean_file.name}", "")
            continue

        if header:
            lean_code = header.rstrip() + "\n" + lean_code

        loaded += 1
        yield Problem(
            id=lean_file.stem,
            source=source,
            lean_code=lean_code,
            metadata={"filename": lean_file.name},
        )

    log.info("Loaded %d .lean files from %s", loaded, directory)


def count_lean_files(directory: Path) -> int:
    """Count .lean files for progress reporting."""
    return sum(1 for _ in directory.glob("*.lean"))


# ---------------------------------------------------------------------------
# HuggingFace loader
# ---------------------------------------------------------------------------

def load_hf(
    repo_id: str,
    split: str | None = None,
    header: str | None = None,
    source: str | None = None,
) -> tuple[list[Problem], list[ParseError]]:
    """Load problems from a HuggingFace dataset.

    Requires: pip install datasets

    Args:
        repo_id: HuggingFace dataset ID (e.g. "AI-MO/CombiBench").
        split: Split to load. If None, prefers "test", then first available.
        header: Optional Lean header prepended to every problem.
        source: Dataset source name (defaults to repo_id with / replaced).

    Returns:
        (problems, errors)
    """
    return _collect_items(iter_hf(repo_id, split=split, header=header, source=source))


def iter_hf(
    repo_id: str,
    split: str | None = None,
    header: str | None = None,
    source: str | None = None,
) -> Iterator[DatasetItem]:
    """Iterate over a HuggingFace dataset split, yielding Problem or ParseError in row order."""
    try:
        import datasets as ds_lib
    except ImportError:
        raise ValueError(
            "HuggingFace datasets library required for --format hf. "
            "Install with: pip install datasets"
        )

    if source is None:
        source = repo_id.replace("/", "_")

    log.info("Loading HuggingFace dataset: %s", repo_id)
    if split:
        effective_split = split
    else:
        try:
            split_names = list(ds_lib.get_dataset_split_names(repo_id, trust_remote_code=True))
        except Exception as e:
            raise ValueError(
                f"Error loading HuggingFace split metadata for {repo_id!r}: {e}. "
                "Specify --split explicitly."
            ) from e

        if not split_names:
            raise ValueError(f"No splits found in HuggingFace dataset {repo_id!r}")

        effective_split = "test" if "test" in split_names else split_names[0]
        log.info("Auto-selected split: %s", effective_split)

    try:
        data = ds_lib.load_dataset(
            repo_id,
            split=effective_split,
            streaming=True,
            trust_remote_code=True,
        )
    except Exception as e:
        raise ValueError(
            f"Error loading HuggingFace dataset {repo_id!r} split {effective_split!r}: {e}"
        ) from e

    print(f"Streaming rows from {repo_id} (split={effective_split})")

    strategy_counts: dict[str, int] = {}

    for idx, row in enumerate(data):
        try:
            resolved = resolve_row(dict(row), row_index=idx, header=header)
            strategy_counts[resolved.strategy] = strategy_counts.get(resolved.strategy, 0) + 1
            yield _resolved_to_problem(resolved, source)
        except ValueError as e:
            yield ParseError(idx + 1, str(e), str(dict(row))[:200])

    for strat, count in sorted(strategy_counts.items()):
        log.info("  Strategy %s: %d rows", strat, count)
