"""Dataset loaders for the ATP checkers runner."""
from __future__ import annotations

import json
from pathlib import Path
from typing import Iterator, Tuple
import sys

from .models import Problem, ParseError


def load_jsonl(
    path: Path,
    source: str | None = None,
    on_error: str = "skip"  # "skip", "raise", or "include"
) -> Tuple[list[Problem], list[ParseError]]:
    """
    Load problems from a JSONL file.

    Expected format per line:
    {"id": "...", "lean_code": "...", ...}

    The 'id' and 'lean_code' fields are required.
    All other fields are stored in metadata.

    Args:
        path: Path to JSONL file
        source: Dataset source name (defaults to filename stem)
        on_error: How to handle parse errors:
            - "skip": Skip bad lines, continue loading
            - "raise": Raise exception on first error
            - "include": Include ParseError objects in errors list

    Returns:
        Tuple of (problems, errors)
    """
    if source is None:
        source = path.stem

    problems = []
    errors = []

    with open(path, "r", encoding="utf-8") as f:
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
                errors.append(err)
                continue

            # Extract required fields
            problem_id = data.get("id")
            if problem_id is None:
                err = ParseError(line_num, "Missing 'id' field", line[:200])
                if on_error == "raise":
                    raise ValueError(f"{path}:{line_num}: {err.error}")
                errors.append(err)
                continue

            lean_code = data.get("lean_code")
            if lean_code is None:
                err = ParseError(line_num, "Missing 'lean_code' field", line[:200])
                if on_error == "raise":
                    raise ValueError(f"{path}:{line_num}: {err.error}")
                errors.append(err)
                continue

            # Validate lean_code is a string
            if not isinstance(lean_code, str):
                err = ParseError(line_num, f"'lean_code' must be string, got {type(lean_code).__name__}", line[:200])
                if on_error == "raise":
                    raise ValueError(f"{path}:{line_num}: {err.error}")
                errors.append(err)
                continue

            # Everything else goes into metadata
            metadata = {k: v for k, v in data.items() if k not in ("id", "lean_code")}

            problems.append(Problem(
                id=str(problem_id),
                source=source,
                lean_code=lean_code,
                metadata=metadata,
            ))

    return problems, errors


def load_jsonl_streaming(path: Path, source: str | None = None) -> Iterator[Problem | ParseError]:
    """
    Load problems from a JSONL file as a stream.

    Yields Problem objects for valid lines and ParseError for invalid ones.
    This avoids loading everything into memory.
    """
    if source is None:
        source = path.stem

    with open(path, "r", encoding="utf-8") as f:
        for line_num, line in enumerate(f, start=1):
            line = line.strip()
            if not line:
                continue

            try:
                data = json.loads(line)
            except json.JSONDecodeError as e:
                yield ParseError(line_num, f"Invalid JSON: {e}", line[:200])
                continue

            problem_id = data.get("id")
            if problem_id is None:
                yield ParseError(line_num, "Missing 'id' field", line[:200])
                continue

            lean_code = data.get("lean_code")
            if lean_code is None:
                yield ParseError(line_num, "Missing 'lean_code' field", line[:200])
                continue

            if not isinstance(lean_code, str):
                yield ParseError(line_num, f"'lean_code' must be string, got {type(lean_code).__name__}", line[:200])
                continue

            metadata = {k: v for k, v in data.items() if k not in ("id", "lean_code")}

            yield Problem(
                id=str(problem_id),
                source=source,
                lean_code=lean_code,
                metadata=metadata,
            )
