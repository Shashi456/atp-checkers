"""Shared helpers for splitting and rebuilding Lean problem preambles."""
from __future__ import annotations

import re


_TRAILING_BY_RE = re.compile(r"\bby(?:\s*--[^\n]*)?\s*$")


def split_preamble(lean_code: str) -> tuple[tuple[str, ...], str]:
    """Split leading import/open/set_option lines from the body."""
    preamble: list[str] = []
    body_lines: list[str] = []
    scanning = True
    block_comment_depth = 0

    for line in lean_code.splitlines(keepends=True):
        stripped = line.strip()

        if scanning:
            if block_comment_depth > 0:
                body_lines.append(line)
                block_comment_depth += line.count("/-") - line.count("-/")
                if block_comment_depth < 0:
                    block_comment_depth = 0
                continue

            if not stripped or stripped.startswith("--"):
                body_lines.append(line)
                continue

            if stripped.startswith("/-"):
                body_lines.append(line)
                block_comment_depth = stripped.count("/-") - stripped.count("-/")
                if block_comment_depth < 0:
                    block_comment_depth = 0
                continue

            if stripped.startswith(("import ", "open ", "set_option ")):
                preamble.append(stripped)
                if line.endswith("\n"):
                    body_lines.append("\n")
                continue

            scanning = False

        body_lines.append(line)

    return tuple(preamble), "".join(body_lines)


def partition_preamble(preamble: tuple[str, ...]) -> tuple[tuple[str, ...], tuple[str, ...]]:
    """Split a preamble into import lines and cheap local directives."""
    imports: list[str] = []
    directives: list[str] = []
    for line in preamble:
        if line.startswith("import "):
            imports.append(line)
        else:
            directives.append(line)
    return tuple(imports), tuple(directives)


def normalize_imports(imports: tuple[str, ...]) -> tuple[str, ...]:
    """Deduplicate imports while preserving order and excluding AtpLinter."""
    seen: set[str] = set()
    normalized: list[str] = []
    for line in imports:
        if line == "import AtpLinter":
            continue
        if line in seen:
            continue
        seen.add(line)
        normalized.append(line)
    return tuple(normalized)


def build_env_cmd(preamble: tuple[str, ...]) -> str:
    imports, directives = partition_preamble(preamble)
    parts = ["import AtpLinter", *normalize_imports(imports), *directives]
    return "\n".join(parts)


def build_problem_cmd(body: str, directives: tuple[str, ...] = ()) -> str:
    stripped = body.rstrip()
    if _TRAILING_BY_RE.search(stripped):
        stripped += "\n  sorry"

    pieces: list[str] = []
    if directives:
        pieces.append("\n".join(directives))
    if stripped:
        pieces.append(stripped)
    if not pieces:
        return "#check_atp_all"
    return "\n\n".join(pieces) + "\n\n#check_atp_all"


def render_problem_source(lean_code: str, import_module: str | None = None) -> str:
    """Render a runnable Lean file, optionally using a cached import module."""
    preamble, body = split_preamble(lean_code)
    imports, directives = partition_preamble(preamble)

    header_lines: list[str]
    if import_module is None:
        header_lines = ["import AtpLinter", *normalize_imports(imports)]
    else:
        header_lines = [f"import {import_module}"]

    problem_cmd = build_problem_cmd(body, directives=directives)
    header = "\n".join(header_lines)
    if not header:
        return problem_cmd
    return f"{header}\n\n{problem_cmd}"
