"""Shared parsing helpers used by both execution backends."""
from __future__ import annotations

import json
from datetime import datetime, timezone
from typing import Optional, Tuple

from .models import Finding, Provenance


SENTINEL_LINT = "ATP_LINT:"
SENTINEL_DONE = "ATP_DONE"

DEFAULT_TIMEOUT = 30


def make_provenance(toolchain: str) -> Provenance:
    return Provenance(
        lean_toolchain=toolchain,
        timestamp=datetime.now(timezone.utc).isoformat(),
    )


def parse_lint_output(text: str) -> Tuple[list[Finding], list[str]]:
    """Extract ATP_LINT findings and malformed-line errors from linter output."""
    findings = []
    parse_errors = []
    for line in text.splitlines():
        if line.startswith(SENTINEL_LINT):
            json_str = line[len(SENTINEL_LINT):]
            try:
                findings.append(Finding.from_dict(json.loads(json_str)))
            except json.JSONDecodeError as e:
                parse_errors.append(f"Malformed ATP_LINT JSON: {e} in: {json_str[:100]}")
    return findings, parse_errors


def has_done_sentinel(text: str) -> Tuple[bool, Optional[dict]]:
    """Check for ATP_DONE sentinel and parse its metadata."""
    for line in text.splitlines():
        if line.startswith(SENTINEL_DONE):
            rest = line[len(SENTINEL_DONE):]
            if rest.startswith(":"):
                try:
                    return True, json.loads(rest[1:])
                except json.JSONDecodeError:
                    return True, None
            return True, None
    return False, None
