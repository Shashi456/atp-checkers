"""Data models for the ATP checkers runner."""
from __future__ import annotations

from dataclasses import dataclass, field
from datetime import datetime
from typing import Optional, Any
import json


@dataclass
class Problem:
    """A problem to lint."""
    id: str
    source: str
    lean_code: str
    metadata: dict = field(default_factory=dict)

    @property
    def natural_language(self) -> Optional[str]:
        """Get natural language statement if available."""
        return self.metadata.get("natural_language") or self.metadata.get("nl_statement")


@dataclass
class Finding:
    """A single lint finding."""
    category: str
    severity: str
    declaration: str
    message: str
    suggestion: Optional[str] = None
    confidence: str = "maybe"           # "proven" or "maybe"
    proved_by: Optional[str] = None     # tactic/method name

    @classmethod
    def from_dict(cls, d: dict) -> "Finding":
        return cls(
            category=d.get("category", "unknown"),
            severity=d.get("severity", "warning"),
            declaration=d.get("declaration", ""),
            message=d.get("message", ""),
            suggestion=d.get("suggestion"),
            confidence=d.get("confidence", "maybe"),
            proved_by=d.get("provedBy"),
        )


@dataclass
class Provenance:
    """Provenance information for reproducibility."""
    runner_version: str
    linter_version: str
    lean_toolchain: str
    timestamp: str

    def to_dict(self) -> dict:
        return {
            "runner_version": self.runner_version,
            "linter_version": self.linter_version,
            "lean_toolchain": self.lean_toolchain,
            "timestamp": self.timestamp,
        }


@dataclass
class LintResult:
    """Result of linting a single problem."""
    problem_id: str
    source: str
    status: str  # ok, findings, compile_error, timeout, infra_error
    findings: list[Finding]
    error_message: Optional[str]
    duration_ms: int
    provenance: Provenance
    metadata: dict = field(default_factory=dict)  # Preserve original metadata including NL

    def to_dict(self) -> dict:
        return {
            "problem_id": self.problem_id,
            "source": self.source,
            "status": self.status,
            "findings": [
                {
                    "category": f.category,
                    "severity": f.severity,
                    "declaration": f.declaration,
                    "message": f.message,
                    "suggestion": f.suggestion,
                    "confidence": f.confidence,
                    "provedBy": f.proved_by,
                }
                for f in self.findings
            ],
            "error_message": self.error_message,
            "duration_ms": self.duration_ms,
            "provenance": self.provenance.to_dict(),
            "metadata": self.metadata,
        }

    def to_jsonl(self) -> str:
        return json.dumps(self.to_dict(), ensure_ascii=False)


@dataclass
class ParseError:
    """Represents a JSON parse error for a line."""
    line_number: int
    error: str
    raw_line: str
