"""Data models and shared parsing helpers for the ATP checkers runner."""
from __future__ import annotations

import json
from dataclasses import dataclass, field
from datetime import datetime, timezone

# ---------------------------------------------------------------------------
# Sentinel constants
# ---------------------------------------------------------------------------

SENTINEL_LINT = "ATP_LINT:"
SENTINEL_DONE = "ATP_DONE"

DEFAULT_TIMEOUT = 30
RESULT_SCHEMA_VERSION = 1


# ---------------------------------------------------------------------------
# Data models
# ---------------------------------------------------------------------------

@dataclass
class Problem:
    """A problem to lint."""
    id: str
    source: str
    lean_code: str
    metadata: dict = field(default_factory=dict)


@dataclass
class Finding:
    """A single lint finding."""
    category: str
    severity: str
    declaration: str
    message: str
    suggestion: str | None = None
    confidence: str = "maybe"
    proved_by: str | None = None
    taxonomy_category: str | None = None

    @classmethod
    def from_dict(cls, d: dict) -> Finding:
        return cls(
            category=d.get("category", "unknown"),
            severity=d.get("severity", "warning"),
            declaration=d.get("declaration", ""),
            message=d.get("message", ""),
            suggestion=d.get("suggestion"),
            confidence=d.get("confidence", "maybe"),
            proved_by=d.get("provedBy"),
            taxonomy_category=d.get("taxonomyCategory"),
        )


@dataclass
class Provenance:
    """Provenance information for reproducibility."""
    lean_toolchain: str
    timestamp: str

    def to_dict(self) -> dict:
        return {
            "lean_toolchain": self.lean_toolchain,
            "timestamp": self.timestamp,
        }


@dataclass
class LintResult:
    """Result of linting a single problem."""
    problem_id: str
    source: str
    status: str  # Primary outcome: ok, findings, compile_error, timeout, infra_error
    findings: list[Finding]
    error_message: str | None
    duration_ms: int
    provenance: Provenance
    compile_error: bool = False
    compile_error_message: str | None = None
    dataset: str | None = None
    run_id: str | None = None
    metadata: dict = field(default_factory=dict)

    def to_dict(self) -> dict:
        return {
            "schema_version": RESULT_SCHEMA_VERSION,
            "dataset": self.dataset,
            "run_id": self.run_id,
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
                    "taxonomyCategory": f.taxonomy_category,
                }
                for f in self.findings
            ],
            "error_message": self.error_message,
            "duration_ms": self.duration_ms,
            "provenance": self.provenance.to_dict(),
            "compile_error": self.compile_error,
            "compile_error_message": self.compile_error_message,
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


# ---------------------------------------------------------------------------
# Parsing helpers
# ---------------------------------------------------------------------------

def make_provenance(toolchain: str) -> Provenance:
    return Provenance(
        lean_toolchain=toolchain,
        timestamp=datetime.now(timezone.utc).isoformat(),
    )


def parse_lint_output(text: str) -> tuple[list[Finding], list[str]]:
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


def has_done_sentinel(text: str) -> tuple[bool, dict | None, str | None]:
    """Check for ATP_DONE sentinel and parse its metadata.

    Returns (done, metadata, parse_error). A malformed JSON payload is
    surfaced as parse_error so the caller can log it rather than silently
    accepting done=True with no metadata.
    """
    for line in text.splitlines():
        if line.startswith(SENTINEL_DONE):
            rest = line[len(SENTINEL_DONE):]
            if rest.startswith(":"):
                payload = rest[1:]
                try:
                    return True, json.loads(payload), None
                except json.JSONDecodeError as e:
                    return True, None, f"Malformed ATP_DONE JSON: {e} in: {payload[:100]}"
            return True, None, None
    return False, None, None


def classify_lint_execution(
    *,
    problem: Problem,
    toolchain: str,
    duration_ms: int,
    stdout: str,
    stderr: str = "",
    returncode: int = 0,
    compile_error: bool | None = None,
    compile_error_message: str | None = None,
    metadata: dict | None = None,
) -> LintResult:
    """Classify raw linter output into the runner result schema."""
    result_metadata = problem.metadata if metadata is None else metadata
    findings, parse_errors = parse_lint_output(stdout)
    done, done_meta, done_parse_err = has_done_sentinel(stdout)
    if done_parse_err is not None:
        parse_errors.append(done_parse_err)

    if compile_error is None:
        compile_error = returncode > 0
    if compile_error and compile_error_message is None:
        compile_error_message = (
            f"=== STDOUT ===\n{stdout[:2000]}\n\n=== STDERR ===\n{stderr[:2000]}"
        )[:4000]

    truncation_error = None
    if done and done_meta and "findings" in done_meta:
        expected_findings = done_meta["findings"]
        actual_findings = len(findings)
        if expected_findings != actual_findings:
            truncation_error = (
                f"Output may be truncated: ATP_DONE reports {expected_findings} "
                f"findings but only {actual_findings} were parsed"
            )

    if parse_errors or truncation_error:
        errors_section = ""
        if truncation_error:
            errors_section += f"=== TRUNCATION ===\n{truncation_error}\n\n"
        if parse_errors:
            errors_section += "=== PARSE ERRORS ===\n" + "\n".join(parse_errors)
        combined_output = (
            f"=== STDOUT ===\n{stdout[:3000]}\n\n"
            f"=== STDERR ===\n{stderr[:1000]}\n\n"
            f"{errors_section}"
        )
        return LintResult(
            problem_id=problem.id,
            source=problem.source,
            status="infra_error",
            findings=findings,
            error_message=combined_output[:4000],
            duration_ms=duration_ms,
            provenance=make_provenance(toolchain),
            compile_error=compile_error,
            compile_error_message=compile_error_message,
            metadata=result_metadata,
        )

    if returncode < 0:
        signal_num = -returncode
        combined_output = (
            f"Process killed by signal {signal_num}\n\n"
            f"=== STDOUT ===\n{stdout[:2000]}\n\n"
            f"=== STDERR ===\n{stderr[:2000]}"
        )
        return LintResult(
            problem_id=problem.id,
            source=problem.source,
            status="infra_error",
            findings=[],
            error_message=combined_output[:4000],
            duration_ms=duration_ms,
            provenance=make_provenance(toolchain),
            metadata=result_metadata,
        )

    if compile_error and not done:
        return LintResult(
            problem_id=problem.id,
            source=problem.source,
            status="compile_error",
            findings=[],
            error_message=compile_error_message,
            duration_ms=duration_ms,
            provenance=make_provenance(toolchain),
            compile_error=True,
            compile_error_message=compile_error_message,
            metadata=result_metadata,
        )

    if not done:
        combined_output = (
            f"Linter did not complete (no ATP_DONE sentinel)\n\n"
            f"=== STDOUT ===\n{stdout[:2000]}\n\n"
            f"=== STDERR ===\n{stderr[:1000]}"
        )
        return LintResult(
            problem_id=problem.id,
            source=problem.source,
            status="infra_error",
            findings=[],
            error_message=combined_output[:4000],
            duration_ms=duration_ms,
            provenance=make_provenance(toolchain),
            compile_error=compile_error,
            compile_error_message=compile_error_message,
            metadata=result_metadata,
        )

    return LintResult(
        problem_id=problem.id,
        source=problem.source,
        status="findings" if findings else "ok",
        findings=findings,
        error_message=None,
        duration_ms=duration_ms,
        provenance=make_provenance(toolchain),
        compile_error=compile_error,
        compile_error_message=compile_error_message,
        metadata=result_metadata,
    )
