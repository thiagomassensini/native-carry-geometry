#!/usr/bin/env python3
"""Reject proof placeholders and project-defined axioms in Lean sources."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from auditlib import (
    AuditFailure,
    REPOSITORY_ROOT,
    fail_if_errors,
    lean_sources,
    relative_display,
    strip_lean_comments_and_strings,
    write_report,
)


FORBIDDEN_TOKENS = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "sorryAx": re.compile(r"\bsorryAx\b"),
}
AXIOM_COMMAND_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]\r\n]+\][ \t]*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|local|scoped)[ \t]+)*"
    r"(?:axioms?|constants?)\b"
)


def line_number(source: str, offset: int) -> int:
    return source.count("\n", 0, offset) + 1


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()

    errors: list[str] = []
    inspected: list[str] = []
    for path in lean_sources():
        relative = relative_display(path)
        inspected.append(relative)
        source = path.read_text(encoding="utf-8")
        try:
            code = strip_lean_comments_and_strings(source)
        except AuditFailure as error:
            errors.append(f"{relative}: {error}")
            continue

        for label, pattern in FORBIDDEN_TOKENS.items():
            for match in pattern.finditer(code):
                errors.append(
                    f"{relative}:{line_number(source, match.start())}: "
                    f"forbidden proof token {label}"
                )
        for match in AXIOM_COMMAND_RE.finditer(code):
            errors.append(
                f"{relative}:{line_number(source, match.start())}: "
                "project-defined axiom command is forbidden"
            )

    report = {
        "check": "no-placeholders-or-project-axioms",
        "repository": str(REPOSITORY_ROOT),
        "files_inspected": inspected,
        "file_count": len(inspected),
        "errors": sorted(set(errors)),
        "status": "pass" if not errors else "fail",
    }
    write_report(args.report, report)
    fail_if_errors(errors)
    print(f"PASS: inspected {len(inspected)} Lean files; no placeholders or axioms")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AuditFailure as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
