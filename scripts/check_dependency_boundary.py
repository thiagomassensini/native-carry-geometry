#!/usr/bin/env python3
"""Audit the public import closure and excluded-route boundary."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from auditlib import (
    AuditFailure,
    PROJECT_MODULE_PREFIX,
    REPOSITORY_ROOT,
    fail_if_errors,
    imports_in,
    public_import_closure,
    relative_display,
    strip_lean_comments_and_strings,
    write_report,
)


# These are code-level identifiers or module-name fragments, not prose checks.
# Comments and strings are masked before matching.
EXCLUDED_CODE_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    (
        "Green route",
        re.compile(r"\b[A-Za-z0-9_']*green[A-Za-z0-9_']*\b", re.IGNORECASE),
    ),
    (
        "Bessel route",
        re.compile(r"\b[A-Za-z0-9_']*bessel[A-Za-z0-9_']*\b", re.IGNORECASE),
    ),
    (
        "TFVD route",
        re.compile(r"\b[A-Za-z0-9_']*tfvd[A-Za-z0-9_']*\b", re.IGNORECASE),
    ),
    ("G_pre route", re.compile(r"\bG_?pre[A-Za-z0-9_']*\b", re.IGNORECASE)),
    (
        "precompression route",
        re.compile(r"\b[A-Za-z0-9_']*precompression[A-Za-z0-9_']*\b", re.IGNORECASE),
    ),
    (
        "Cayley route",
        re.compile(r"\b[A-Za-z0-9_']*cayley[A-Za-z0-9_']*\b", re.IGNORECASE),
    ),
    (
        "self-adjoint route",
        re.compile(r"\b[A-Za-z0-9_']*selfAdjoint[A-Za-z0-9_']*\b", re.IGNORECASE),
    ),
    (
        "spectral-pencil route",
        re.compile(r"\b[A-Za-z0-9_']*spectralPencil[A-Za-z0-9_']*\b", re.IGNORECASE),
    ),
    (
        "root-tangent route",
        re.compile(r"\b[A-Za-z0-9_']*rootTangent[A-Za-z0-9_']*\b", re.IGNORECASE),
    ),
    (
        "LSB route",
        re.compile(r"\b[A-Za-z0-9_']*lsb[A-Za-z0-9_']*\b", re.IGNORECASE),
    ),
    (
        "external classical function",
        re.compile(r"\b(?:riemann_?zeta|zeta)\b", re.IGNORECASE),
    ),
    (
        "explicit-formula route",
        re.compile(r"\b[A-Za-z0-9_']*explicitFormula[A-Za-z0-9_']*\b", re.IGNORECASE),
    ),
    (
        "Möbius-inversion route",
        re.compile(r"\b[A-Za-z0-9_']*moebius[A-Za-z0-9_']*\b", re.IGNORECASE),
    ),
)

EXCLUDED_IMPORT_PATTERNS: tuple[re.Pattern[str], ...] = (
    re.compile(r"(?:^|\.)External(?:\.|$)"),
    re.compile(r"(?:^|\.)(?:Green|Bessel|TFVD|Gpre|Precompression|Cayley)(?:\.|$)"),
)

# Meta exporters and the deliberately deferred external module are not required
# to be reachable from the public mathematical root.
REACHABILITY_EXEMPT_PREFIXES = (
    f"{PROJECT_MODULE_PREFIX}.Audit.",
    f"{PROJECT_MODULE_PREFIX}.External.",
)


def line_number(source: str, offset: int) -> int:
    return source.count("\n", 0, offset) + 1


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()

    reached, graph, modules = public_import_closure()
    errors: list[str] = []

    for name in sorted(modules):
        if name in reached or name == PROJECT_MODULE_PREFIX:
            continue
        if name.startswith(REACHABILITY_EXEMPT_PREFIXES):
            continue
        errors.append(f"module is not reachable from public root: {name}")

    scanned: list[str] = []
    for name in sorted(reached):
        path = modules[name]
        relative = relative_display(path)
        scanned.append(name)
        source = path.read_text(encoding="utf-8")
        code = strip_lean_comments_and_strings(source)

        for imported in imports_in(path):
            for pattern in EXCLUDED_IMPORT_PATTERNS:
                if pattern.search(imported):
                    errors.append(
                        f"{relative}: excluded import in public closure: {imported}"
                    )

        for label, pattern in EXCLUDED_CODE_PATTERNS:
            for match in pattern.finditer(code):
                errors.append(
                    f"{relative}:{line_number(source, match.start())}: "
                    f"excluded {label} identifier {match.group(0)!r}"
                )

    report = {
        "check": "public-root-dependency-boundary",
        "root": PROJECT_MODULE_PREFIX,
        "reachable_modules": sorted(reached),
        "reachable_count": len(reached),
        "project_module_count": len(modules),
        "graph": {name: sorted(imported) for name, imported in sorted(graph.items())},
        "reachability_exempt_prefixes": list(REACHABILITY_EXEMPT_PREFIXES),
        "errors": sorted(set(errors)),
        "status": "pass" if not errors else "fail",
    }
    write_report(args.report, report)
    fail_if_errors(errors)
    print(
        "PASS: public root reaches "
        f"{len(reached)}/{len(modules)} project modules with no excluded routes"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AuditFailure as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
