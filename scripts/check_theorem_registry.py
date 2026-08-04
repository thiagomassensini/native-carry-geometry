#!/usr/bin/env python3
"""Cross-check NCG theorem markers against ``audit/theorems.tsv``."""

from __future__ import annotations

import argparse
import csv
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

from auditlib import (
    AuditFailure,
    NCG_ID_RE,
    REPOSITORY_ROOT,
    fail_if_errors,
    lean_sources,
    module_name,
    module_path,
    public_import_closure,
    relative_display,
    strip_lean_comments_and_strings,
    write_report,
)


REQUIRED_COLUMNS = ("id", "declaration", "module")
INACTIVE_STATUSES = {"retired", "reserved"}
COMMENT_MARKER_RE = re.compile(r"\b(NCG-[A-Z]{3}-[0-9]{3})\s*:")
ATTRIBUTE_MARKER_RE = re.compile(
    r"\bncg_id\s+\"(NCG-[A-Z]{3}-[0-9]{3})\""
)
DECLARATION_RE = re.compile(
    r"\b(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)


@dataclass(frozen=True)
class RegistryRow:
    line: int
    theorem_id: str
    declaration: str
    module: str
    kind: str
    status: str


@dataclass(frozen=True)
class Annotation:
    theorem_id: str
    declaration: str
    kind: str
    module: str
    path: Path
    line: int


def final_component(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def read_registry(path: Path) -> tuple[list[RegistryRow], list[str]]:
    errors: list[str] = []
    if not path.is_file():
        raise AuditFailure(
            "missing audit/theorems.tsv; expected a committed UTF-8 TSV registry"
        )
    raw = path.read_text(encoding="utf-8")
    if "\r" in raw:
        errors.append("audit/theorems.tsv must use LF line endings")
    if raw and not raw.endswith("\n"):
        errors.append("audit/theorems.tsv must end with LF")

    reader = csv.DictReader(raw.splitlines(), delimiter="\t")
    if reader.fieldnames is None:
        raise AuditFailure("audit/theorems.tsv has no header")
    if len(reader.fieldnames) != len(set(reader.fieldnames)):
        errors.append("audit/theorems.tsv has duplicate header columns")
    for required in REQUIRED_COLUMNS:
        if required not in reader.fieldnames:
            errors.append(f"audit/theorems.tsv is missing required column {required!r}")
    fail_if_errors(errors)

    rows: list[RegistryRow] = []
    for index, record in enumerate(reader, start=2):
        if None in record:
            errors.append(f"audit/theorems.tsv:{index}: too many tab-separated fields")
            continue
        theorem_id = (record.get("id") or "").strip()
        declaration = (record.get("declaration") or "").strip()
        module = (record.get("module") or "").strip()
        kind = (record.get("kind") or "theorem").strip().lower()
        status = (record.get("status") or "active").strip().lower()
        if not theorem_id and not declaration and not module:
            errors.append(f"audit/theorems.tsv:{index}: blank rows are not allowed")
            continue
        if not NCG_ID_RE.fullmatch(theorem_id):
            errors.append(
                f"audit/theorems.tsv:{index}: invalid permanent ID {theorem_id!r}"
            )
        if not declaration:
            errors.append(f"audit/theorems.tsv:{index}: empty declaration")
        if not module:
            errors.append(f"audit/theorems.tsv:{index}: empty module")
        rows.append(
            RegistryRow(
                index,
                theorem_id,
                declaration,
                module,
                kind or "theorem",
                status or "active",
            )
        )

    ids: dict[str, int] = {}
    declarations: dict[str, int] = {}
    for row in rows:
        if row.theorem_id in ids:
            errors.append(
                f"audit/theorems.tsv:{row.line}: duplicate ID {row.theorem_id}; "
                f"first seen on line {ids[row.theorem_id]}"
            )
        ids[row.theorem_id] = row.line
        if row.status not in INACTIVE_STATUSES:
            if row.declaration in declarations:
                errors.append(
                    f"audit/theorems.tsv:{row.line}: duplicate active declaration "
                    f"{row.declaration}; first seen on line "
                    f"{declarations[row.declaration]}"
                )
            declarations[row.declaration] = row.line

    observed_order = [row.theorem_id for row in rows]
    if observed_order != sorted(observed_order):
        errors.append("audit/theorems.tsv rows must be sorted lexicographically by ID")
    return rows, errors


def annotations_in(path: Path) -> tuple[list[Annotation], list[str]]:
    errors: list[str] = []
    source = path.read_text(encoding="utf-8")
    code = strip_lean_comments_and_strings(source)
    module = module_name(path)
    annotations: list[Annotation] = []
    seen: set[tuple[str, str, str]] = set()

    marker_matches = list(COMMENT_MARKER_RE.finditer(source))
    marker_matches.extend(ATTRIBUTE_MARKER_RE.finditer(source))
    marker_matches.sort(key=lambda match: match.start())

    for marker in marker_matches:
        theorem_id = marker.group(1)
        declaration_match = DECLARATION_RE.search(code, marker.end())
        line = source.count("\n", 0, marker.start()) + 1
        if declaration_match is None:
            errors.append(
                f"{relative_display(path)}:{line}: {theorem_id} has no following declaration"
            )
            continue
        kind, declaration = declaration_match.groups()
        key = (theorem_id, declaration, module)
        if key in seen:
            # Supporting both a doc marker and @[ncg_id "..."] must not make a
            # correctly dual-annotated theorem appear duplicated.
            continue
        seen.add(key)
        annotations.append(
            Annotation(theorem_id, declaration, kind, module, path, line)
        )
    return annotations, errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--registry",
        type=Path,
        default=REPOSITORY_ROOT / "audit" / "theorems.tsv",
    )
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()

    rows, errors = read_registry(args.registry)
    active_rows = [row for row in rows if row.status not in INACTIVE_STATUSES]

    source_lock_path = REPOSITORY_ROOT / "audit" / "source-lock.json"
    try:
        source_lock = json.loads(source_lock_path.read_text(encoding="utf-8"))
        locked_count = source_lock["registry"]["id_count"]
        if locked_count != len(active_rows):
            errors.append(
                "audit/source-lock.json registry.id_count is "
                f"{locked_count}, expected {len(active_rows)} active IDs"
            )
    except (OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        errors.append(f"invalid audit/source-lock.json registry count: {error}")

    reached, _, _ = public_import_closure()
    annotations: list[Annotation] = []
    for path in lean_sources():
        found, source_errors = annotations_in(path)
        annotations.extend(found)
        errors.extend(source_errors)

    by_id: dict[str, list[Annotation]] = {}
    for annotation in annotations:
        by_id.setdefault(annotation.theorem_id, []).append(annotation)

    registry_ids = {row.theorem_id for row in rows}
    active_ids = {row.theorem_id for row in active_rows}
    for theorem_id in sorted(by_id):
        if theorem_id not in registry_ids:
            locations = ", ".join(
                f"{relative_display(item.path)}:{item.line}" for item in by_id[theorem_id]
            )
            errors.append(f"source ID {theorem_id} is absent from registry ({locations})")

    for row in active_rows:
        expected_path = module_path(row.module)
        if not expected_path.is_file():
            errors.append(
                f"audit/theorems.tsv:{row.line}: module {row.module} has no source file"
            )
        if row.module not in reached:
            errors.append(
                f"audit/theorems.tsv:{row.line}: module {row.module} is not reachable "
                "from NativeCarryGeometry.lean"
            )

        matches = by_id.get(row.theorem_id, [])
        if not matches:
            errors.append(
                f"audit/theorems.tsv:{row.line}: active ID {row.theorem_id} "
                "has no source annotation"
            )
            continue
        if len(matches) != 1:
            locations = ", ".join(
                f"{relative_display(item.path)}:{item.line} -> {item.declaration}"
                for item in matches
            )
            errors.append(
                f"audit/theorems.tsv:{row.line}: ID {row.theorem_id} annotates "
                f"multiple declarations ({locations})"
            )
            continue
        annotation = matches[0]
        if annotation.module != row.module:
            errors.append(
                f"audit/theorems.tsv:{row.line}: {row.theorem_id} module is "
                f"{row.module}, source annotation is in {annotation.module}"
            )
        if final_component(row.declaration) != annotation.declaration:
            errors.append(
                f"audit/theorems.tsv:{row.line}: {row.theorem_id} declaration is "
                f"{row.declaration}, source annotation names {annotation.declaration}"
            )
        if row.kind != annotation.kind:
            errors.append(
                f"audit/theorems.tsv:{row.line}: {row.theorem_id} kind is "
                f"{row.kind}, source declaration is {annotation.kind}"
            )

    for row in rows:
        if row.status in INACTIVE_STATUSES and row.theorem_id in by_id:
            errors.append(
                f"audit/theorems.tsv:{row.line}: inactive ID {row.theorem_id} "
                "still annotates a source declaration"
            )

    report = {
        "check": "theorem-registry-source-crosswalk",
        "registry": relative_display(args.registry),
        "required_columns": list(REQUIRED_COLUMNS),
        "row_count": len(rows),
        "active_count": len(active_rows),
        "inactive_count": len(rows) - len(active_rows),
        "source_annotation_count": len(annotations),
        "active_ids": sorted(active_ids),
        "errors": sorted(set(errors)),
        "status": "pass" if not errors else "fail",
    }
    write_report(args.report, report)
    fail_if_errors(errors)
    print(
        f"PASS: {len(active_rows)} active theorem IDs match one reachable "
        "source declaration each"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AuditFailure, UnicodeDecodeError, csv.Error) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
