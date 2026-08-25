#!/usr/bin/env python3
"""Audit separation of raw zero predicates from native-mass representation."""

from __future__ import annotations

import argparse
import csv
import json
import re
from pathlib import Path

from auditlib import REPOSITORY_ROOT

EXCLUDED_PARTS = {".git", ".lake", "__pycache__"}

EXPECTED_STATEMENTS = {
    "MASS_UPSTREAM": "Carry mass and its quadratic-root amplitude are constructed before the native state and operator.",
    "SIGMA_IS_NORM_DEFORMATION": "Sigma changes radial amplitude and quadratic norm; native-mass compatibility is a separate representation predicate.",
    "REAL_COMPLEX_SAME_OPERATOR": "Real pairs and complex numbers are faithful additive coordinates of the same resultants and preserve the full raw zero locus in the stated domain.",
    "RAW_ZERO_IS_CANCELLATION": "A raw finite, real-boundary, or analytic radial zero is exactly resultant cancellation at the supplied coordinates and contains no mass-compatibility premise.",
    "NATIVE_SPECIALIZATION": "At sigma one half, the raw radial zero predicate agrees with the zero predicate of the fixed carry-built native operator.",
    "NATIVE_REPRESENTATION_IS_SEPARATE": "Native representation conjoins upstream mass compatibility with a raw zero; its half-shell factorization does not classify the full raw zero locus.",
}

EXPECTED_LEGACY_ALIASES = {
    "NativeCarryGeometry.Measure.massWeight": "NativeCarryGeometry.Measure.radialEnergyWeight",
    "NativeCarryGeometry.Measure.criticalAmplitude": "NativeCarryGeometry.Measure.carryAmplitude",
    "NativeCarryGeometry.Operator.realCarryState": "NativeCarryGeometry.Operator.radialDeformationState",
    "NativeCarryGeometry.Operator.RealCarryEnergyCompatible": "NativeCarryGeometry.Operator.RadialDeformationRepresentsNativeMass",
    "NativeCarryGeometry.Operator.finiteRealCarryOperator": "NativeCarryGeometry.Operator.finiteRadialDeformation",
    "NativeCarryGeometry.Operator.BoundaryConvergesToZero": "NativeCarryGeometry.Operator.RadialChartCancelsAt",
    "NativeCarryGeometry.Operator.IsNativeRealCarryOperatorZero": "NativeCarryGeometry.Operator.IsNativeCarryOperatorZero",
    "NativeCarryGeometry.Equivalence.IsNativeCanonicalCarryOperatorZero": "NativeCarryGeometry.Operator.IsNativeCarryOperatorZero",
}

FORBIDDEN_LEGACY_ALIAS_KEYS = {
    "NativeCarryGeometry.Operator.IsFiniteRealCarryOperatorZero",
    "NativeCarryGeometry.Operator.IsRealCarryOperatorZero",
    "NativeCarryGeometry.Equivalence.IsCanonicalCarryOperatorZero",
    "NativeCarryGeometry.Operator.IsRadialDeformationPresentationZero",
}

FORBIDDEN_CURRENT_TEXT = {
    "realCarryOperatorZero_sigma_eq_half",
    "not_realCarryOperatorZero_of_sigma_ne_half",
    "canonicalCarryOperatorZero_re_eq_half",
    "AMBIENT_CANCELLATION_NOT_ZERO",
    "raw chart cancellation is an operator zero",
    "raw chart cancellation is not an operator zero",
}

REQUIRED_TEXT = {
    "README.md": [
        "Fixed native zero and raw radial-family zero are separate predicates",
        "IsRealCarryOperatorZero",
        "IsCanonicalCarryOperatorZero",
        "Native representation is a different question",
    ],
    "NativeCarryGeometry/Operator/FiniteRealOperator.lean": [
        "IsFiniteRadialCarryOperatorZero",
        "Finite Radial Operator Zero/Resultant Identity",
    ],
    "NativeCarryGeometry/Operator/ZeroSetFactorization.lean": [
        "IsRadialCarryOperatorZero",
        "realCarryOperatorZero_half_iff_native",
        "radialChartRepresentsNativeZero_iff_massCompatible_and_zero",
    ],
    "NativeCarryGeometry/Equivalence/RealAnalyticBoundary.lean": [
        "IsCanonicalCarryOperatorZero",
        "Real/Analytic Radial Zero-Locus Identity",
        "analyticChartRepresentsNativeZero_iff_massCompatible_and_zero",
    ],
    "docs/00_SCOPE.md": ["A raw zero outside one half is still a zero"],
    "docs/70_ZERO_SET_FACTORIZATION.md": [
        "Removed circular corollaries",
        "raw radial zero ⇒ sigma = 1/2",
    ],
    "docs/90_SEMANTIC_AUDIT.md": ["Corrected contract"],
    "audit/README.md": ["Corrected semantic surface"],
    "docs/80_THEOREM_REGISTRY.md": [
        "Half-Shell Radial/Native Zero Identity",
        "Analytic Native-Representation Predicate Separation",
    ],
}

REQUIRED_REGISTRY = {
    "NCG-OPR-003": (
        "NativeCarryGeometry.Operator.isFiniteRealCarryOperatorZero_iff",
        "Finite Radial Operator Zero/Resultant Identity",
    ),
    "NCG-OPR-004": (
        "NativeCarryGeometry.Operator.isRealCarryOperatorZero_iff",
        "Radial Operator Zero/Boundary Cancellation Identity",
    ),
    "NCG-OPR-005": (
        "NativeCarryGeometry.Operator.realCarryOperatorZero_half_iff_native",
        "Half-Shell Radial/Native Zero Identity",
    ),
    "NCG-OPR-006": (
        "NativeCarryGeometry.Operator.radialChartRepresentsNativeZero_iff_massCompatible_and_zero",
        "Native Representation Predicate Separation",
    ),
    "NCG-EQV-008": (
        "NativeCarryGeometry.Equivalence.isRealCarryOperatorZero_iff_isCanonicalCarryOperatorZero",
        "Real/Analytic Radial Zero-Locus Identity",
    ),
    "NCG-EQV-009": (
        "NativeCarryGeometry.Equivalence.analyticChartRepresentsNativeZero_iff_massCompatible_and_zero",
        "Analytic Native-Representation Predicate Separation",
    ),
}


def versioned_text_files() -> tuple[dict[str, str], list[str]]:
    result: dict[str, str] = {}
    errors: list[str] = []
    for path in sorted(REPOSITORY_ROOT.rglob("*")):
        if not path.is_file() or any(part in EXCLUDED_PARTS for part in path.parts):
            continue
        relative = str(path.relative_to(REPOSITORY_ROOT))
        try:
            result[relative] = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            errors.append(f"{relative} is not UTF-8 text")
    return result, errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()

    files, errors = versioned_text_files()

    try:
        contract = json.loads(files["audit/semantic-contract.json"])
    except (KeyError, json.JSONDecodeError) as exc:
        contract = {}
        errors.append(f"invalid audit/semantic-contract.json: {exc}")

    if contract.get("schema") != "native-carry-semantic-contract-v2":
        errors.append("semantic contract schema must be v2")
    if contract.get("baseline_release") != "v0.4.0":
        errors.append("semantic contract baseline_release must be v0.4.0")

    by_id = {
        str(item.get("id")): item
        for item in contract.get("contracts", [])
        if isinstance(item, dict)
    }
    for contract_id, statement in EXPECTED_STATEMENTS.items():
        if by_id.get(contract_id, {}).get("statement") != statement:
            errors.append(f"statement mismatch for {contract_id}")

    aliases = contract.get("legacy_aliases", {})
    for legacy, canonical in EXPECTED_LEGACY_ALIASES.items():
        if aliases.get(legacy) != canonical:
            errors.append(f"missing legacy alias map {legacy} -> {canonical}")
    for forbidden in FORBIDDEN_LEGACY_ALIAS_KEYS:
        if forbidden in aliases:
            errors.append(f"raw zero name incorrectly listed as legacy representation alias: {forbidden}")

    for relative, required in REQUIRED_TEXT.items():
        text = files.get(relative)
        if text is None:
            errors.append(f"missing required file {relative}")
            continue
        for phrase in required:
            if phrase not in text:
                errors.append(f"{relative}: missing required phrase {phrase!r}")

    # Guard active source and the reader-facing registry against stale theorem
    # names.  Explanatory migration notes may quote retired names, and the
    # checker itself necessarily stores the denylist, so neither belongs in
    # this semantic-name scan.
    semantic_guard_paths = [
        relative
        for relative in files
        if relative.startswith("NativeCarryGeometry/")
        or relative == "audit/theorems.tsv"
        or relative == "docs/80_THEOREM_REGISTRY.md"
    ]
    for relative in semantic_guard_paths:
        lowered = files[relative].lower()
        for forbidden in FORBIDDEN_CURRENT_TEXT:
            if forbidden.lower() in lowered:
                errors.append(
                    f"{relative}: contains forbidden stale semantic text {forbidden!r}"
                )

    # Check malformed Unicode without embedding the replacement character in
    # the checker's own source, an impressively efficient way to accuse itself.
    replacement_character = chr(0xFFFD)
    for relative, file_text in files.items():
        if relative.startswith("scripts/migrate_zero_semantics"):
            continue
        if replacement_character in file_text:
            errors.append(f"{relative}: contains Unicode replacement character")

    try:
        rows = list(csv.DictReader(files["audit/theorems.tsv"].splitlines(), delimiter="\t"))
    except (KeyError, csv.Error) as exc:
        rows = []
        errors.append(f"invalid audit/theorems.tsv: {exc}")
    active = [
        row for row in rows
        if (row.get("status") or "active").strip().lower() not in {"retired", "reserved"}
    ]
    registry = {(row.get("id") or "").strip(): row for row in active}
    active_ids = set(registry)
    for theorem_id, (declaration, label) in REQUIRED_REGISTRY.items():
        row = registry.get(theorem_id, {})
        if row.get("declaration") != declaration:
            errors.append(f"registry declaration mismatch for {theorem_id}")
        if row.get("label") != label:
            errors.append(f"registry label mismatch for {theorem_id}")
        digest = row.get("type_sha256", "")
        if not re.fullmatch(r"[0-9a-f]{64}", digest):
            errors.append(f"registry digest missing for {theorem_id}")

    for artifact, key in (
        ("audit/theorem-registry.json", "theorems"),
        ("audit/axioms.json", "theorems"),
    ):
        try:
            payload = json.loads(files[artifact])
            artifact_ids = {str(item["id"]) for item in payload[key]}
            if artifact_ids != active_ids:
                errors.append(f"{artifact}: active ID set mismatch")
        except (KeyError, TypeError, json.JSONDecodeError) as exc:
            errors.append(f"invalid {artifact}: {exc}")

    preimage_ids = {
        Path(relative).stem
        for relative in files
        if relative.startswith("audit/preimages/") and relative.endswith(".txt")
    }
    if preimage_ids != active_ids:
        errors.append("audit/preimages ID set differs from active theorem registry")

    try:
        source_lock = json.loads(files["audit/source-lock.json"])
        if source_lock["registry"]["id_count"] != len(active_ids):
            errors.append("audit/source-lock.json registry count mismatch")
    except (KeyError, TypeError, json.JSONDecodeError) as exc:
        errors.append(f"invalid audit/source-lock.json: {exc}")

    sentinel = files.get(".release/v0.4.0.md")
    if sentinel != "publish-v0.4.0\nrequest=1\n":
        errors.append("historical v0.4.0 release sentinel changed")

    report = {
        "check": "semantic-contract-v2",
        "baseline_release": "v0.4.0",
        "files_checked": len(files),
        "active_theorem_ids": len(active_ids),
        "errors": sorted(set(errors)),
        "status": "pass" if not errors else "fail",
    }
    if args.report is not None:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    if errors:
        for error in sorted(set(errors)):
            print(f"ERROR: {error}")
        return 1
    print(
        f"PASS: semantic contract v2 across {len(files)} files and "
        f"{len(active_ids)} active theorem IDs"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
