#!/usr/bin/env python3
"""Audit the repository-wide one-operator semantic contract."""

from __future__ import annotations

import argparse
import csv
import json
import re
from pathlib import Path

from auditlib import REPOSITORY_ROOT


EXCLUDED_PARTS = {".git", ".lake", "__pycache__"}
PUBLIC_NARRATIVE = {
    REPOSITORY_ROOT / "README.md",
    REPOSITORY_ROOT / "audit" / "README.md",
    REPOSITORY_ROOT / "CITATION.cff",
    REPOSITORY_ROOT / ".zenodo.json",
}
PUBLIC_NARRATIVE.update((REPOSITORY_ROOT / "docs").glob("*.md"))

FORBIDDEN_PUBLIC_PHRASES = {
    "scalar zero": (
        "describe this as ambient analytic-chart cancellation or the native "
        "analytic readout"
    ),
    "mass injection": "state that mass is constructed upstream",
    "full analytic zero predicate": "use AnalyticChartRepresentsNativeZero",
    "complete analytic operator predicate": "use a chart-representation relation",
    "different zero predicates": "state the one native zero and its coordinates",
}

LEGACY_NAMES = {
    "IsFiniteRealCarryOperatorZero",
    "IsRealCarryOperatorZero",
    "IsNativeRealCarryOperatorZero",
    "IsNativeCanonicalCarryOperatorZero",
    "IsCanonicalCarryOperatorZero",
}

REQUIRED_TEXT = {
    "README.md": [
        "Mass comes before the operator",
        "Sigma is a quadratic-norm deformation coordinate",
        "There is one operator-zero predicate",
        "IsNativeCarryOperatorZero",
        "RadialChartCancelsAt",
        "RadialChartRepresentsNativeZero",
    ],
    "NativeCarryGeometry/Measure/CarryMass.lean": [
        "nativeTowerAmplitude_sq_eq_mass",
        "radialEnergyWeight",
    ],
    "NativeCarryGeometry/Operator/RealState.lean": [
        "quadraticEnergy_radialDeformationState",
        "radialDeformationRepresentsNativeMass_iff",
    ],
    "NativeCarryGeometry/Operator/BoundaryOperator.lean": [
        "RadialChartCancelsAt",
        "not a second zero predicate",
    ],
    "NativeCarryGeometry/Operator/ZeroSetFactorization.lean": [
        "IsNativeCarryOperatorZero",
        "RadialChartRepresentsNativeZero",
        "radialChartRepresentsNativeZero_iff",
    ],
    "NativeCarryGeometry/Equivalence/ComplexCoordinates.lean": [
        "normSq_complexCoordinates_radialDeformationState",
        "normSq_complexCoordinates_nativeRealCarryState",
        "radialComplexNormRepresentsNativeMass_iff",
    ],
    "NativeCarryGeometry/Equivalence/RealAnalyticBoundary.lean": [
        "normSq_powerMonomial_canonicalParameter",
        "isNativeCarryOperatorZero_iff_analyticReadout_eq_zero",
        "AnalyticChartRepresentsNativeZero",
        "analyticChartRepresentsNativeZero_iff",
    ],
    "docs/00_SCOPE.md": [
        "One operator and one zero",
        "Ambient chart cancellation and native representation",
    ],
    "docs/60_REAL_ANALYTIC_EQUIVALENCE.md": [
        "Real–Analytic Identity of the Same Operator",
        "There is no “real zero” and “complex zero”",
    ],
    "docs/70_ZERO_SET_FACTORIZATION.md": [
        "One Native Zero and Radial-Chart Representation",
        "Historical aliases",
    ],
    "docs/80_THEOREM_REGISTRY.md": [
        "Release `v0.3.0` designates 75",
        "NCG-EQV-017",
    ],
    "audit/README.md": [
        "Release `v0.3.0` contains 75",
        "One operator zero",
    ],
    "lakefile.toml": ['version = "0.3.0"'],
    "CITATION.cff": ["version: 0.3.0"],
    ".zenodo.json": ['"version": "0.3.0"'],
    ".github/workflows/publish-v0.3.0.yml": [
        "RELEASE_TAG: v0.3.0",
        "publish-v0.3.0",
    ],
}


def versioned_text_files() -> tuple[list[Path], list[str]]:
    files: list[Path] = []
    errors: list[str] = []
    for path in sorted(REPOSITORY_ROOT.rglob("*")):
        if not path.is_file() or any(part in EXCLUDED_PARTS for part in path.parts):
            continue
        try:
            path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            # No binary artifact is expected in the committed audit root.
            errors.append(f"{path.relative_to(REPOSITORY_ROOT)} is not UTF-8 text")
            continue
        files.append(path)
    return files, errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()

    files, errors = versioned_text_files()
    by_relative = {
        str(path.relative_to(REPOSITORY_ROOT)): path.read_text(encoding="utf-8")
        for path in files
    }

    try:
        semantic_contract = json.loads(
            by_relative["audit/semantic-contract.json"]
        )
        if semantic_contract.get("release") != "v0.3.0":
            errors.append("audit/semantic-contract.json release must be v0.3.0")
    except (KeyError, json.JSONDecodeError) as error:
        errors.append(f"invalid audit/semantic-contract.json: {error}")
        semantic_contract = {"contracts": []}

    try:
        registry_rows = list(
            csv.DictReader(
                by_relative["audit/theorems.tsv"].splitlines(),
                delimiter="\t",
            )
        )
    except (KeyError, csv.Error) as error:
        errors.append(f"invalid audit/theorems.tsv: {error}")
        registry_rows = []

    active_rows = [
        row
        for row in registry_rows
        if (row.get("status") or "active").strip().lower()
        not in {"retired", "reserved"}
    ]
    registry_by_id = {(row.get("id") or "").strip(): row for row in active_rows}
    active_ids = set(registry_by_id)
    for contract in semantic_contract.get("contracts", []):
        contract_id = contract.get("id", "<missing>")
        for witness in contract.get("witness_ids", []):
            row = registry_by_id.get(witness)
            if row is None:
                errors.append(
                    f"semantic contract {contract_id}: missing witness {witness}"
                )
                continue
            digest = (row.get("type_sha256") or "").strip()
            if not re.fullmatch(r"[0-9a-f]{64}", digest):
                errors.append(
                    f"semantic contract {contract_id}: witness {witness} "
                    "has no generated type digest"
                )

    for artifact, key in (
        ("audit/theorem-registry.json", "theorems"),
        ("audit/axioms.json", "theorems"),
    ):
        try:
            payload = json.loads(by_relative[artifact])
            artifact_ids = {
                str(item["id"]) for item in payload[key]
            }
            if artifact_ids != active_ids:
                errors.append(
                    f"{artifact}: ID set differs from audit/theorems.tsv"
                )
        except (KeyError, TypeError, json.JSONDecodeError) as error:
            errors.append(f"invalid generated artifact {artifact}: {error}")

    preimage_ids = {
        Path(relative).stem
        for relative in by_relative
        if relative.startswith("audit/preimages/") and relative.endswith(".txt")
    }
    if preimage_ids != active_ids:
        errors.append(
            "audit/preimages ID set differs from audit/theorems.tsv"
        )

    try:
        source_lock = json.loads(by_relative["audit/source-lock.json"])
        if source_lock["registry"]["id_count"] != len(active_ids):
            errors.append(
                "audit/source-lock.json registry.id_count differs from "
                "the active theorem count"
            )
    except (KeyError, TypeError, json.JSONDecodeError) as error:
        errors.append(f"invalid audit/source-lock.json: {error}")

    if by_relative.get(".release/v0.3.0.md") != (
        "publish-v0.3.0\nrequest=1\n"
    ):
        errors.append("invalid immutable release sentinel .release/v0.3.0.md")

    for relative, required in REQUIRED_TEXT.items():
        text = by_relative.get(relative)
        if text is None:
            errors.append(f"missing semantic-contract file {relative}")
            continue
        for phrase in required:
            if phrase not in text:
                errors.append(f"{relative}: missing contract phrase {phrase!r}")

    for path in sorted(PUBLIC_NARRATIVE):
        if not path.is_file():
            errors.append(f"missing public narrative {path.relative_to(REPOSITORY_ROOT)}")
            continue
        text = path.read_text(encoding="utf-8")
        lowered = text.lower()
        for phrase, replacement in FORBIDDEN_PUBLIC_PHRASES.items():
            if phrase in lowered:
                errors.append(
                    f"{path.relative_to(REPOSITORY_ROOT)}: forbidden phrase "
                    f"{phrase!r}; {replacement}"
                )
        present_legacy = sorted(name for name in LEGACY_NAMES if name in text)
        if present_legacy and "legacy" not in lowered:
            errors.append(
                f"{path.relative_to(REPOSITORY_ROOT)}: legacy API name(s) "
                f"{', '.join(present_legacy)} appear without an explicit "
                "legacy-compatibility notice"
            )

    for relative, text in by_relative.items():
        if "\uFFFD" in text or "\u00e2\u0084" in text:
            errors.append(f"{relative}: broken Unicode encoding marker")
        allowed_controls = "\n"
        if relative == "audit/theorems.tsv":
            allowed_controls += "\t"
        controls = sorted(
            {ord(char) for char in text
             if ord(char) < 32 and char not in allowed_controls}
        )
        if controls:
            errors.append(
                f"{relative}: forbidden control character code(s) "
                + ", ".join(str(code) for code in controls)
            )
        if relative.endswith(".md"):
            lost_tex_patterns = (
                (r"(?<!\\)operatorname\{", "operatorname{"),
                (r"(?<!\\)mathbb\{", "mathbb{"),
                (r"(?<!\\)frac\{", "frac{"),
                (
                    r"(?<!\\)(?:qquad|longrightarrow|simeq)(?![A-Za-z])",
                    "standalone TeX command",
                ),
            )
            for pattern, token in lost_tex_patterns:
                if re.search(pattern, text):
                    errors.append(
                        f"{relative}: possible lost TeX escape before {token!r}"
                    )

    payload = {
        "check": "one-operator-semantic-contract",
        "files_inspected": len(files),
        "public_narratives_inspected": len(PUBLIC_NARRATIVE),
        "required_contract_files": len(REQUIRED_TEXT),
        "registered_theorems": len(active_ids),
        "semantic_contracts": len(semantic_contract.get("contracts", [])),
        "errors": sorted(set(errors)),
        "status": "pass" if not errors else "fail",
    }
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    if errors:
        for error in sorted(set(errors)):
            print(f"ERROR: {error}")
        return 1
    print(
        "PASS: one-operator semantic contract; "
        f"{len(files)} versioned text files inspected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
