#!/usr/bin/env python3
"""Audit the repository-wide one-native-operator semantic contract."""

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
    "different zero predicates": (
        "state that there is one native operator-zero predicate and that "
        "coordinate presentations define the same zero locus"
    ),
    "one native zero": "say one native operator-zero predicate",
    "one operator zero": "say one native operator-zero predicate",
    "one boundary zero": "say native operator-zero predicate",
    "same native zero": "say the same native operator-zero locus",
    "unique native zero": "say the one native operator-zero predicate",
    "zero species": "distinguish predicates, loci, and chart relations directly",
    "different kinds of zero": "say no additional operator-zero predicate",
    "another operator zero": "say an additional operator-zero predicate",
}

LEGACY_NAMES = {
    "IsFiniteRealCarryOperatorZero",
    "IsRealCarryOperatorZero",
    "IsNativeRealCarryOperatorZero",
    "IsNativeCanonicalCarryOperatorZero",
    "IsCanonicalCarryOperatorZero",
    "IsRadialDeformationPresentationZero",
    "BoundaryConvergesToZero",
    "RealCarryEnergyCompatible",
    "finiteRealCarryOperator",
    "realCarryState",
    "massWeight",
    "criticalAmplitude",
}

REQUIRED_TEXT = {
    "README.md": [
        "Mass comes before the operator",
        "Sigma is a quadratic-norm deformation coordinate",
        "There is one native operator-zero predicate",
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
        "One native operator-zero predicate",
        "Ambient chart cancellation and native representation",
    ],
    "docs/60_REAL_ANALYTIC_EQUIVALENCE.md": [
        "Real–Analytic Identity of the Same Operator",
        "There is no “real zero” and “complex zero”",
    ],
    "docs/70_ZERO_SET_FACTORIZATION.md": [
        "One Native Operator-Zero Predicate and Radial-Chart Representation",
        "Historical aliases",
    ],
    "docs/80_THEOREM_REGISTRY.md": [
        "Release `v0.4.0` designates 75",
        "NCG-EQV-017",
    ],
    "audit/README.md": [
        "Release `v0.4.0` contains 75",
        "One native operator-zero predicate",
    ],
    "lakefile.toml": ['version = "0.4.0"'],
    "CITATION.cff": ["version: 0.4.0"],
    ".zenodo.json": ['"version": "0.4.0"'],
    ".github/workflows/publish-v0.4.0.yml": [
        "RELEASE_TAG: v0.4.0",
        "publish-v0.4.0",
        "one native operator-zero predicate",
    ],
}

EXPECTED_CONTRACT_STATEMENTS = {
    "REAL_COMPLEX_SAME_OPERATOR": (
        "Real pairs and complex numbers are faithful additive coordinates of "
        "the same state and resultants and define the same zero locus."
    ),
    "ONE_OPERATOR_ZERO": (
        "The native carry operator has one native operator-zero predicate, "
        "already built from the mass-weighted tower."
    ),
    "AMBIENT_CANCELLATION_NOT_ZERO": (
        "Ambient chart cancellation is distinguished from the relation that "
        "a chart point represents a point of the native operator-zero locus."
    ),
}

EXPECTED_LEGACY_ALIASES = {
    "NativeCarryGeometry.Measure.criticalAmplitude":
        "NativeCarryGeometry.Measure.carryAmplitude",
    "NativeCarryGeometry.Measure.massWeight":
        "NativeCarryGeometry.Measure.radialEnergyWeight",
    "NativeCarryGeometry.Operator.realCarryState":
        "NativeCarryGeometry.Operator.radialDeformationState",
    "NativeCarryGeometry.Operator.RealCarryEnergyCompatible":
        "NativeCarryGeometry.Operator.RadialDeformationRepresentsNativeMass",
    "NativeCarryGeometry.Operator.finiteRealCarryOperator":
        "NativeCarryGeometry.Operator.finiteRadialDeformation",
    "NativeCarryGeometry.Operator.BoundaryConvergesToZero":
        "NativeCarryGeometry.Operator.RadialChartCancelsAt",
    "NativeCarryGeometry.Operator.IsRadialDeformationPresentationZero":
        "NativeCarryGeometry.Operator.RadialChartRepresentsNativeZero",
    "NativeCarryGeometry.Operator.IsFiniteRealCarryOperatorZero":
        "NativeCarryGeometry.Operator.RadialChartRepresentsFiniteNativeZero",
    "NativeCarryGeometry.Operator.IsRealCarryOperatorZero":
        "NativeCarryGeometry.Operator.RadialChartRepresentsNativeZero",
    "NativeCarryGeometry.Operator.IsNativeRealCarryOperatorZero":
        "NativeCarryGeometry.Operator.IsNativeCarryOperatorZero",
    "NativeCarryGeometry.Equivalence.IsCanonicalCarryOperatorZero":
        "NativeCarryGeometry.Equivalence.AnalyticChartRepresentsNativeZero",
    "NativeCarryGeometry.Equivalence.IsNativeCanonicalCarryOperatorZero":
        "NativeCarryGeometry.Operator.IsNativeCarryOperatorZero",
}

REQUIRED_REGISTRY_LABELS = {
    "NCG-ANL-008":
        "Odd-Prime Camera Ambient Chart-Cancellation Locus Identity",
    "NCG-EQV-004":
        "Finite Resultant Coordinate Zero-Locus Identity",
    "NCG-EQV-007":
        "Camera-Three Real/Analytic Chart-Cancellation Locus Identity",
    "NCG-EQV-010":
        "Native Finite Resultant Coordinate Zero-Locus Identity",
    "NCG-EQV-011":
        "Native Boundary/Analytic Readout Zero-Locus Identity",
    "NCG-EQV-012":
        "Legacy Coordinate-Labelled Native Operator Zero-Locus Identity",
    "NCG-EQV-017":
        "Native Operator/Analytic Readout Zero-Locus Identity",
    "NCG-OPR-007":
        "Canonical Radial-Chart Native Representation Factorization",
    "NCG-OPR-008":
        "Canonical Finite Radial-Chart Native Representation Factorization",
    "NCG-REA-004":
        "Native State Carry-Mass Energy",
}

FORBIDDEN_REGISTRY_LABELS = {
    "Finite Zero-Set Equivalence",
    "Finite Real/Analytic Operator Identity",
    "Camera-Three Boundary/Continuation Zero Equivalence",
    "One Native Operator Zero Analytic Identity",
    "Native State Inverse-Mass Energy",
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
        if semantic_contract.get("release") != "v0.4.0":
            errors.append("audit/semantic-contract.json release must be v0.4.0")
    except (KeyError, json.JSONDecodeError) as error:
        errors.append(f"invalid audit/semantic-contract.json: {error}")
        semantic_contract = {"contracts": []}

    contracts_by_id = {
        str(contract.get("id")): contract
        for contract in semantic_contract.get("contracts", [])
    }
    for contract_id, expected_statement in EXPECTED_CONTRACT_STATEMENTS.items():
        actual = contracts_by_id.get(contract_id, {}).get("statement")
        if actual != expected_statement:
            errors.append(
                f"audit/semantic-contract.json: statement mismatch for "
                f"{contract_id}"
            )
    legacy_aliases = semantic_contract.get("legacy_aliases", {})
    for legacy, canonical in EXPECTED_LEGACY_ALIASES.items():
        if legacy_aliases.get(legacy) != canonical:
            errors.append(
                f"audit/semantic-contract.json: missing canonical map "
                f"{legacy} -> {canonical}"
            )

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
    for theorem_id, expected_label in REQUIRED_REGISTRY_LABELS.items():
        actual_label = (registry_by_id.get(theorem_id, {}).get("label") or "").strip()
        if actual_label != expected_label:
            errors.append(
                f"audit/theorems.tsv: label mismatch for {theorem_id}"
            )
    for theorem_id, row in registry_by_id.items():
        label = (row.get("label") or "").strip()
        if label in FORBIDDEN_REGISTRY_LABELS:
            errors.append(
                f"audit/theorems.tsv: legacy-ambiguous label for "
                f"{theorem_id}: {label}"
            )
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
            if artifact == "audit/theorem-registry.json":
                artifact_by_id = {
                    str(item["id"]): item for item in payload[key]
                }
                for theorem_id, row in registry_by_id.items():
                    generated = artifact_by_id.get(theorem_id, {})
                    for field in ("declaration", "label", "type_sha256"):
                        if str(generated.get(field, "")).strip() != (
                            row.get(field) or ""
                        ).strip():
                            errors.append(
                                f"{artifact}: {field} mismatch for {theorem_id}"
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

    if by_relative.get(".release/v0.4.0.md") != (
        "publish-v0.4.0\nrequest=1\n"
    ):
        errors.append("invalid immutable release sentinel .release/v0.4.0.md")

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
            narrative = re.sub(r"```.*?```", "", text, flags=re.DOTALL)
            if re.search(r"(?m)^\s*[\[\]]\s*$", narrative):
                errors.append(
                    f"{relative}: bare bracket used as a math delimiter"
                )
            display_delimiter = "$" * 2
            if narrative.count(display_delimiter) % 2:
                errors.append(f"{relative}: unbalanced display-math delimiters")
            if narrative.count(r"\[") != narrative.count(r"\]"):
                errors.append(f"{relative}: unbalanced \\[ / \\] delimiters")
            without_displays = narrative.replace(display_delimiter, "")
            inline_dollars = re.findall(r"(?<!\\)\$", without_displays)
            if len(inline_dollars) % 2:
                errors.append(f"{relative}: unbalanced inline math delimiters")
            if re.search(r"(?<=[0-9)}\]])iff\b", narrative):
                errors.append(
                    f"{relative}: possible lost TeX escape before 'iff'"
                )
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
        "check": "one-native-operator-semantic-contract",
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
        "PASS: one-native-operator semantic contract; "
        f"{len(files)} versioned text files inspected"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
