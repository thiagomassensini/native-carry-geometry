#!/usr/bin/env python3
"""Audit the repository-wide one-operator semantic contract."""

from __future__ import annotations

import argparse
import json
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
        if "�" in text or "â" in text:
            errors.append(f"{relative}: broken Unicode encoding marker")

    payload = {
        "check": "one-operator-semantic-contract",
        "files_inspected": len(files),
        "public_narratives_inspected": len(PUBLIC_NARRATIVE),
        "required_contract_files": len(REQUIRED_TEXT),
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
