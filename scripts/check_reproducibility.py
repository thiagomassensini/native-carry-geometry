#!/usr/bin/env python3
"""Verify the exact Lean/Mathlib lock used by the current release audit."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import tomllib
from pathlib import Path

from auditlib import (
    AuditFailure,
    REPOSITORY_ROOT,
    fail_if_errors,
    relative_display,
    write_report,
)


EXPECTED_PACKAGE_VERSION = "0.4.0"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.32.0"
EXPECTED_MATHLIB_INPUT_REV = "v4.32.0"
EXPECTED_MATHLIB_COMMIT = "81a5d257c8e410db227a6665ed08f64fea08e997"
FULL_SHA_RE = re.compile(r"^[0-9a-f]{40}$")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()

    errors: list[str] = []
    toolchain_path = REPOSITORY_ROOT / "lean-toolchain"
    lakefile_path = REPOSITORY_ROOT / "lakefile.toml"
    manifest_path = REPOSITORY_ROOT / "lake-manifest.json"

    for path in (toolchain_path, lakefile_path, manifest_path):
        if not path.is_file():
            errors.append(f"missing reproducibility lock: {relative_display(path)}")
    fail_if_errors(errors)

    raw_toolchain = toolchain_path.read_text(encoding="utf-8")
    toolchain = raw_toolchain.strip()
    if raw_toolchain != f"{toolchain}\n":
        errors.append("lean-toolchain must contain one LF-terminated line")
    if toolchain != EXPECTED_TOOLCHAIN:
        errors.append(
            f"lean-toolchain is {toolchain!r}; expected {EXPECTED_TOOLCHAIN!r}"
        )

    lakefile = tomllib.loads(lakefile_path.read_text(encoding="utf-8"))
    package_version = lakefile.get("version")
    if package_version != EXPECTED_PACKAGE_VERSION:
        errors.append(
            f"lakefile.toml package version is {package_version!r}; "
            f"expected {EXPECTED_PACKAGE_VERSION!r}"
        )
    requirements = lakefile.get("require", [])
    mathlib_requirements = [
        item for item in requirements if isinstance(item, dict) and item.get("name") == "mathlib"
    ]
    if len(mathlib_requirements) != 1:
        errors.append(
            "lakefile.toml must contain exactly one [[require]] entry for mathlib"
        )
    elif mathlib_requirements[0].get("rev") != EXPECTED_MATHLIB_INPUT_REV:
        errors.append(
            "lakefile.toml mathlib rev is "
            f"{mathlib_requirements[0].get('rev')!r}; "
            f"expected {EXPECTED_MATHLIB_INPUT_REV!r}"
        )

    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    packages = manifest.get("packages")
    if not isinstance(packages, list):
        errors.append("lake-manifest.json packages must be an array")
        packages = []

    package_names: set[str] = set()
    duplicate_packages: set[str] = set()
    for package in packages:
        if not isinstance(package, dict):
            errors.append("lake-manifest.json contains a non-object package")
            continue
        name = package.get("name")
        revision = package.get("rev")
        if not isinstance(name, str) or not name:
            errors.append("lake-manifest.json contains a package without a name")
            continue
        if name in package_names:
            duplicate_packages.add(name)
        package_names.add(name)
        if not isinstance(revision, str) or not FULL_SHA_RE.fullmatch(revision):
            errors.append(
                f"manifest package {name} is not locked to a full lowercase commit SHA"
            )
    for name in sorted(duplicate_packages):
        errors.append(f"duplicate manifest package: {name}")

    mathlib_packages = [
        package
        for package in packages
        if isinstance(package, dict) and package.get("name") == "mathlib"
    ]
    if len(mathlib_packages) != 1:
        errors.append("lake-manifest.json must contain exactly one mathlib package")
        mathlib_package: dict[str, object] = {}
    else:
        mathlib_package = mathlib_packages[0]
        if mathlib_package.get("inputRev") != EXPECTED_MATHLIB_INPUT_REV:
            errors.append(
                "manifest mathlib inputRev is "
                f"{mathlib_package.get('inputRev')!r}; "
                f"expected {EXPECTED_MATHLIB_INPUT_REV!r}"
            )
        if mathlib_package.get("rev") != EXPECTED_MATHLIB_COMMIT:
            errors.append(
                "manifest mathlib commit is "
                f"{mathlib_package.get('rev')!r}; expected {EXPECTED_MATHLIB_COMMIT}"
            )

    report = {
        "check": "reproducibility-lock",
        "expected": {
            "package_version": EXPECTED_PACKAGE_VERSION,
            "lean_toolchain": EXPECTED_TOOLCHAIN,
            "mathlib_input_rev": EXPECTED_MATHLIB_INPUT_REV,
            "mathlib_commit": EXPECTED_MATHLIB_COMMIT,
        },
        "observed": {
            "package_version": package_version,
            "lean_toolchain": toolchain,
            "mathlib_input_rev": mathlib_package.get("inputRev"),
            "mathlib_commit": mathlib_package.get("rev"),
            "package_count": len(packages),
        },
        "lock_sha256": {
            "lean-toolchain": sha256(toolchain_path),
            "lakefile.toml": sha256(lakefile_path),
            "lake-manifest.json": sha256(manifest_path),
        },
        "errors": sorted(set(errors)),
        "status": "pass" if not errors else "fail",
    }
    write_report(args.report, report)
    fail_if_errors(errors)
    print(
        "PASS: Lean v4.32.0 and mathlib "
        f"{EXPECTED_MATHLIB_COMMIT} are exactly locked"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AuditFailure, json.JSONDecodeError, tomllib.TOMLDecodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
