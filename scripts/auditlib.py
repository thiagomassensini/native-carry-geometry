#!/usr/bin/env python3
"""Shared, dependency-free helpers for repository audits.

The checks in ``scripts/`` deliberately use only the Python standard library.
They run before Lean is installed in CI and therefore catch repository-shape
and source-policy regressions without trusting generated build products.
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, Iterable


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
PUBLIC_ROOT = REPOSITORY_ROOT / "NativeCarryGeometry.lean"
SOURCE_ROOT = REPOSITORY_ROOT / "NativeCarryGeometry"

PROJECT_MODULE_PREFIX = "NativeCarryGeometry"
NCG_ID_RE = re.compile(r"^NCG-[A-Z]{3}-[0-9]{3}$")


class AuditFailure(RuntimeError):
    """A deterministic repository audit failure."""


def lean_sources(repository_root: Path = REPOSITORY_ROOT) -> list[Path]:
    """Return every project Lean source in deterministic order."""

    public_root = repository_root / "NativeCarryGeometry.lean"
    source_root = repository_root / "NativeCarryGeometry"
    sources: list[Path] = []
    if public_root.is_file():
        sources.append(public_root)
    if source_root.is_dir():
        sources.extend(sorted(source_root.rglob("*.lean")))
    return sources


def module_name(path: Path, repository_root: Path = REPOSITORY_ROOT) -> str:
    """Convert a project source path to its Lean module name."""

    relative = path.resolve().relative_to(repository_root.resolve())
    if relative.suffix != ".lean":
        raise AuditFailure(f"not a Lean source: {relative}")
    return ".".join(relative.with_suffix("").parts)


def module_path(name: str, repository_root: Path = REPOSITORY_ROOT) -> Path:
    """Convert a project module name to its expected source path."""

    if not name or any(part in {"", ".", ".."} for part in name.split(".")):
        raise AuditFailure(f"invalid Lean module name: {name!r}")
    return repository_root.joinpath(*name.split(".")).with_suffix(".lean")


def strip_lean_comments_and_strings(source: str) -> str:
    """Mask Lean comments and strings while preserving offsets and newlines.

    Lean block comments nest.  Keeping source length unchanged lets callers
    associate a marker found in a doc comment with the next declaration in the
    masked code.  Double-quoted strings are masked too so policy words inside a
    string literal do not become false positives.
    """

    chars = list(source)
    result = list(source)
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False

    def mask(position: int) -> None:
        if result[position] not in "\r\n":
            result[position] = " "

    while index < len(chars):
        current = chars[index]
        following = chars[index + 1] if index + 1 < len(chars) else ""

        if in_line_comment:
            mask(index)
            if current in "\r\n":
                in_line_comment = False
            index += 1
            continue

        if block_depth:
            if current == "/" and following == "-":
                mask(index)
                mask(index + 1)
                block_depth += 1
                index += 2
                continue
            if current == "-" and following == "/":
                mask(index)
                mask(index + 1)
                block_depth -= 1
                index += 2
                continue
            mask(index)
            index += 1
            continue

        if in_string:
            mask(index)
            if escaped:
                escaped = False
            elif current == "\\":
                escaped = True
            elif current == '"':
                in_string = False
            index += 1
            continue

        if current == "-" and following == "-":
            mask(index)
            mask(index + 1)
            in_line_comment = True
            index += 2
            continue
        if current == "/" and following == "-":
            mask(index)
            mask(index + 1)
            block_depth = 1
            index += 2
            continue
        if current == '"':
            mask(index)
            in_string = True
            index += 1
            continue
        index += 1

    if block_depth:
        raise AuditFailure("unterminated Lean block comment")
    if in_string:
        raise AuditFailure("unterminated Lean string literal")
    return "".join(result)


IMPORT_LINE_RE = re.compile(r"(?m)^[ \t]*import[ \t]+([^\r\n]+)$")
MODULE_TOKEN_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")


def imports_in(path: Path) -> list[str]:
    """Extract imports from a Lean source after masking comments/strings."""

    source = path.read_text(encoding="utf-8")
    code = strip_lean_comments_and_strings(source)
    imports: list[str] = []
    for match in IMPORT_LINE_RE.finditer(code):
        tokens = match.group(1).split()
        for token in tokens:
            if not MODULE_TOKEN_RE.fullmatch(token):
                relative = path.relative_to(REPOSITORY_ROOT)
                raise AuditFailure(
                    f"{relative}: unsupported import syntax near {token!r}"
                )
            imports.append(token)
    return imports


def project_module_map(
    repository_root: Path = REPOSITORY_ROOT,
) -> dict[str, Path]:
    """Return the one-to-one project module map, rejecting collisions."""

    result: dict[str, Path] = {}
    for path in lean_sources(repository_root):
        name = module_name(path, repository_root)
        if name in result:
            raise AuditFailure(
                f"duplicate module {name}: "
                f"{result[name].relative_to(repository_root)} and "
                f"{path.relative_to(repository_root)}"
            )
        result[name] = path
    return result


def public_import_closure(
    repository_root: Path = REPOSITORY_ROOT,
) -> tuple[set[str], dict[str, list[str]], dict[str, Path]]:
    """Return modules reachable from the public audit root."""

    modules = project_module_map(repository_root)
    root_name = PROJECT_MODULE_PREFIX
    if root_name not in modules:
        raise AuditFailure("missing public root NativeCarryGeometry.lean")

    graph: dict[str, list[str]] = {}
    for name, path in modules.items():
        project_imports: list[str] = []
        for imported in imports_in(path):
            if imported == PROJECT_MODULE_PREFIX or imported.startswith(
                f"{PROJECT_MODULE_PREFIX}."
            ):
                if imported not in modules:
                    relative = path.relative_to(repository_root)
                    raise AuditFailure(
                        f"{relative}: project import {imported} has no source file"
                    )
                project_imports.append(imported)
        graph[name] = project_imports

    reached: set[str] = set()
    pending = [root_name]
    while pending:
        current = pending.pop()
        if current in reached:
            continue
        reached.add(current)
        pending.extend(graph[current])
    return reached, graph, modules


def relative_display(path: Path, repository_root: Path = REPOSITORY_ROOT) -> str:
    try:
        return str(path.resolve().relative_to(repository_root.resolve()))
    except ValueError:
        return str(path)


def write_report(path: Path | None, payload: dict[str, Any]) -> None:
    """Write a stable JSON report if requested."""

    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )


def fail_if_errors(errors: Iterable[str]) -> None:
    ordered = sorted(set(errors))
    if ordered:
        details = "\n".join(f"  - {item}" for item in ordered)
        raise AuditFailure(f"audit failed with {len(ordered)} error(s):\n{details}")
