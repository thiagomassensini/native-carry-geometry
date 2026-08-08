#!/usr/bin/env python3
"""Create the post-tag, non-self-referential release manifest."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

from auditlib import AuditFailure, REPOSITORY_ROOT


def git(*arguments: str) -> str:
    completed = subprocess.run(
        ["git", *arguments],
        cwd=REPOSITORY_ROOT,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    return completed.stdout.strip()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def artifact_entry(path: Path) -> dict[str, object]:
    return {
        "path": str(path.relative_to(REPOSITORY_ROOT)),
        "sha256": sha256(path),
        "bytes": path.stat().st_size,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tag", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--audit-artifact", type=Path, action="append", default=[])
    args = parser.parse_args()

    if args.tag not in {"v0.1.0", "v0.2.0", "v0.3.0", "v0.4.0"}:
        raise AuditFailure(
            "this publisher manifest is restricted to tags v0.1.0, v0.2.0, v0.3.0, and v0.4.0"
        )
    if git("status", "--porcelain"):
        raise AuditFailure("working tree is not clean before manifest generation")

    head_commit = git("rev-parse", "HEAD")
    tag_type = git("cat-file", "-t", args.tag)
    if tag_type != "tag":
        raise AuditFailure(f"{args.tag} is not an annotated tag object")
    tag_object = git("rev-parse", f"{args.tag}^{{tag}}")
    tag_commit = git("rev-parse", f"{args.tag}^{{commit}}")
    if head_commit != tag_commit:
        raise AuditFailure(
            f"tag {args.tag} resolves to {tag_commit}, but HEAD is {head_commit}"
        )

    tracked_candidates = [
        REPOSITORY_ROOT / relative
        for relative in git("ls-files").splitlines()
        if relative
    ]
    tracked_candidates.extend(args.audit_artifact)

    artifacts: list[dict[str, object]] = []
    seen: set[Path] = set()
    for candidate in tracked_candidates:
        path = candidate.resolve()
        if path in seen or not path.is_file():
            continue
        seen.add(path)
        try:
            path.relative_to(REPOSITORY_ROOT)
        except ValueError as error:
            raise AuditFailure(
                f"manifest artifact is outside repository: {path}"
            ) from error
        artifacts.append(artifact_entry(path))

    repository = os.environ.get("GITHUB_REPOSITORY", "")
    if not repository:
        raise AuditFailure("GITHUB_REPOSITORY is required")
    run_id = os.environ.get("GITHUB_RUN_ID", "")
    server_url = os.environ.get("GITHUB_SERVER_URL", "https://github.com")
    run_url = (
        f"{server_url}/{repository}/actions/runs/{run_id}" if run_id else None
    )

    payload = {
        "schema": "native-carry-geometry-release-manifest-v1",
        "release": {
            "tag": args.tag,
            "annotated_tag_object": tag_object,
            "commit": tag_commit,
            "tree": git("rev-parse", f"{tag_commit}^{{tree}}"),
            "repository": repository,
            "generated_at_utc": datetime.now(timezone.utc)
            .replace(microsecond=0)
            .isoformat()
            .replace("+00:00", "Z"),
            "workflow_run_id": run_id or None,
            "workflow_run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
            "workflow_run_url": run_url,
        },
        "artifacts": sorted(artifacts, key=lambda item: str(item["path"])),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(args.output)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AuditFailure, subprocess.CalledProcessError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        raise SystemExit(1)
