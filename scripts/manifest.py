#!/usr/bin/env python3
"""Write or verify the release file inventory. Hashes identify bytes, not proofs."""

import argparse
import hashlib
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = "MANIFEST.json"
EXCLUDED = {
    ".git",
    ".lake",
    ".venv",
    ".ruff_cache",
    ".pytest_cache",
    "__pycache__",
    "build",
    "tmp",
    "dist",
}
EXTENSIONS = {
    ".md",
    ".py",
    ".c",
    ".json",
    ".txt",
    ".lean",
    ".toml",
    ".yml",
    ".yaml",
    ".bib",
    ".tex",
    ".sty",
    ".lock",
}
SPECIAL = {
    ".gitignore",
    ".dockerignore",
    "lean-toolchain",
    "Dockerfile",
    "Makefile",
    "LICENSE",
    "NOTICE",
}


def release_files(root=ROOT):
    files = []
    for directory, directories, names in os.walk(root):
        directories[:] = sorted(name for name in directories if name not in EXCLUDED)
        for name in directories + names:
            path = Path(directory) / name
            relative = path.relative_to(root)
            if path.is_symlink():
                raise ValueError(f"release must contain ordinary files, not symlinks: {relative}")
        for name in names:
            path = Path(directory) / name
            relative = path.relative_to(root)
            if relative.as_posix() == MANIFEST:
                continue
            if (
                path.suffix in EXTENSIONS
                or path.name in SPECIAL
                or relative.as_posix() == "output/pdf/dbn-upper-bound.pdf"
            ):
                files.append(relative.as_posix())
            elif path.name not in {".DS_Store"} and path.suffix not in {".pyc", ".pyo", ".png"}:
                raise ValueError(f"unclassified release file: {relative}")
    return sorted(files)


def inventory(root=ROOT):
    return {
        name: {
            "sha256": hashlib.sha256((root / name).read_bytes()).hexdigest(),
            "bytes": (root / name).stat().st_size,
        }
        for name in release_files(root)
    }


def verify(root=ROOT):
    saved = json.loads((root / MANIFEST).read_text())
    actual = inventory(root)
    if saved.get("schema_version") != 1:
        raise ValueError("unsupported manifest schema")
    expected = saved["entries"]
    changed = [
        name
        for name in sorted(set(actual) | set(expected))
        if actual.get(name) != expected.get(name)
    ]
    if changed:
        raise ValueError("release inventory mismatch: " + ", ".join(changed))
    return len(actual)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write",
        action="store_true",
        help="explicitly replace the manifest with the current inventory",
    )
    args = parser.parse_args()
    try:
        if args.write:
            entries = inventory()
            result = dict(
                schema_version=1,
                publication="dbn-lambda-upper-bound",
                bound="3885632262767861213460393068710302759/24646172707879668706230182733520000000",
                entries=entries,
            )
            (ROOT / MANIFEST).write_text(json.dumps(result, indent=2) + "\n")
            print(f"Wrote manifest for {len(entries)} files.")
        else:
            print(f"PASS: {verify()} release files match their recorded hashes and sizes.")
    except (ValueError, KeyError, OSError) as error:
        parser.exit(1, f"FAIL: {error}\n")


if __name__ == "__main__":
    main()
