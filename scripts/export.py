#!/usr/bin/env python3
"""Export a verified standalone repository, excluding caches and research history."""

import argparse
import importlib.util
import json
from pathlib import Path
import shutil
import tarfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("dbn_manifest", HERE / "manifest.py")
manifest = importlib.util.module_from_spec(spec)
spec.loader.exec_module(manifest)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path, help="new directory; existing paths are refused")
    parser.add_argument("--archive", type=Path, help="optional new .tar.gz archive")
    args = parser.parse_args()
    destination = args.destination.resolve()
    try:
        if args.archive:
            archive_path = args.archive.resolve()
            if archive_path == destination or destination in archive_path.parents:
                raise ValueError("place the archive beside the exported directory, not inside it")
            if archive_path == manifest.ROOT or manifest.ROOT in archive_path.parents:
                raise ValueError("write the archive outside the source repository")
        count = manifest.verify()
        if destination.exists() or (args.archive and args.archive.exists()):
            raise ValueError("destination and optional archive must not exist")
        if destination == manifest.ROOT or manifest.ROOT in destination.parents:
            raise ValueError("export outside the source directory")
        destination.mkdir(parents=True)
        names = manifest.release_files() + ["MANIFEST.json"]
        for name in names:
            target = destination / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(manifest.ROOT / name, target)
        manifest.verify(destination)
        if args.archive:
            args.archive.parent.mkdir(parents=True, exist_ok=True)
            with tarfile.open(args.archive, "x:gz") as archive:
                for name in sorted(names):
                    archive.add(
                        destination / name,
                        arcname="dbn-lambda-upper-bound/" + name,
                        recursive=False,
                    )
        print(
            json.dumps(
                dict(
                    directory=str(destination),
                    files=count + 1,
                    archive=str(args.archive) if args.archive else None,
                ),
                indent=2,
            )
        )
    except (ValueError, KeyError, OSError) as error:
        parser.exit(1, f"FAIL: {error}\n")


if __name__ == "__main__":
    main()
