#!/usr/bin/env python3
"""Regenerate all 3844 matrix entries from their finite sums, retaining radii.

No historical matrix or numerical result is read. Requires gcc and libflint-dev.
The output is refused if it already exists. Temporary partitions are removed
after completion. The pinned generator computes at 192 bits; reduction uses 256.
"""

import argparse
import concurrent.futures
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import flint
from flint import arb, acb, ctx
from matrix import N, ORDER, read_matrix


def main():
    if sys.flags.optimize:
        raise SystemExit("Assertions must be enabled")
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--jobs", type=int, default=8)
    args = ap.parse_args()
    if args.output.exists() or not 1 <= args.jobs <= 32:
        raise SystemExit("Output must be new; jobs must be in 1..32")
    ctx.prec = 256
    started = time.monotonic()
    source = Path(__file__).with_name("generate-matrix.c")
    with tempfile.TemporaryDirectory(prefix="dbn-matrix-") as directory:
        tmp = Path(directory)
        binary = tmp / "generate-matrix"
        compile_command = [
            "gcc",
            "-O2",
            "-Wall",
            "-Wextra",
            "-o",
            str(binary),
            str(source),
            "-lflint",
            "-lgmp",
            "-lmpfr",
        ]
        subprocess.run(compile_command, check=True)
        partitions = [
            (1 + N * i // args.jobs, N * (i + 1) // args.jobs) for i in range(args.jobs)
        ]
        assert partitions[0][0] == 1 and partitions[-1][1] == N
        assert all(a[1] + 1 == b[0] for a, b in zip(partitions, partitions[1:]))

        def generate(item):
            i, (first, last) = item
            path = tmp / f"part-{i}.txt"
            subprocess.run([str(binary), str(first), str(last), str(path)], check=True)
            return path

        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            paths = list(pool.map(generate, enumerate(partitions)))
        total = [[acb(0) for _ in range(ORDER)] for _ in range(ORDER)]
        for path, expected in zip(paths, partitions):
            actual, part = read_matrix(path)
            if actual != expected:
                raise RuntimeError("Partition metadata mismatch")
            for e in range(ORDER):
                for k in range(ORDER):
                    total[e][k] += part[e][k]
        lines = ["5999347341500.5,345475,1,690950,62,62,192"]
        for row in total:
            entries = []
            for value in row:
                parts = [value.real.str(65, more=True), value.imag.str(65, more=True)]
                for text, ball in zip(parts, [value.real, value.imag]):
                    if not arb(text).contains(ball):
                        raise RuntimeError("Serialization lost enclosure")
                entries.append(" | ".join(parts))
            lines.append(" ; ".join(entries))
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x") as f:
            f.write("\n".join(lines) + "\n")
        result = {
            "complete": True,
            "terms": N,
            "entries": ORDER**2,
            "generator_bits": 192,
            "reduction_bits": ctx.prec,
            "generator_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "matrix_sha256": hashlib.sha256(args.output.read_bytes()).hexdigest(),
            "partitions": partitions,
            "elapsed_seconds": time.monotonic() - started,
            "compiler": subprocess.check_output(
                ["gcc", "--version"], text=True
            ).splitlines()[0],
            "python": sys.version,
            "python_flint": flint.__version__,
            "python_flint_backend": flint.__FLINT_VERSION__,
            "native_packages": subprocess.check_output(
                ["dpkg-query", "-W", "libflint-dev", "libgmp-dev", "libmpfr-dev"],
                text=True,
            ).splitlines(),
        }
        print(json.dumps(result, indent=2))
        with args.output.with_suffix(".provenance.json").open("x") as f:
            json.dump(result, f, indent=2)
            f.write("\n")


if __name__ == "__main__":
    main()
