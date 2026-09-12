#!/usr/bin/env python3
"""Replay all 800000 closed cells on t in [0,1/5], y in [0,1], at x=X.

This computes the source polynomial on every cell, retaining all matrix radii.
It consumes check_bounds() for the unscaled source and Taylor error budgets.
The numerical result plus the analytic derivation proves H_t(X+iy) != 0.
It does not itself verify the cited finite-RH theorem or the homotopy argument.
"""

import argparse
import hashlib
import json
from pathlib import Path
import sys
import time
import flint
from flint import arb, acb, ctx
from bounds import check_bounds
from matrix import N, X, read_matrix, rational as Q, horner, evaluate


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--matrix", type=Path, default=Path(__file__).parent / "data/matrix.txt")
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    if sys.flags.optimize:
        raise SystemExit("Assertions must be enabled")
    if args.output and args.output.exists():
        raise SystemExit("Refuse to overwrite a result")
    started = time.monotonic()
    errors = check_bounds()
    ctx.prec = 192
    extent, matrix = read_matrix(args.matrix)
    assert extent == (1, N)
    threshold = Q("0.002000000001")
    worst, worst_cell, count = None, None, 0
    for i in range(400):
        t = arb(i).union(arb(i + 1)) / 2000
        assert t.contains(Q(f"{i}/2000")) and t.contains(Q(f"{i + 1}/2000"))
        fin = [horner(row, acb(t)) for row in matrix]
        for j in range(2000):
            y = arb(j).union(arb(j + 1)) / 2000
            assert y.contains(Q(f"{j}/2000")) and y.contains(Q(f"{j + 1}/2000"))
            modulus = abs(evaluate(fin, t, y))
            if not modulus > threshold:
                raise RuntimeError(f"Cell {(i, j)} failed: {modulus}")
            lower = modulus.lower()
            if worst is None:
                worst, worst_cell = lower, [i, j]
            else:
                if lower < worst:
                    worst_cell = [i, j]  # diagnostic location only
                worst = (worst + lower - abs(worst - lower)) / 2
            count += 1
        if (i + 1) % 50 == 0:
            print(f"{count}/800000 cells passed; {time.monotonic() - started:.1f}s", flush=True)
    assert count == 800000 and worst > threshold
    result = {
        "complete": True,
        "X": X,
        "t_interval": ["0", "1/5"],
        "y_interval": ["0", "1"],
        "denominator": 2000,
        "t_cells": 400,
        "y_cells": 2000,
        "passed": count,
        "gate": "abs(F_M)>0.002000000001 on every closed cell",
        "minimum_lower_enclosure": worst.str(60, more=True),
        "minimum_cell_diagnostic": worst_cell,
        "error_bounds": errors,
        "matrix_sha256": hashlib.sha256(args.matrix.read_bytes()).hexdigest(),
        "precision_bits": ctx.prec,
        "python_flint": flint.__version__,
        "flint_version": flint.__FLINT_VERSION__,
        "python": sys.version,
        "elapsed_seconds": time.monotonic() - started,
    }
    print(json.dumps(result, indent=2))
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x") as f:
            json.dump(result, f, indent=2)
            f.write("\n")


if __name__ == "__main__":
    main()
