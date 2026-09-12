#!/usr/bin/env python3
"""Independent direct-sum checks of the accelerated source at two corners.

This is a normalization and implementation cross-check, not coverage of the
boundary. The complete coverage proof is verify.py. No saved source values
are read: each original sum has all 690950 terms.
"""

import argparse
import json
from pathlib import Path
import time
from flint import arb, acb, ctx
from matrix import X, N, rational as Q, read_matrix, alpha, log_m0, horner, evaluate


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--matrix", type=Path, default=Path(__file__).parent / "data/matrix.txt")
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    if args.output and args.output.exists():
        raise SystemExit("Refuse to overwrite result")
    ctx.prec = 256
    extent, matrix = read_matrix(args.matrix)
    if extent != (1, N):
        raise ValueError("Wrong matrix range")
    started, results = time.monotonic(), []
    for ts, ys in [("0", "0"), ("1/5", "1")]:
        t, y = Q(ts), Q(ys)
        w = acb((1 + y) / 2, -arb(X) / 2)
        v = 1 - w
        aw, av = alpha(w), alpha(v)
        sb, sa = w + t * aw / 2, v + t * av / 2
        gamma = (log_m0(v) - log_m0(w) + t * (av * av - aw * aw) / 4).exp()
        primary, reflected = acb(0), acb(0)
        for n in range(1, N + 1):
            ell = arb(n).log()
            heat = t * ell * ell / 4
            primary += (heat - sb * ell).exp()
            reflected += (heat - sa * ell).exp()
        direct = primary + gamma * reflected
        fin = [horner(row, acb(t)) for row in matrix]
        fast = evaluate(fin, t, y)
        difference = abs(direct - fast)
        if not difference < Q("1e-12"):
            raise ArithmeticError(f"Direct source discrepancy at {(ts, ys)}: {difference}")
        results.append(
            {
                "t": ts,
                "y": ys,
                "terms_per_sum": N,
                "direct_source_real": direct.real.str(60, more=True),
                "direct_source_imag": direct.imag.str(60, more=True),
                "absolute_difference": difference.str(60, more=True),
            }
        )
        print(f"Direct source {(ts, ys)} agrees: {difference}", flush=True)
    result = {
        "complete": True,
        "scope": "two points only; full grid in verify.py",
        "bits": ctx.prec,
        "elapsed_seconds": time.monotonic() - started,
        "checks": results,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x") as f:
            json.dump(result, f, indent=2)
            f.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
