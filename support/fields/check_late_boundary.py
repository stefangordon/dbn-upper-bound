#!/usr/bin/env python3
"""Recompute the 117 late jet-boundary boxes from finite sums and analytic tails.

No saved value/derivative bounds are inputs.  This is the complete raw source
replay, including all nine cutoff bands on each physical circle.  It consumes
the exact geometry independently checked by check_fixed_c.py.
"""

import argparse, hashlib, json, time, sys
from pathlib import Path
from fractions import Fraction as F
from flint import arb, ctx
import flint
import late_core as core
import source

if not __debug__:
    raise RuntimeError("Run without Python optimization; assertions are proof gates.")
ap = argparse.ArgumentParser()
ap.add_argument("--start", type=int, default=45)
ap.add_argument("--stop", type=int, default=162)
ap.add_argument("--bits", type=int, default=512)
ap.add_argument("--out", "--output", type=Path, required=True)
args = ap.parse_args()
ctx.prec = args.bits
assert 45 <= args.start < args.stop <= 162 and args.bits >= 320
here = Path(__file__).resolve().parent
raw = (here / "data/boundary-geometry.json").read_bytes()
assert (
    hashlib.sha256(raw).hexdigest()
    == "e0026af966a3d56db00bfedbcca8f8762bea204b33ac7f4bec49c5284044d453"
)
g = json.loads(raw)
Q = core.Q
C = source.constants()
CW = dict(C, X=Q(g["x_wide_min"]))
assert F(g["x_center_min"]) == 5999346341500 and F(g["x_wide_min"]) == F(g["x_center_min"]) - F(
    1, 4
)
assert C["X"] - Q("1/2") > 4 * C["pi"] * C["N0"] ** 2 and C["X"] - Q("1/2") > C["Xe"]
bands = []
n = 690950
for _ in range(8):
    upper = 11 * n // 10
    bands.append([n, upper])
    n = upper + 1
bands.append([n, None])
assert bands == g["Nbands"] and n == 1481120
R = 100000
primes = (2, 3, 5, 7, 11)
beta = F(1)
T = C["T"]
pi = C["pi"]
logs = [arb(0)] + [arb(n).log() for n in range(1, R + 1)]


def st(x):
    return x.str(75, more=True)


def diskmod(t, yd):
    v = arb(1)
    for p in primes:
        l = logs[p]
        assert l < C["L"]
        v *= 1 + (t * l * l / 4 - ((1 + yd) / 2 + t * C["L"] / 4 - C["corr"]) * l).exp()
    return v


def C_lower(b):
    t0, t1, y = map(Q, (b["tlo"], b["thi"], b["center_yhi"]))
    u = arb(10**9)
    for l, a in zip((F(19, 4), F(97, 20), F(131, 20)), (1758974, 2464729, 302096)):
        l = Q(l)
        u += a * (l * l * t1).exp() * (l * y).cosh()
    return (t0 / 100000).exp() * (Q("8/25") + Q(1130000000000) / u)


rows = []
began = time.monotonic()
min_margin = None
for i in range(args.start, args.stop):
    b = g["boxes"][i]
    assert b["index"] == i
    assert F(b["tlo"]) == F(i, 1000) and F(b["thi"]) == min(F(i + 1, 1000), F(g["time_end"]))
    assert F(b["wide_ylo"]) == F(b["center_ylo"]) - F(1, 4)
    assert F(b["wide_yhi"]) == F(b["center_yhi"]) + F(1, 4)
    wb = dict(tlo=b["tlo"], thi=b["thi"], ylo=b["wide_ylo"], yhi=b["wide_yhi"], radius="3/20")
    cb = dict(wb, ylo=b["center_ylo"], yhi=b["center_yhi"])
    prep = core.prepare(wb, logs, R, primes)
    t = Q(prep["tl"])
    prep["radius"] = F(3, 20)
    prep["source"] = source.source_box(CW, **wb)
    prep["Mdisk"] = diskmod(t, Q(prep["yl"] - prep["radius"]))
    center = dict(
        prep,
        yl=F(cb["ylo"]),
        yh=F(cb["yhi"]),
        source=source.source_box(C, **cb),
        Mdisk=diskmod(t, Q(F(cb["ylo"]) - F(3, 20))),
    )
    wide = []
    Douter = None
    for lo, hi in bands:
        s = core.slab(CW, prep, logs, R, lo, hi, beta=beta)
        v = s["values"]
        D = v["D1"] + v["D2"] + v["source_derivative"]
        assert D >= 0 and D.is_finite()
        upper = D.upper()
        assert upper.rad() == 0
        Douter = upper if Douter is None or upper > Douter else Douter
        wide.append(dict(Nlo=lo, Nhi=hi, D=st(D)))
    assert Douter is not None
    floor = C_lower(b)
    centers = []
    for lo, hi in bands:
        s = core.slab(C, center, logs, R, lo, hi, beta=beta)
        v = s["values"]
        m = 1 - v["rpoint"]
        assert m > 0
        D = v["D1"] + v["D2"] + v["source_derivative"]
        xb = core.maxball(C["X"], 4 * pi * lo**2 - pi * T / 4)
        L = (xb / (4 * pi)).log()
        a1 = 1 / (xb - 6)
        a2 = 2 / xb**2 + 24 / xb**3
        a0 = L / 2 + pi / 4 + 5 / (xb - 6)
        s1 = (1 + T * a1 / 2) / 2
        s2 = T * a2 / 8
        b1 = (5 / (xb - 6) + T * a0 * a1 / 2) / 2
        b2 = (a1 + T * (a1 * a1 + a0 * a2) / 2) / 4
        sig = (1 + Q(center["yl"])) / 2 - C["Cmax"] - C["corr"] + t * arb(lo).log() / 2
        W0 = W1 = arb(0)
        for p in primes:
            l = logs[p]
            z = (t * l * l / 4 - sig * l).exp()
            assert 0 < z < 1
            W0 += l * z / (1 - z)
            W1 += l * l * z / (1 - z) ** 2
        E2 = s2 * W0 + s1 * s1 * W1
        J = b2 + E2 + 4 * Douter / m + (D / m) ** 2 + (v["Elog"] + D / m + b1) ** 2
        margin = floor - J
        assert margin > 0, (i, lo, st(margin))
        lower = margin.lower()
        assert lower.rad() == 0
        min_margin = lower if min_margin is None or lower < min_margin else min_margin
        centers.append(
            dict(Nlo=lo, Nhi=hi, m=st(m), D=st(D), J=st(J), C_lower=st(floor), margin=st(margin))
        )
    rows.append(dict(index=i, wide=wide, Douter=st(Douter), centers=centers))
    print(i, "minimum margin so far", st(min_margin), flush=True)
    result = dict(
        status="LATE_BOUNDARY_PARTIAL",
        completed=False,
        start=args.start,
        stop=i + 1,
        bits=ctx.prec,
        python=sys.version,
        python_flint=flint.__version__,
        R=R,
        primes=list(primes),
        Nbands=bands,
        geometry_sha256=hashlib.sha256(raw).hexdigest(),
        source="H7 3e-9/V7 envelope",
        minimum_margin=st(min_margin),
        rows=rows,
        seconds=time.monotonic() - began,
    )
    args.out.write_text(json.dumps(result, indent=2) + "\n")
assert len(rows) == args.stop - args.start
result.update(status="LATE_BOUNDARY_RANGE_PASS", completed=True)
args.out.write_text(json.dumps(result, indent=2) + "\n")
print("COMPLETE", args.start, args.stop, "seconds", round(time.monotonic() - began, 3), flush=True)
