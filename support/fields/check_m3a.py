#!/usr/bin/env python3
"""M3a initial cover, nonlocal bottom and height rows; Arb 512/Fraction."""

from pathlib import Path
from fractions import Fraction as F
from flint import arb, arb_series, ctx
import json, hashlib, sys, flint, argparse

if not __debug__:
    raise RuntimeError("Run without Python optimization; assertions are proof gates.")
ap = argparse.ArgumentParser()
ap.add_argument("--out", "--output", type=Path)
args = ap.parse_args()
ctx.prec = 512
HERE = Path(__file__).resolve().parent
ip = HERE / "data/m3a-initial.json"
hp = HERE.parents[1] / "certificate/data/old-M3a-wall.json"
expected = {
    ip: "7cade6075dcdd8b6783786209a29defe9b2352366494868c6832f072257f9d6b",
    hp: "e7c49c65b269da9a9d4f3611dad774c4e14c3df73d184581dfbac52c924a848b",
}
for p, h in expected.items():
    assert hashlib.sha256(p.read_bytes()).hexdigest() == h
ini = json.loads(ip.read_text())
height = json.loads(hp.read_text())
C = F(10**9)
LS = [F(95, 20), F(97, 20), F(131, 20)]
AA = [F(1758974), F(2464729), F(302096)]
h0 = F(1000001, 1000000)
qfinal = F(1, 400)
derate = F(1, 10**5)
target = F(817, 5000)
pa = height["parameters"]
assert (
    F(pa["C"]) == C and list(map(F, pa["lambdas"])) == LS and list(map(F, pa["coefficients"])) == AA
)
assert (
    F(pa["h0"]) == h0
    and F(pa["qfinal"]) == qfinal
    and F(pa["derating"]) == derate
    and F(pa["target"]) == target
)
assert pa["strict_delta"] == "exp(90t)/10^14"


def q(x):
    x = F(x)
    return arb(x.numerator) / x.denominator


def txt(v):
    return v.str(65, more=True)


def min_all(values):
    ans = values[0]
    for v in values[1:]:
        ans = (ans + v - abs(ans - v)) / 2
    return ans


def profile(t, y):
    u = q(C)
    uy = arb(0)
    for lam, coef in zip(LS, AA):
        z = (q(lam) * y).exp()
        inv = 1 / z
        heat = q(coef) * (q(lam * lam * t)).exp()
        u += heat * (z + inv) / 2
        uy += heat * q(lam) * (z - inv) / 2
    return uy / u


# Reconstruct stable R factors independently, using exponentials, no lead hyperbolic.
def factors(t, qq):
    hh = q(qq).sqrt()
    D = arb(0)
    V = arb(0)
    W = arb(0)
    E = arb(0)
    for lam, coef in zip(LS, AA):
        l = q(lam)
        arg = l * hh
        z = arg.exp()
        inv = 1 / z
        sc = (z - inv) / (2 * arg)
        ch = (z + inv) / 2
        a = q(coef) * q(lam * lam * t).exp()
        D += a * l**4 * sc**3
        V += a * ch
        W += a * l * l * sc
        E += a * l * l * ch * sc * sc
    return D, V, W, E


XL = q(5999346341500)
arch = (XL / (4 * arb.pi())).log() / 4 - q("1e-6")
assert 1 / (XL * XL) + 1 / (6 * XL - 36) < q("1e-6")


def euler(y):
    z = arb_series([q((1 + y) / 2), arb(1)], 2).zeta()
    return arch + z[1] / (2 * z[0])


# Initial cover includes sharp transfer leaves, not just direct Euler.
leaves = ini["leaves"]
assert len(leaves) == 855 and ini["strict_margin"] == "1/10000000"
prev = h0
initgaps = []
refs = []
eulers = 0
for leaf in leaves:
    lo, hi = h0, F(5)
    for b in leaf["path"]:
        assert b in "01"
        mid = (lo + hi) / 2
        if b == "0":
            hi = mid
        else:
            lo = mid
    assert (lo, hi) == (F(leaf["lo"]), F(leaf["hi"])) and lo == prev and lo < hi
    if leaf["method"] == "Euler":
        assert lo > 1
        bound = euler(lo)
        eulers += 1
    elif leaf["method"] == "sharp-pair-reference":
        v = F(leaf["v"])
        assert v >= hi and lo >= 1
        a = lo * lo + v * v - 6
        c = (lo * lo - 1) * (v * v - 1)
        assert a >= 0 or 4 * c >= a * a
        ev = euler(v)
        assert ev > 0
        bound = q(lo / v) * ev
        refs.append(str(v))
    else:
        raise AssertionError("unknown initial leaf method")
    gap = bound - profile(F(0), q(hi))
    assert gap > q("1e-7")
    initgaps.append(gap)
    prev = hi
assert prev == 5 and eulers == 851 and len(refs) == 4
assert sum(F(1, 2 ** len(row["path"])) for row in leaves) == 1
# Changed analytic constants are checked exactly.
mx = max(LS)
assert mx * mx == F(17161, 400)
assert 90 - 2 * mx * mx == F(839, 200) > 0 and 86 - 2 * mx * mx == F(39, 200) > 0
assert mx < F(659, 100) < 10
actual_delta = q("1e-14") * (90 * q("17/100")).exp()
assert actual_delta < q(derate)
# ALL exact affine height rows plus exact bottom partitions on that same trace.
t = F(0)
qq = h0 * h0
assert qq > 1
floors = []
bottoms = []
rowcount = 0
cellcount = 0
for row in height["rows"]:
    assert row["index"] == rowcount
    tl, tr, ql, qr, p, s, k = [F(row[n]) for n in ["tlo", "thi", "q_start", "q_end", "p", "s", "k"]]
    assert (tl, ql) == (t, qq) and 0 < tr - tl <= F(1, 10000)
    assert qfinal <= qr < ql and 0 < p <= 5 and p * p >= 5 * ql and 9 * ql <= 25
    assert s > 0 and k == 4 * s / p - 8 / (p * p - ql) and k > 0
    slope = (qr - ql) / (tr - tl)
    assert slope + 2 + k * qr >= 0
    gap = profile(tl, q(p)) - q(derate) - q(s)
    assert gap > 0
    floors.append(gap)
    cur = tl
    for cell in row["bottom"]:
        a, b, qa, qb = [F(cell[n]) for n in ["tlo", "thi", "q_start", "q_end"]]
        assert cur == a < b <= tr and qa == ql + slope * (a - tl) and qb == ql + slope * (b - tl)
        assert qr <= qb < qa <= ql
        dl, vl, _, _ = factors(a, qb)
        _, _, wh, eh = factors(b, qa)
        R = dl * (q(C) + vl) - 3 * wh * eh
        assert R > 0
        bottoms.append(R)
        cur = b
        cellcount += 1
    assert cur == tr and row["bottom"]
    t, qq = tr, qr
    rowcount += 1
assert rowcount == 1620 and cellcount == 1620 == height["bottom_cells"] and qq == qfinal
terminal = t + qfinal / 2
assert t == F(height["terminal"]["time"]) and terminal == F(height["terminal"]["Lambda_exact"])
assert terminal == F(
    10806782277448234760467365768160782302951, 66207211195936838001560220771250000000000
)
assert terminal < target < F(17, 100)
out = {
    "status": "M3A_INITIAL_BOTTOM_AND_HEIGHT_GATES_PASS",
    "precision_bits": ctx.prec,
    "python": sys.version,
    "python_flint": flint.__version__,
    "initial_leaves": len(leaves),
    "Euler_leaves": eulers,
    "sharp_references": refs,
    "initial_minimum": txt(min_all(initgaps)),
    "height_rows": rowcount,
    "bottom_cells": cellcount,
    "height_floor_minimum": txt(min_all(floors)),
    "bottom_R_minimum": txt(min_all(bottoms)),
    "actual_delta_max": txt(actual_delta),
    "T_exact": str(t),
    "Lambda_exact": str(terminal),
    "Lambda_ball": txt(q(terminal)),
    "rational_upper": "817/5000",
    "input_hashes": {p.relative_to(HERE.parents[1]).as_posix(): h for p, h in expected.items()},
    "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
if args.out:
    args.out.write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
