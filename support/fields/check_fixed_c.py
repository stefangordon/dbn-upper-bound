"""Fixed-C initial, interior, top, head and boundary-geometry gates (Arb 512)."""

from pathlib import Path
from fractions import Fraction as F
from bisect import bisect_right
import json, hashlib, platform, time, argparse
from flint import arb, arb_series, ctx
import flint

if not __debug__:
    raise RuntimeError("Run without Python optimization; assertions are proof gates.")
ap = argparse.ArgumentParser()
ap.add_argument("--out", "--output", type=Path)
args = ap.parse_args()
ctx.prec = 512
ctx.cap = 3
HERE = Path(__file__).resolve().parent
HP = HERE.parents[1] / "certificate/data/old-M3a-wall.json"
assert (
    hashlib.sha256(HP.read_bytes()).hexdigest()
    == "e7c49c65b269da9a9d4f3611dad774c4e14c3df73d184581dfbac52c924a848b"
)
geompath = HERE / "data/boundary-geometry.json"
assert (
    hashlib.sha256(geompath.read_bytes()).hexdigest()
    == "e0026af966a3d56db00bfedbcca8f8762bea204b33ac7f4bec49c5284044d453"
)
hb = json.loads(HP.read_text())
oldrows = hb["rows"]
tau = F(hb["terminal"]["time"])
geo = json.loads(geompath.read_text())
A = lambda q: arb(F(q).numerator) / F(q).denominator
st = lambda z: z.str(85, more=True)
mx = lambda a, b: (a + b + abs(a - b)) / 2
mn = lambda a, b: (a + b - abs(a - b)) / 2
Xe = F(5900000000000)
XL = F(5999346341500)
X = F(5999347341500)
Tm = F(1, 5)
ctop = F(8, 25)
bigA = F(1130000000000)
kap = F(1, 100000)
K = F(1000000)
ls = (F(19, 4), F(97, 20), F(131, 20))
aa = (1758974, 2464729, 302096)
lam = max(ls)


def U(t, y):
    # Independent exponential evaluator rather than the proposal's cosh call.
    out = A(10**9)
    for l, a in zip(ls, aa):
        e = A(l * l * t)
        w = A(l) * y
        out += A(F(a, 2)) * ((e + w).exp() + (e - w).exp())
    return out


pi = arb.pi()
xl = A(XL)
xe = A(Xe)
Rg = 1 / (12 * (xl / 8 - 1))
eu = 4 / (xl - 20) + 2 * Rg / xl
ev = (1 / xl + 6 / xl**2) / 4 + 8 * Rg / xl**2


# These error formulas are already-reviewed primitive inputs. Evaluate only new C comparisons.
def Cinit(y):
    sig = A((1 + y) / 2)
    z = arb_series([sig, arb(1)], 3).zeta()
    W = -z[1] / z[0]
    return z[2] / (2 * z[0]) + ev + W * eu + eu * eu


assert Cinit(F(3)) < A(F(302335, 1000000)) < A(ctop)
h0 = F(1000001, 1000000)
b0 = h0 + F(3, 5)
cells = [
    {"lo": str(b0 + (3 - b0) * F(i, 400)), "hi": str(b0 + (3 - b0) * F(i + 1, 400))}
    for i in range(400)
]
initial_max = arb(0)
new_cells = []
for i, c in enumerate(cells):
    lo, hi = F(c["lo"]), F(c["hi"])
    assert lo == b0 + (3 - b0) * F(i, 400) and hi == b0 + (3 - b0) * F(i + 1, 400)
    v = Cinit(lo) - A(ctop)
    positive = (v + abs(v)) / 2
    need = positive * U(F(0), A(hi))
    assert need < A(bigA)
    initial_max = mx(initial_max, need)
    new_cells.append(
        {"lo": str(lo), "hi": str(hi), "A_requirement": st(need), "A_slack": st(A(bigA) - need)}
    )
assert initial_max < A(bigA)
# New profile bounds evaluated on the BANKED trace, not an old height-proof replay.
old_t = [F(r["tlo"]) for r in oldrows]
assert len(oldrows) == 1620
Umin = None
Umax = None
last = F(0)
lastq = h0 * h0
for r in oldrows:
    tl, tr, ql, qr = (F(r[k]) for k in ["tlo", "thi", "q_start", "q_end"])
    assert tl == last and ql == lastq and tr > tl and ql > qr >= F(1, 400)
    ulo = U(tl, A(qr).sqrt() + A(F(3, 5)))
    uhi = U(tr, A(ql).sqrt() + A(F(3, 5)))
    Umin = ulo if Umin is None else mn(Umin, ulo)
    Umax = uhi if Umax is None else mx(Umax, uhi)
    last, lastq = tr, qr
assert last == tau and lastq == F(1, 400) and Umin > A(10**9)
Cb_min = A(ctop) + A(bigA) / Umax
Cmax = A(kap * tau).exp() * (A(ctop) + A(bigA) / Umin)
assert 22 * Umax < A(bigA) and Cb_min > 57 and Cmax < A(F(103119, 1000)) < A(10**6)
delta = A(F(1, 10**14)) * A(90 * tau).exp()
assert delta < A(F(1, 100000))
err_ratio = (1 + (pi / 8) / A(ctop).sqrt()) / xl
relative = A(kap) - 2 * A(lam) * delta - err_ratio
assert relative > A(F(97192, 10**10))
Elip = (1 + (pi / 8) / (2 * A(ctop).sqrt())) / xl
assert (A(86) - Elip) * A(K) > 2 * A(lam) * Cmax
assert (A(86) - Elip) * A(K) > 2 * A(lam) * A(10**6)
assert F(4412281, 169) < 30000 < 10 * K
omega = (A(X) / (4 * pi)).log() / 4
assert omega * omega + (pi / 8) ** 2 < 49
# NEW top-jet nested-disc scalar consequences of the banked H7 formula.
assert XL - F(5, 4) > Xe and F(15, 4) > 0 and F(25, 4) < 7
Ne = 685205
N = A(Ne)
q = xe / (4 * pi)
L = q.log()
Z = (L * L + pi * pi / 4).sqrt()
V7 = (20 * Z + 200) / (xe - 40)
yd, yu = A(F(15, 4)), A(F(25, 4))
e_floor = (1 - A(Tm) / (16 * N * N)).log()
cap = -A(Tm) * e_floor / 4
cutk = A(Tm) / (2 * (4 * pi * N * N - pi * A(Tm) / 4 - 6))
cutfirst = ((-(1 + yd) / 2 + A(Tm) / xe**2 + cap) * N.log() + A(Tm) * (N + 1).log() / (2 * N)).exp()
cutratio = (
    (yu * A(F(1, 10**11)) - yu * e_floor / 2).exp()
    * (1 + 1 / N) ** yu
    * (cutk * yu * (N + 1).log()).exp()
)
Ec = (
    q ** (-(1 + yd) / 4)
    * (2 * (arb(3) ** yu + arb(3) ** (-yu)) / (N - 1) + A(F(1, 10**10)) + V7).exp()
)
Ed = A(F(3, 10**9)) + Ec + cutfirst * (1 + cutratio)
assert Ed < A(F(1, 10**8)) and 4 * Ed < A(F(1, 10**7))
rate = A(F(500001, 1000000))
assert (1 + A(Tm) / (2 * (xe - 6))) / 2 < rate
rho = A(F(5, 2)) - A(Tm) / xe**2
z = arb_series([rho, arb(1)], 2).zeta()
ref0 = A(F(101, 100)) * N ** (1 - rho)
ref1 = ref0 * (2 * (N + 1).log() + 1)
assert (rho - 1) * (
    2 * (N + 1).log() + 1
) > 2  # proves N-uniform endpoint monotonicity of reflected derivative
m = 2 - z[0] - ref0 - A(F(1, 10**8))
assert m > 0
K2 = (rate * (-z[1]) + ref1 + A(F(1, 10**7))) / m
z3 = arb_series([3 - A(Tm) / xe**2, arb(1)], 2).zeta()
K3 = (rate * (-z3[1]) + A(F(1, 10**9)) + A(F(1, 10**7))) / (
    2 - z3[0] - A(F(1, 10**11)) - A(F(1, 10**8))
)
a1 = 1 / xe + 6 / xe**2
a2 = 2 / xe**2 + 24 / xe**3
a0 = Z / 2 + 8 / (xe - 20)
assert a0 > A(F(1, 2))
earch = 4 / (xe - 20) + A(Tm) * a0 * a1 / 4
ej = (a1 + A(Tm) * (a1 * a1 + a0 * a2) / 2) / 4
assert earch < A(F(1, 10**10)) and ej < A(F(1, 10**10))
Jtop = K2 + ej + (K3 + earch) ** 2
assert Jtop < A(F(309518, 1000000)) < A(ctop)


# Inspect the ROOT-FROZEN new boundary geometry only; no J source bands are evaluated.
def trace(t):
    if t == tau:
        return F(1, 400)
    i = bisect_right(old_t, t) - 1
    assert i >= 0
    rr = oldrows[i]
    tl, tr, ql, qr = (F(rr[k]) for k in ["tlo", "thi", "q_start", "q_end"])
    assert tl <= t < tr
    return ql + (qr - ql) * (t - tl) / (tr - tl)


assert F(geo["x_center_min"]) == XL and F(geo["x_wide_min"]) == XL - F(1, 4)
assert A(XL - F(1, 2)) > 4 * pi * 690950**2 and XL - F(1, 2) > Xe
assert (
    geo["beta"] == "1"
    and geo["source_inner_radius"] == "3/20"
    and geo["physical_outer_radius"] == "1/4"
)
bands = []
n = 690950
for _ in range(8):
    m0 = 11 * n // 10
    bands.append([n, m0])
    n = m0 + 1
bands.append([n, None])
assert n == 1481120 and geo["Nbands"] == bands
boxes = geo["boxes"]
assert len(boxes) == 162 and F(geo["time_end"]) == tau
last = F(0)
geomout = []
for i, bx in enumerate(boxes):
    tl, tr = F(bx["tlo"]), F(bx["thi"])
    assert bx["index"] == i and tl == last and tr == min(tl + F(1, 1000), tau)
    ql, qr = trace(tl), trace(tr)
    assert F(bx["banked_q_start"]) == ql and F(bx["banked_q_end"]) == qr and ql > qr
    yl, yh = F(bx["center_ylo"]), F(bx["center_yhi"])
    hl, hh = yl - F(3, 5), yh - F(3, 5)
    assert hl >= 0 and hl * hl <= qr and hh * hh >= ql and yl <= yh
    assert qr < (hl + F(1, 10**6)) ** 2 and (hh - F(1, 10**6)) ** 2 < ql
    wl, wh = F(bx["wide_ylo"]), F(bx["wide_yhi"])
    assert wl == yl - F(1, 4) and wh == yh + F(1, 4)
    assert 0 <= wl - F(3, 20) < wh + F(3, 20) <= F(5, 2)
    assert bx["source_inner_radius"] == "3/20" and bx["physical_outer_radius"] == "1/4"
    lower = A(kap * tl).exp() * (A(ctop) + A(bigA) / U(tr, A(yh)))
    geomout.append(
        {
            "index": i,
            "tlo": str(tl),
            "thi": str(tr),
            "center_ylo": str(yl),
            "center_yhi": str(yh),
            "C_lower": st(lower),
            "geometry_verified": True,
        }
    )
    last = tr
assert last == tau
assert F(198, 1250) - F(1, 800) == F(3143, 20000) < tau
balls = {
    "initial_A_requirement_max": initial_max,
    "boundary_U_max": Umax,
    "boundary_C_lower": Cb_min,
    "full_band_Cmax": Cmax,
    "delta_end": delta,
    "relative_interior_margin": relative,
    "E_lipschitz": Elip,
    "top_inner_source_error": Ed,
    "top_K2": K2,
    "top_K3": K3,
    "top_arch_error": earch,
    "top_arch_jet": ej,
    "top_J_bound": Jtop,
}
out = {
    "status": "FIXED_C_PROFILE_TOP_HEAD_AND_GEOMETRY_GATES_PASS",
    "precision_bits": ctx.prec,
    "python": platform.python_version(),
    "python_flint": flint.__version__,
    "same_profile": {"A": str(bigA), "constant": "8/25", "time_factor": "exp(t/100000)"},
    "balls": {k: st(v) for k, v in balls.items()},
    "initial_cells": new_cells,
    "banked_trace_cells_used_for_new_profile": len(oldrows),
    "source_geometry_cells": geomout,
    "source_geometry_sha256": hashlib.sha256(geompath.read_bytes()).hexdigest(),
    "banked_height_input_sha256": hashlib.sha256(HP.read_bytes()).hexdigest(),
    "executed_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
if args.out:
    args.out.write_text(json.dumps(out, indent=2) + "\n")
print(
    json.dumps(
        {
            "status": out["status"],
            "initial_cells": len(cells),
            "profile_trace_rows": len(oldrows),
            "source_geometry_boxes": len(boxes),
            "balls": out["balls"],
        },
        indent=2,
    )
)
