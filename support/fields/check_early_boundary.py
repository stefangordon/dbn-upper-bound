"""Relative-Euler boundary estimates on boxes 0--44; see analytic-estimates.md.
The only input is exact geometry. Decimals are parsed as exact rationals.
"""

import argparse, hashlib, json, math, sys
from fractions import Fraction as F
from pathlib import Path
import flint
from flint import arb as A, arb_series, ctx

if not __debug__:
    raise RuntimeError("Run without Python optimization; assertions are proof gates.")
ap = argparse.ArgumentParser()
ap.add_argument(
    "--geometry", default=str(Path(__file__).resolve().parent / "data/boundary-geometry.json")
)
ap.add_argument("--out", "--output", required=True)
ap.add_argument("--bits", type=int, default=512)
args = ap.parse_args()
ctx.prec = args.bits
ctx.cap = 8


def rat(x):
    q = F(str(x))
    return A(q.numerator) / q.denominator


def pos(x, name):
    if not x > 0:
        raise AssertionError((name, str(x)))
    return x


def bound(x):
    return {"ball": str(x), "lower": str(x.lower()), "upper": str(x.upper())}


raw = Path(args.geometry).read_bytes()
g = json.loads(raw)
assert (
    hashlib.sha256(raw).hexdigest()
    == "e0026af966a3d56db00bfedbcca8f8762bea204b33ac7f4bec49c5284044d453"
)
assert F(g["x_center_min"]) == F(5999346341500)
assert F(g["source_inner_radius"]) == F(3, 20)
assert F(g["physical_outer_radius"]) == F(1, 4)
boxes = g["boxes"][:45]
assert [b["index"] for b in boxes] == list(range(45))
for i, b in enumerate(boxes):
    assert F(b["tlo"]) == F(i, 1000) and F(b["thi"]) == F(i + 1, 1000)
    lo, hi = F(b["center_ylo"]), F(b["center_yhi"])
    assert 1 < lo < hi < 3
    assert (lo - F(3, 5)) ** 2 <= F(b["banked_q_end"])
    assert (hi - F(3, 5)) ** 2 >= F(b["banked_q_start"])
    assert F(b["banked_q_start"]) >= F(b["banked_q_end"]) > 0
    assert F(b["source_inner_radius"]) == F(3, 20)
    assert F(b["physical_outer_radius"]) == F(1, 4)
assert F(boxes[0]["tlo"]) == 0 and F(boxes[-1]["thi"]) == F(9, 200)

N0 = 690950
Ne = 685205
Xe = rat(5900000000000)
XL = rat(5999346341500)
T = rat("1/5")
r = rat("3/20")
ell = A(N0).log()
pi = A.pi()
Qe = Xe / (4 * pi)
Le = Qe.log()
Z = (Le * Le + pi * pi / 4).sqrt()
logloss = (1 - T / (16 * N0 * N0)).log()
cm = -T * logloss / 4
corr = T / (Xe * Xe)
r1 = rat("500001/1000000")
apr = 1 / (Xe - 6)
apr2 = 2 / (Xe * Xe) + 24 / (Xe**3)
r2 = T * apr2 / 8
amag = Z / 2 + 8 / (Xe - 20)
betadiff = 8 / (Xe - 20) + T * amag * apr / 2
betap = apr + T * (apr * apr + amag * apr2) / 2
b1 = betadiff / 2
b2 = betap / 4
beta = rat("1/1000")
phase2 = rat("1/10000000000")
phase1_bound = 1 / A(N0) + betadiff + T * ell / (4 * (Xe - 6))
phase2_bound = betap / 2 + T * apr2 * ell / 8
V7 = (20 * Z + 200) / (Xe - 40)
K = T / (2 * (4 * pi * N0 * N0 - pi * T / 4 - 6))
dg = rat("1/100000000000") - logloss / 2
pos(XL - r - Xe, "full disk x guard")
pos(XL - r - 4 * pi * N0 * N0, "full disk actual N lower bound")
pos(r1 - (1 + T * apr / 2) / 2, "actual s_z guard")
pos(beta - phase1_bound, "complete phase1 bound")
pos(phase2 - phase2_bound, "complete phase2 bound")
# A point x>=Xe bounds combined logarithm/negative-power expressions by
# monotonicity. log N<=.5 log(x/(4pi)+T/16) and this ratio decreases there.
pos(ell - (Xe / (4 * pi) + T / 16).log() / 2, "logN comparator at Xe")

head_logs = [A(n).log() for n in range(2, 1025)]
vstart = A(1024).log()
dv = rat("1/16")
V = vstart + 64
vleft = [vstart + rat(F(k, 16)) for k in range(1024)]
pos(V - ell, "negative Gaussian tail domain")
# Exact symbolic grid: endpoints are log(1024)+k/16, not decoded ball geometry.
assert F(1024, 16) == 64


def heat_moments(c, tl, th):
    out = [A(0), A(0), A(0)]
    for v in head_logs:
        h = 1 - (1 + th * v * v / 4) * (-th * v * v / 4).exp()
        pos(h, "positive finite heat remainder h")
        if v < ell:
            exponent = tl * (v * v / 4 - v * ell / 2)
        elif v > ell:
            exponent = -tl * v * v / 4
        else:
            raise AssertionError("ambiguous exact max at finite head")
        f = (-c * v + exponent).exp() * h
        for j in range(3):
            out[j] += v**j * f
    for v in vleft:
        w = v + dv
        if v < ell:
            exponent = tl * (v * v / 4 - v * ell / 2)
        elif v > ell:
            exponent = -tl * v * v / 4
        else:
            raise AssertionError("ambiguous exact max at integration endpoint")
        E = (-(c - 1) * v + exponent).exp()
        h = 1 - (1 + th * w * w / 4) * (-th * w * w / 4).exp()
        pos(h, "positive heat integral h")
        for j in range(3):
            out[j] += dv * E * w**j * h
    lam = c - 1 + tl * V / 2
    pos(lam, "heat tail exponential rate")
    pref = (-(c - 1) * V - tl * V * V / 4).exp()
    tails = []
    for j in range(3):
        tail = pref * sum(
            A(math.comb(j, k) * math.factorial(k)) * V ** (j - k) / lam ** (k + 1)
            for k in range(j + 1)
        )
        out[j] += tail
        tails.append(tail)
    return out, tails


def unheated_tail(a, j):
    return ((1 - a) * ell).exp() * sum(
        A(math.factorial(j) // math.factorial(j - k)) * ell ** (j - k) / (a - 1) ** (k + 1)
        for k in range(j + 1)
    )


def C_lower(y, tlo, thi):
    U = rat(1000000000)
    for lam0, coef in [(F(19, 4), 1758974), (F(97, 20), 2464729), (F(131, 20), 302096)]:
        lam = rat(lam0)
        U += coef * (lam * lam * thi).exp() * (lam * y).cosh()
    return (tlo / 100000).exp() * (rat("8/25") + rat(1130000000000) / U)


rows = []
for i, b in enumerate(boxes):
    tl, th = rat(b["tlo"]), rat(b["thi"])
    yl, yh = rat(b["center_ylo"]), rat(b["center_yhi"])
    c = (1 + yl) / 2 - cm - corr
    a = c + tl * ell / 2
    yd, yu = yl - r, yh + r
    gates = {
        "a_gt_1": a - 1,
        "heat_c_gt_1": c - 1,
        "cutoff_negative_coefficient": (1 + yd) / 2 - corr - cm,
        "Euler_reference_full_disk": a - r1 * r - 1,
        "heat_summand_decrease": c - 6 / vstart,
        "unheated_tail_decrease": a - 4 / ell,
        "disk_y_positive": yd,
        "disk_y_below_H7": 7 - yu,
        "alpha_sigma_early_scope": 2 - (1 + yu) / 2,
    }
    for key, val in gates.items():
        pos(val, key)
    # Positive Euler logarithmic derivative moments from the convergent zeta
    # Taylor series. Coefficient factorials are explicit, including W3=4!q4.
    q = arb_series([a, 1], 8).zeta().log()
    W = [(-1) ** (j + 1) * math.factorial(j + 1) * q[j + 1] for j in range(4)]
    for j, w in enumerate(W):
        pos(w, "Euler W" + str(j))
    w0, w1, w2, w3 = W
    z0 = w1 + w0 * w0
    z1 = w2 + 2 * w0 * w1
    z2 = w3 + 2 * w1 * w1 + 2 * w0 * w2
    mz = (2 * a).zeta() / a.zeta()
    pos(mz, "sharp Euler minimum")
    H, heat_tail = heat_moments(c, tl, th)
    tails = [unheated_tail(a, j) + th * unheated_tail(a, j + 2) / 4 for j in range(3)]
    # Reflected finite-prefix all-N reduction, with positive square-phase weight.
    bb = c - yl - K * yl
    ee = bb + yl
    a0 = 1 - bb
    k0 = (1 - (-a0 * ell).exp()) / a0
    gates.update(
        {
            "reflected_y_reduction": (rat("1/2") - K) * ell - dg,
            "reflected_integral_rate": a0,
            "reflected_square_weight_integral": (yl - 2 / (ell + beta)) * k0 - 1,
            "reflected_square_weight_endpoint": ee * (ell + beta) - 2,
            "reflected_right_endpoint_rectangles": 1 - bb - tl * ell / 2,
        }
    )
    for key, val in gates.items():
        pos(val, key)
    dlog = ell / 1024
    integral = A(0)
    for k in range(1, 1025):
        v = dlog * k
        integral += dlog * ((1 - bb - tl * ell / 2) * v + tl * v * v / 4).exp()
    ref = (dg * yl).exp() * (
        ((-yl * ell).exp()) * (1 + integral) + (-ee * ell - tl * ell * ell / 4).exp()
    )

    # NEW early disk consequence of H7 point source plus both cutoff branches.
    def ec(lo, hi):
        return (
            -(1 + lo) * Le / 4
            - tl * Le * Le / 16
            + 2 * ((hi * A(3).log()).exp() + (-hi * A(3).log()).exp()) / (Ne - 1)
            + rat("1/10000000000")
            + V7
        ).exp()

    E0 = rat("3/1000000000") + ec(yl, yu)
    cut1 = (
        ((-(1 + yd) / 2 + corr + cm) * ell) - tl * ell * ell / 4 + T * A(N0 + 1).log() / (2 * N0)
    ).exp()
    gcut = (
        yu * rat("1/100000000000")
        - yu * logloss / 2
        + yu * (1 + 1 / A(N0)).log()
        + T * yu * A(N0 + 1).log() / (2 * (4 * pi * N0 * N0 - pi * T / 4 - 6))
    ).exp()
    Ed = rat("3/1000000000") + ec(yd, yu) + cut1 * (1 + gcut)
    E1 = Ed / r
    E2 = 2 * Ed / (r * r)
    R0 = H[0] + tails[0] + ref + E0
    R1 = r1 * (H[1] + tails[1]) + (ell + beta) * ref + E1
    R2 = (
        r1 * r1 * (H[2] + tails[2])
        + r2 * (H[1] + tails[1])
        + ((ell + beta) ** 2 + phase2) * ref
        + E2
    )
    rho0 = th * z0 / 4 + R0 / mz
    rho1 = th * r1 * z1 / 4 + (R1 + r1 * w0 * R0) / mz
    rho2 = (
        th * (r1 * r1 * z2 + r2 * z1) / 4
        + (R2 + 2 * r1 * w0 * R1 + (r1 * r1 * (w0 * w0 + w1) + r2 * w0) * R0) / mz
    )
    d = 1 - rho0
    pos(d, "relative denominator")
    gg1 = r1 * w0 + rho1 / d
    gg2 = r1 * r1 * w1 + r2 * w0 + rho2 / d + (rho1 / d) ** 2
    J = b2 + gg2 + (b1 + gg1) ** 2
    C = C_lower(yh, tl, th)
    margin = C - J
    pos(margin, "SAME-C source gate")
    row = {
        "index": i,
        "geometry": b,
        "gates": {k: bound(v) for k, v in gates.items()},
        "a": bound(a),
        "c": bound(c),
        "W": list(map(bound, W)),
        "m_zeta": bound(mz),
        "heat_moments": list(map(bound, H)),
        "heat_tails": list(map(bound, heat_tail)),
        "ordinary_Taylor_tails": list(map(bound, tails)),
        "reflected_amplitude": bound(ref),
        "source_jets": list(map(bound, [E0, E1, E2])),
        "source_disk": bound(Ed),
        "raw_remainder_jets": list(map(bound, [R0, R1, R2])),
        "rho_jets": list(map(bound, [rho0, rho1, rho2])),
        "denominator": bound(d),
        "J": bound(J),
        "C_lower": bound(C),
        "margin": bound(margin),
        "ratio": bound(J / C),
    }
    rows.append(row)
    print(i, "margin", margin, "ratio", J / C, flush=True)

result = {
    "status": "EARLY_BOUNDARY_45_BOXES_PASS",
    "completed": True,
    "python": sys.version,
    "python_flint": flint.__version__,
    "bits": ctx.prec,
    "input_geometry_sha256": hashlib.sha256(raw).hexdigest(),
    "input_scope": "45 original closed center boxes; all x>=5999346341500; analytic all actual N>=690950",
    "source_budgets": "H7 point Eab<3e-9 and the early fixed-cutoff disk bound",
    "source_Cauchy_second_factorial": 2,
    "global_constants": {
        k: bound(v)
        for k, v in {
            "b1": b1,
            "b2": b2,
            "r1": r1,
            "r2": r2,
            "phase1_bound": phase1_bound,
            "phase1_cap": beta,
            "phase2_bound": phase2_bound,
            "phase2_cap": phase2,
            "full_disk_N_guard": XL - r - 4 * pi * N0 * N0,
        }.items()
    },
    "rows": rows,
}
Path(args.out).write_text(json.dumps(result, indent=2) + "\n")
