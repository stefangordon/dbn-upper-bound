#!/usr/bin/env python3
"""Scalar gates for analytic-estimates.md, Sections A.1--A.3 (Arb 512)."""

from pathlib import Path
from fractions import Fraction as F
from flint import arb, arb_series, ctx
import flint, json, hashlib, sys, argparse

if not __debug__:
    raise RuntimeError("Run without Python optimization; assertions are proof gates.")
ap = argparse.ArgumentParser()
ap.add_argument("--out", "--output", type=Path)
args = ap.parse_args()
ctx.prec = 512


def q(x):
    x = F(x)
    return arb(x.numerator) / x.denominator


def txt(x):
    return x.str(65, more=True)


Xe = q(5900000000000)
X = q(5999347341500)
XL = X - 1000000
T = q("1/5")
YM = q(7)
N = q(685205)
pi = arb.pi()
Q = Xe / (4 * pi)
L = Q.log()
Z = (L * L + pi * pi / 4).sqrt()
da = 8 / (Xe - 20)
assert (1 - YM) / 2 == -3 and (1 + YM) / 2 == 4
assert N * N < Q and (Q + T / 16).sqrt() < q("1001/1000") * Q.sqrt()
assert 7 / Xe + 16 / Xe**2 < da
assert T * pi / 8 + 4 * T / (Xe - 20) < 1
lg = (T * L / 4 + 9) / (Xe - 20)
assert lg < q("1e-11")
gbound = (
    (YM * q("1e-11")).exp()
    * (1 + T / (16 * Q)) ** (YM / 2)
    * (T * YM * Xe.log() / (2 * (Xe - 6))).exp()
)
assert gbound < q("101/100")
# The SAME vertical Euler--Maclaurin bound, but NEW sigma_abs4 / sigma_lower-3.
Ag = Xe / 2 - 3
D = 1 - T / Ag
err = (17 / Ag + 16 * T / (Ag * Ag * D)).exp() / D.sqrt() - 1
pos = q("1/5") * (17 / Ag + T * (arb(3).log() + 4 / Ag) ** 2 / D).exp() / D.sqrt()
neg = q("29/1000") * (17 / Ag + T * (arb(2).log() / 2 + 4 / Ag) ** 2 / D).exp() / D.sqrt()
assert err < q("6e-12") and pos < q("26/100") and neg < q("3/100")
assert (2 * pi).sqrt() / (4 * pi) < q("1/5") and q("11/10") ** 2 / 7 < q("173/1000")
kap = ((3 - 2 * arb(2).log()) * pi) ** q("-1/2")
pr = arb(2).sqrt() / (4 * pi * pi)
coef = pr * (pi.sqrt() * kap + kap * kap / N) / (1 - 50 * kap * kap / (N * N))
assert coef < q("29/1000") and pr < q("1/2") and kap < q("11/10")
assert q("11/10") * 101 / N < q("1/1000")
rs100 = q("1/2") * q("1e-303") * 8 * neg / q("29/1000")
assert rs100 < q("1e-301")
tail_pref = 8 * (T / pi).sqrt() * (33 / Ag).exp()
assert 4 * T <= Ag and tail_pref < 4 and 4 * (-q(5000)).exp() < q("1e-100")
assert q("6e-12") + 2 * q("1e-100") + 2 * q("1e-301") < q("1e-10")
# NEW normalization range/displacement, unchanged polynomial-multiplier numerator.
assert 16 + (pi * T / 8) ** 2 < 17
assert 3 * q(17).sqrt() / Xe + 17 / (2 * (Xe - 6)) < 22 / (Xe - 20)
extra = pi * pi / 16 + da * Z + da * da
assert extra < q("667/1000") and T * T * q("667/1000") / 8 + T / 4 + q("1/6") < q("313/1000")
V = (20 * Z + 200) / (Xe - 40)
Vraw = (22 + 2 * T * Z) / (Xe - 20) + 16 * T / (Xe - 20) ** 2
assert Vraw < V
c = q("499/1000")
beta = (1 - c) / 2
dd = (T * T * L * L / 16 + q("626/1000")) / (Xe - q("666/100"))
assert T / (Xe * Xe) < q("1/1000") and dd < q("1/1000") and beta + 2 / L - 1 < 0
Eab = q("201/100") * q("1000/999") * q("1001/1000") ** (1 - c) / (1 - c) * Q**beta * dd
assert Eab < q("3e-9")
U = 2 * (arb(3) ** YM + arb(3) ** (-YM)) / (N - 1) + q("1e-10")
Ewhole = q("3e-9") + Q ** q("-1/4") * (U + V).exp()
assert Ewhole < q("1/500")
# NEW whole disk x0>=Xe+1,Y5,r1/4, usingNe not oldN0.
yd = q("19/4")
yu = q("21/4")
radius = q("1/4")
assert 0 <= yd < yu <= YM
ell = (1 - T / (16 * N * N)).log()
Cmax = -T * ell / 4
dc = T / (Xe * Xe)
assert -(1 + yd) / 2 + dc + Cmax < 0
cut1 = ((-(1 + yd) / 2 + dc + Cmax) * N.log() + T * (N + 1).log() / (2 * N)).exp()
K = T / (2 * (4 * pi * N * N - pi * T / 4 - 6))
gcut = (yu * q("1e-11") - yu * ell / 2).exp() * (1 + 1 / N) ** yu * (K * yu * (N + 1).log()).exp()
cut = cut1 * (1 + gcut)
EdiskC = (
    Q ** (-(1 + yd) / 4) * (2 * (arb(3) ** yu + arb(3) ** (-yu)) / (N - 1) + q("1e-10") + V).exp()
)
Edisk = q("3e-9") + EdiskC + cut
assert Edisk < q("1e-8") and Edisk / radius < q("1e-7")
# Uniform top full finite model and exact derivative majorants.
rho = 3 - T / (Xe * Xe)
assert rho > 2
zz = arb_series([rho, arb(1)], 2).zeta()
zeta = zz[0]
mzprime = -zz[1]
rate = q("500001/1000000")
assert (1 + T / (2 * (Xe - 6))) / 2 < rate
betamod = (Z / 2 + da) * (1 + T / (2 * (Xe - 6)))
assert betamod < L / 2 + 1
ref0 = q("101/100") * N ** (1 - rho)
ref1 = ref0 * (2 * (N + 1).log() + 1)
assert ref0 < q("1e-11") and ref1 < q("1e-9")
m = 2 - zeta - q("1e-11") - q("1e-8")
assert m > q("79/100")
quot = (rate * mzprime + q("1e-9") + q("1e-7")) / m
assert quot < q("1/8")
archloss = 1 / (Xe * Xe) + T * (Z / 2 + da) / (4 * (Xe - 6))
assert archloss < q("1e-10")
TOP = (XL / (4 * pi)).log() / 4 - q("1e-10") - quot
assert TOP > q("659/100")
Zmax = ((X / (4 * pi)).log() ** 2 + pi * pi / 4).sqrt()
SIDE = (Zmax / 2 + da) * (1 + T / (2 * (Xe - 6))) / 2 + quot
assert SIDE < 10
assert XL > Xe + 6 and X - 92000 < X - 6
out = {
    "status": "H7_SCALAR_GATES_PASS",
    "precision_bits": ctx.prec,
    "python": sys.version,
    "python_flint": flint.__version__,
    "values": {
        k: txt(v)
        for k, v in dict(
            gamma_envelope=gbound,
            gaussian_epsilon=err,
            gaussian_positive=pos,
            gaussian_negative=neg,
            negative_coefficient=coef,
            RS100=rs100,
            high_tail_prefactor=tail_pref,
            Eab=Eab,
            whole_H7_error=Ewhole,
            fixedN_disk=Edisk,
            fixedN_derivative=Edisk / radius,
            reflected_mass=ref0,
            reflected_derivative=ref1,
            F_modulus_lower=m,
            F_log_derivative_upper=quot,
            archimedean_loss=archloss,
            TOP5_lower=TOP,
            SIDE5_upper=SIDE,
        ).items()
    },
    "exact_H7": "x>=5900000000000,t[0,1/5],y[0,7]",
    "exact_TOP5": "x>=5999346341500,t[0,1/5],Y5,H nonzero,S>659/100",
    "exact_SIDE5": "x[5900000000001,5999347341500],t[0,1/5],Y5,|Hprime/H|<10",
    "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
if args.out:
    args.out.write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps(out, indent=2))
