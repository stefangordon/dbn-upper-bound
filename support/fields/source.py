"""H7 point and fixed-cutoff disk bounds used by the jet boundary check.

All constants are exact rationals or Arb balls.  The proof, including cutoff
jumps, is in analytic-estimates.md A.1--A.3.  This module uses the uniform
3e-9 polynomial error and V7 throughout, including on the smaller low-Y band.
"""

from fractions import Fraction as F
from flint import arb


def Q(x):
    r = F(x)
    return arb(r.numerator) / r.denominator


def constants():
    Xe = Q(5900000000000)
    T = Q("1/5")
    pi = arb.pi()
    N0 = arb(690950)
    Ne = arb(685205)
    q = Xe / (4 * pi)
    L = q.log()
    Z = (L * L + pi * pi / 4).sqrt()
    e0 = (1 - T / (16 * N0 * N0)).log()
    assert Ne * Ne < q < (Ne + 1) ** 2
    return dict(
        X=Q(5999346341500),
        Xe=Xe,
        T=T,
        N0=N0,
        Ne=Ne,
        pi=pi,
        q=q,
        L=L,
        Eab=Q("3e-9"),
        V=(20 * Z + 200) / (Xe - 40),
        e0=e0,
        Cmax=-T * e0 / 4,
        LN=N0.log(),
        LNP=(N0 + 1).log(),
        corr=T / (Xe * Xe),
    )


def source_box(C, tlo, thi, ylo, yhi, radius):
    tl, th, yl, yh, r = map(F, (tlo, thi, ylo, yhi, radius))
    assert 0 <= tl <= th <= F(1, 5) and 0 < r <= F(1, 4) and 0 <= yl - r <= yh + r <= F(5, 2)
    yd, yu = Q(yl - r), Q(yh + r)
    t = Q(tl)
    q, L, T, Ne, N0 = (C[k] for k in ("q", "L", "T", "Ne", "N0"))
    positive = 2 * (arb(3) ** yu + arb(3) ** (-yu)) / (Ne - 1) + Q("1e-10") + C["V"]
    point = C["Eab"] + q ** (-(1 + Q(yl)) / 4) * (-t * L * L / 16 + positive).exp()
    disk = C["Eab"] + q ** (-(1 + yd) / 4) * (-t * L * L / 16 + positive).exp()
    coefficient = -(1 + yd) / 2 + C["corr"] + C["Cmax"]
    assert coefficient < 0
    first = (coefficient * C["LN"] - t * C["LN"] ** 2 / 4 + T * C["LNP"] / (2 * N0)).exp()
    k = T / (2 * (4 * C["pi"] * N0 * N0 - C["pi"] * T / 4 - 6))
    ratio = (
        (Q("1/50") * yu - yu * C["e0"] / 2).exp() * (1 + 1 / N0) ** yu * (k * yu * C["LNP"]).exp()
    )
    return dict(source_point=point, fixedN_disk=disk + first * (1 + ratio))
