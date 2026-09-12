#!/usr/bin/env python3
"""Mollified value/derivative majorants on integer-cutoff bands.
Analytic justification: analytic-estimates.md, Section A.7.
Adapted from the historical P5 v2 evaluator; provenance is recorded separately.
"""

from flint import arb, ctx
from fractions import Fraction as F
from pathlib import Path

if not __debug__:
    raise RuntimeError("Run without Python optimization; assertions are proof gates.")


def Q(v):
    q = F(v)
    return arb(q.numerator) / q.denominator


def ball(lo, hi):
    lo, hi = F(lo), F(hi)
    assert lo <= hi
    value = arb(Q((lo + hi) / 2), Q((hi - lo) / 2))
    assert value.contains(Q(lo)) and value.contains(Q(hi))
    return value


def st(x):
    return x.str(40, more=True)


def maxball(x, y):
    return (x + y + abs(x - y)) / 2


def minball(x, y):
    return (x + y - abs(x - y)) / 2


def I(a, t, m, M, pi):
    # Integral of u^(-a) exp(t log(u)^2/4), and its first log moment.
    ell = arb(m).log()
    H = arb(M).log()
    assert M > m >= 1
    if t == 0:
        k = 1 - a
        if k == 0:
            i0 = H - ell
            i1 = (H * H - ell * ell) / 2
        else:
            assert k > 0 or k < 0
            gh = (k * H).exp()
            gl = (k * ell).exp()
            i0 = (gh - gl) / k
            i1 = (H * gh - ell * gl) / k - (gh - gl) / (k * k)
    else:
        tt = Q(t)
        root = tt.sqrt()
        k = 1 - a
        zl = root * ell / 2 + k / root
        zh = root * H / 2 + k / root
        i0 = (pi / tt).sqrt() * (-k * k / tt).exp() * (zh.erfi() - zl.erfi())
        gh = (tt * H * H / 4 + k * H).exp()
        gl = (tt * ell * ell / 4 + k * ell).exp()
        i1 = 2 * (gh - gl) / tt - 2 * k * i0 / tt
    assert i0 > 0 and i1 >= 0
    return i0, i1


def J(a, t, N, pi):
    L = arb(N).log()
    if t == 0:
        assert a > 1
        e = ((1 - a) * L).exp()
        j0 = e / (a - 1)
        j1 = e * (L / (a - 1) + 1 / (a - 1) ** 2)
    else:
        tt = Q(t)
        u = 1 - a
        root = tt.sqrt()
        z = root * L / 2 - u / root
        j0 = (pi / tt).sqrt() * (u * u / tt).exp() * z.erfc()
        j1 = 2 * ((1 - a) * L - tt * L * L / 4).exp() / tt + 2 * (1 - a) * j0 / tt
    assert j0 > 0 and j1 > 0 and a + Q(t) * L / 2 > 1 / L
    return j0, j1


def prepare(box, logs, R, primes):
    tl, th, yl, yh = map(F, [box[k] for k in ("tlo", "thi", "ylo", "yhi")])
    assert 0 <= tl <= th <= F(1, 5) and 0 < yl <= yh
    ti = ball(tl, th)
    lam = {1: arb(1)}
    lsq = {1: arb(0)}
    for p in primes:
        bp = (ti * logs[p] * logs[p] / 4).exp()
        lam.update({d * p: -v * bp for d, v in list(lam.items())})
        lsq.update({d * p: v + logs[p] * logs[p] for d, v in list(lsq.items())})
    ds = sorted(lam)
    assert ds[-1] < R
    bcore = [arb(1)] + [(ti * logs[n] * logs[n] / 4).exp() for n in range(1, R + 1)]
    coeff = [arb(0) for _ in range(R + 1)]
    for d in ds:
        for n in range(1, R // d + 1):
            coeff[d * n] += lam[d] * bcore[n]
    assert coeff[1] == 1
    return dict(
        tl=tl,
        th=th,
        yl=yl,
        yh=yh,
        ti=ti,
        mag=[abs(x) for x in coeff],
        ds=ds,
        lsq=lsq,
        primes=primes,
    )


def slab(C, prep, logs, R, nlo, nhi, beta=F(2, 5)):
    tl, yl = prep["tl"], prep["yl"]
    t = Q(tl)
    y = Q(yl)
    bb = Q(beta)
    Lm = arb(nlo).log()
    pi = C["pi"]
    T = C["T"]
    Cmax, corr = C["Cmax"], C["corr"]
    K = T / (2 * (4 * pi * C["N0"] ** 2 - pi * T / 4 - 6))
    delta = Q(F(1, 50)) - C["e0"] / 2
    ca = (1 + y) / 2 - Cmax - corr
    cb = ca - y - K * y
    ceff = cb + y
    sig = ca + t * Lm / 2
    assert ca > 0 and ceff > 0 and y * (Lm / 2 + bb) > 1
    xb = maxball(C["X"], 4 * pi * arb(nlo) ** 2 - pi * T / 4)
    La = (xb / (4 * pi)).log()
    C1 = 1 + T / (2 * (xb - 6))
    assert xb > C["Xe"]
    Blower = La / 4 - 1 / (xb * xb) - T * (La / 2 + pi / 4 + 5 / (xb - 6)) / (4 * (xb - 6))
    M = arb(1)
    Elog = arb(0)
    for p in prep["primes"]:
        lp = logs[p]
        zp = (t * lp * lp / 4 - sig * lp).exp()
        assert zp < 1
        M *= 1 + zp
        Elog += C1 * lp * zp / (2 * (1 - zp))
    Phase = 1 / arb(nlo) + (5 + T * (La + 1) / 2) / (xb - 6)
    assert Elog + Phase < bb
    SB = arb(0)
    DB = arb(0)
    for n in range(2, R + 1):
        val = prep["mag"][n] * (-sig * logs[n]).exp()
        SB += val
        DB += logs[n] * val
    Mhi = nlo if nhi is None else nhi
    H = arb(Mhi).log()
    assert H < 2 * Lm and y * (Lm + bb - H / 2) > 1
    assert delta - Lm + (Q(F(1, 2)) + K) * H < 0  # joint Y-monotonicity, finite part
    assert delta - (Q(F(1, 2)) - K) * Lm < 0  # joint Y-monotonicity, Gaussian tail
    if nhi is None:
        ja0, ja1 = J(ca, tl, nlo, pi)
        jb0, jb1 = J(ceff, tl, nlo, pi)
    else:
        ja0 = ja1 = jb0 = jb1 = arb(0)
    TB = arb(0)
    DT = arb(0)
    for d in prep["ds"]:
        m = R // d
        ld = logs[d]
        ell = arb(m).log()
        assert m >= 1 and ca - t * (H - Lm) / 2 > 1 / (ld + ell)
        # Weight log(d*u) times finite upper summand is decreasing.
        i0, i1 = I(sig, tl, m, Mhi, pi)
        assert prep["lsq"][d] - 2 * Lm * ld <= 0
        fac = (t * prep["lsq"][d] / 4 - sig * ld).exp()
        TB += fac * (i0 + ja0)
        DT += fac * (ld * (i0 + ja0) + i1 + ja1)
    # Second polynomial: complete prefix via a single-valley / one-positive-variation bound.
    asig = cb + t * Lm / 2
    i0, i1 = I(asig, tl, 1, Mhi, pi)
    gend = (t * H * H / 4 - asig * H).exp()
    weighted = (Lm + bb) * i0 - i1 / 2
    assert weighted > 0
    if asig - t * H / 2 > 0:
        raw0 = 1 + i0
        raww = Lm + bb + weighted
        second_case = "decreasing"
    else:
        raw0 = 1 + i0 + gend
        raww = Lm + bb + weighted + (Lm + bb) * maxball(arb(1), gend)
        second_case = "single-positive-variation"
    gp = (y * (delta - Lm)).exp()
    ginf = (y * delta).exp()
    Araw = gp * raw0 + ginf * jb0
    D1 = C1 * (DB + DT) / 2
    D2 = M * (gp * raww + ginf * (bb * jb0 + jb1 / 2))
    rpoint = SB + TB + M * Araw + M * prep["source"]["source_point"]
    drem = prep["Mdisk"] * prep["source"]["fixedN_disk"] / Q(prep["radius"])
    result = dict(Nlo=nlo, Nhi=nhi, case=second_case, nonzero=bool(rpoint < 1))
    fields = dict(
        SB=SB,
        DB=DB,
        TB=TB,
        DT=DT,
        D1=D1,
        D2=D2,
        rpoint=rpoint,
        Elog=Elog,
        Blower=Blower,
        Araw=Araw,
        source_derivative=drem,
    )
    if rpoint < 1:
        S = Blower - Elog - (D1 + D2 + drem) / (1 - rpoint)
        fields["S_lower"] = S
        result["S"] = S
    result["values"] = fields
    return result
