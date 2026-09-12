"""Exact metadata, preserved ball radii, and Taylor matrix evaluation."""

from fractions import Fraction as F
from pathlib import Path
from flint import arb, acb

X, N, N0, ORDER = 5999347341500, 690950, 345475, 62
XM = F(2 * X + 1, 2)


def rational(value):
    q = F(value)
    return arb(q.numerator) / q.denominator


def read_matrix(path):
    lines = Path(path).read_text().splitlines()
    if len(lines) != ORDER + 1:
        raise ValueError("Matrix must have a header and 62 rows")
    header = lines[0].split(",")
    if not (
        F(header[0]) == XM
        and int(header[1]) == N0
        and list(map(int, header[4:6])) == [ORDER, ORDER]
    ):
        raise ValueError("Wrong matrix centre, scaling or dimensions")
    out = []
    for line in lines[1:]:
        entries = line.split(" ; ")
        if len(entries) != ORDER:
            raise ValueError("Wrong matrix width")
        row = [acb(*[arb(part) for part in entry.split(" | ")]) for entry in entries]
        if not all(z.is_finite() for z in row):
            raise ValueError("Nonfinite matrix entry")
        out.append(row)
    return tuple(map(int, header[2:4])), out


def alpha(s):
    return 1 / (2 * s) + 1 / (s - 1) + (s / (2 * arb.pi())).log() / 2


def log_m0(s):
    pi = arb.pi()
    return (
        s.log()
        + (s - 1).log()
        - arb(16).log()
        - s * pi.log() / 2
        + (2 * pi).log() / 2
        + (s / 2 - rational("1/2")) * (s / 2).log()
        - s / 2
    )


def horner(coefficients, value):
    out = coefficients[-1]
    for coefficient in reversed(coefficients[:-1]):
        out = out * value + coefficient
    return out


def evaluate(fin, t, y):
    """Unscaled source polynomial, with every prefactor and gamma retained."""
    s = acb((1 - y) / 2, arb(X) / 2)
    w, sc = 1 - s, s.conjugate()
    a_s, a_w, a_sc = alpha(s), alpha(w), alpha(sc)
    ell0 = arb(N0).log()
    base_b = acb(-y / 2, rational("-1/4"))
    base_a = acb(y / 2, rational("-1/4"))
    vb, va = base_b - t * (a_w - ell0) / 2, base_a - t * (a_sc - ell0) / 2
    pb = ((base_b - t * (2 * a_w - ell0) / 4) * ell0).exp()
    pa = ((base_a - t * (2 * a_sc - ell0) / 4) * ell0).exp()
    gamma = (t * (a_s * a_s - a_w * a_w) / 4 + log_m0(s) - log_m0(w)).exp()
    return pb * horner(fin, vb) + gamma * (pa * horner(fin, va)).conjugate()
