"""Whole-domain error gates used by the full vertical boundary replay.

The approximation error uses the repaired H7 Lemma A.1 in analytic-estimates.md,
on x>=Xe, 0<=t<=1/5, 0<=y<=7. The Taylor gates cover actual x=X,
0<=t<=1/5, 0<=y<=1, including endpoints; see computational-estimates.md.
"""

from math import factorial
from flint import arb, acb, ctx
from matrix import X, N, N0, XM, rational as Q, alpha


def check_bounds():
    import sys

    if sys.flags.optimize:
        raise RuntimeError("Assertions must be enabled")
    ctx.prec = 256
    x, xe, tm = arb(X), arb(5900000000000), Q("1/5")
    q = xe / (4 * arb.pi())
    ell = q.log()
    assert 2 * XM == 11998694683001 and 2 * N0 == N
    assert q > 1
    assert (x / (4 * arb.pi())).sqrt() > N
    assert (x / (4 * arb.pi()) + tm / 16).sqrt() < N + 1
    # Lemma A.1 proves Eab(x)<3e-9. Bound its Ec over the whole H7
    # domain using Y=7 only in positive inflation, Y=0 in q's power,
    # t=0 in the nonpositive heat exponent, and N>=Ne.
    ne, ymax = arb(685205), arb(7)
    assert ne * ne < q
    eab = Q("3e-9")
    v7 = (20 * (ell * ell + arb.pi() ** 2 / 4).sqrt() + 200) / (xe - 40)
    inflation = 2 * (arb(3) ** ymax + arb(3) ** (-ymax)) / (ne - 1) + Q("1e-10")
    ec = q ** (-Q("1/4")) * (inflation + v7).exp()
    source = eab + ec
    assert source < Q("0.001215803") < Q("1/500")
    t = arb(0).union(tm)
    y = arb(0).union(arb(1))
    assert t.contains(arb(0)) and t.contains(tm)
    assert y.contains(arb(0)) and y.contains(arb(1))
    s = acb((1 - y) / 2, x / 2)
    a_w, a_sc = alpha(1 - s), alpha(s.conjugate())
    ell0 = arb(N0).log()
    assert a_w.real > ell0 and a_sc.real > ell0
    vb = acb(-y / 2, Q("-1/4")) - t * (a_w - ell0) / 2
    va = acb(y / 2, Q("-1/4")) - t * (a_sc - ell0) / 2
    assert abs(vb) < Q("33/50") and abs(va) < Q("33/50")
    # For actual t>=0, the real heat contribution to either prefactor
    # is nonpositive. Thus |prefB|<=1, |prefA|<=sqrt(N0)<600.
    assert (ell0 / 2).exp() < 600
    assert Q("1e-11") - (x / (4 * arb.pi())).log() / 2 < 0  # H7: |gamma|<=1
    u, v = tm * ell0 * ell0 / 4, Q("33/50") * ell0
    assert u < 63 and v < 63
    ru = u**62 / (arb(factorial(62)) * (1 - u / 63))
    rv = v**62 / (arb(factorial(62)) * (1 - v / 63))
    tail = 2 * 600 * (2 * arb(N).sqrt() - 1) * (ru * v.exp() + u.exp() * rv)
    assert tail < Q("1/1000000000000")
    return {
        name: value.str(60, more=True)
        for name, value in {
            "source_AB_upper": eab,
            "source_C_upper": ec,
            "source_total_upper": source,
            "vB_modulus_upper": abs(vb),
            "vA_modulus_upper": abs(va),
            "prefactor_upper": (ell0 / 2).exp(),
            "Taylor_tail_upper": tail,
        }.items()
    }


if __name__ == "__main__":
    import json

    print(json.dumps(check_bounds(), indent=2))
