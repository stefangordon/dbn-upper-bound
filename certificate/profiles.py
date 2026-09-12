#!/usr/bin/env python3
"""Rigorous evaluation of the finite profile inequalities in P8.

Two arithmetic backends independently enclose the elementary expressions. The
analytic comparisons S >= f0 - delta and J <= C are separate proof obligations.
This module neither samples H_t nor infers a global estimate from point samples.
"""

import argparse
from fractions import Fraction
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("dbn_certificate_check", HERE / "check.py")
exact = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exact)


def arb_profiles(data, bits=512):
    import flint
    from flint import arb, ctx

    exact.require(type(bits) is int and bits >= 128, "Arb precision must be at least 128 bits")
    ctx.prec = bits

    def real(q):
        value = Fraction(q)
        return arb(value.numerator) / value.denominator

    def minimum(a, b):
        return b if a is None else (a + b - abs(a - b)) / 2

    omega_gap = (arb(5999346341500) / (4 * arb.pi())).log() / 4 - real(exact.OMEGA)
    subtraction_gap = real("1/100000") - (90 * real(exact.TM)).exp() / 10**14
    exact.require(omega_gap > 0, "Arb: Omega gap is not certainly positive")
    exact.require(subtraction_gap > 0, "Arb: delta(T_M) < 1e-5 is not certified")
    floor_min, ceiling_min = None, None
    signed = 0
    for i, row in enumerate(data["reference"]):
        field = row["field"]
        p, tl, tr, s = [Fraction(value) for value in (field["p"], row["tl"], row["tr"], field["s"])]
        U, UY = arb(10**9), arb(0)
        for coefficient, frequency in [
            (1758974, Fraction(19, 4)),
            (2464729, Fraction(97, 20)),
            (302096, Fraction(131, 20)),
        ]:
            weight = coefficient * real(frequency * frequency * tl).exp()
            argument = real(frequency * p)
            U += weight * argument.cosh()
            UY += weight * real(frequency) * argument.sinh()
        gap = UY / U - real("1/100000") - real(s)
        exact.require(gap > 0, f"Arb: reference[{i}] density margin not certainly positive")
        floor_min = minimum(floor_min, gap)
        if field["signed"]:
            signed += 1
            upper = (real(tr) / 100000).exp() * (real("8/25") + arb(1130000000000) / U)
            gap = real(field["c"]) - upper
            exact.require(gap >= 0, f"Arb: reference[{i}] jet margin not certainly nonnegative")
            ceiling_min = minimum(ceiling_min, gap)
    text = lambda x: x.str(55, more=True)
    return dict(
        status="PASS",
        backend="Arb",
        python_flint=flint.__version__,
        flint=flint.__FLINT_VERSION__,
        precision_bits=ctx.prec,
        density_floors=len(data["reference"]),
        jet_ceilings=signed,
        minimum_density_margin=text(floor_min),
        minimum_jet_margin=text(ceiling_min),
        omega_gap=text(omega_gap),
        subtraction_gap=text(subtraction_gap),
    )


def mpmath_profiles(data, digits=80):
    import mpmath
    from mpmath import iv

    exact.require(
        type(digits) is int and digits >= 40, "mpmath precision must be at least 40 digits"
    )
    iv.dps = digits

    def interval(q):
        value = Fraction(q)
        return iv.mpf(value.numerator) / iv.mpf(value.denominator)

    omega_gap = iv.log(iv.mpf(5999346341500) / (4 * iv.pi)) / 4 - interval(exact.OMEGA)
    subtraction_gap = interval("1/100000") - iv.exp(90 * interval(exact.TM)) / iv.mpf(10) ** 14
    exact.require(omega_gap.a > 0, "mpmath: Omega gap is not certainly positive")
    exact.require(subtraction_gap.a > 0, "mpmath: delta(T_M) < 1e-5 is not certified")
    floor_min, ceiling_min = None, None
    signed = 0
    for i, row in enumerate(data["reference"]):
        field = row["field"]
        p, tl, tr, s = [interval(value) for value in (field["p"], row["tl"], row["tr"], field["s"])]
        U, derivative = iv.mpf(10**9), iv.mpf(0)
        for coefficient, frequency in zip([1758974, 2464729, 302096], ["19/4", "97/20", "131/20"]):
            lam = interval(frequency)
            heat = iv.exp(lam * lam * tl)
            positive, negative = iv.exp(lam * p), iv.exp(-lam * p)
            U += coefficient * heat * (positive + negative) / 2
            derivative += coefficient * heat * lam * (positive - negative) / 2
        gap = derivative / U - interval("1/100000") - s
        exact.require(gap.a > 0, f"mpmath: reference[{i}] density margin not certainly positive")
        floor_min = gap.a if floor_min is None else min(floor_min, gap.a)
        if field["signed"]:
            signed += 1
            upper = iv.exp(tr / 100000) * (interval("8/25") + iv.mpf(1130000000000) / U)
            gap = interval(field["c"]) - upper
            exact.require(
                gap.a >= 0, f"mpmath: reference[{i}] jet margin not certainly nonnegative"
            )
            ceiling_min = gap.a if ceiling_min is None else min(ceiling_min, gap.a)
    return dict(
        status="PASS",
        backend="mpmath intervals",
        mpmath=mpmath.__version__,
        precision_decimal_digits=digits,
        density_floors=len(data["reference"]),
        jet_ceilings=signed,
        minimum_density_margin_lower=str(floor_min),
        minimum_jet_margin_lower=str(ceiling_min),
        omega_gap=str(omega_gap),
        subtraction_gap=str(subtraction_gap),
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=exact.DATA)
    parser.add_argument("--backend", choices=["arb", "mpmath"], required=True)
    parser.add_argument("--bits", type=int, default=512)
    parser.add_argument("--digits", type=int, default=80)
    parser.add_argument("--output", type=Path, help="optional result file; no input is modified")
    args = parser.parse_args()
    try:
        data = exact.load(args.data)
        exact.check(data)
        result = (
            arb_profiles(data, args.bits)
            if args.backend == "arb"
            else mpmath_profiles(data, args.digits)
        )
        result["scope"] = (
            "P8 profile expressions only; analytic density/jet comparisons are separate"
        )
        output = json.dumps(result, indent=2) + "\n"
        if args.output:
            args.output.write_text(output)
        print(output, end="")
    except (
        exact.InvalidCertificate,
        KeyError,
        TypeError,
        ValueError,
        OSError,
        ZeroDivisionError,
        ImportError,
    ) as error:
        parser.exit(1, f"FAIL: {error}\n")


if __name__ == "__main__":
    main()
