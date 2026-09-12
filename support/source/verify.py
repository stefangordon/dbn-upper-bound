#!/usr/bin/env python3
"""Recompute the 26 uniform three-probe floors from analytic majorants.

The finite-head, infinite-tail, reflected all-N and fixed-cutoff Cauchy
calculations implement manuscript/computational-estimates.md. No saved source
enclosures or trajectory are numerical inputs. The additive-Q route proves
the required nonvanishing directly, without using the jet field or a wall.
"""

import argparse
from fractions import Fraction as F
import hashlib
import json
from math import factorial
from pathlib import Path
import sys
import time
import flint
from flint import arb, arb_series, ctx


def require(name, condition):
    if not bool(condition):
        raise ArithmeticError("Unproved gate: " + name)


def Q(value):
    value = F(value)
    return arb(value.numerator) / value.denominator


def text(value):
    require("finite serialized enclosure", value.is_finite())
    return value.str(65, more=True)


def maximum(a, b):
    return (a + b + abs(a - b)) / 2


def evaluate(box):
    tl, th = map(F, box["t_interval"])
    hl, hh = map(F, box["h_interval"])
    require("closed time and height rectangle", 0 <= tl < th <= F(1, 5) and 0 < hl < hh <= 1)
    require("positive floor", F(box["floor"]) > 0)
    tlo, thi, tm = Q(tl), Q(th), Q("1/5")
    rsf = F(1, 20)
    rs, xe, n0 = Q(rsf), Q(5900000000000), Q(690950)
    pi, l0 = arb.pi(), n0.log()
    le = (xe / (4 * pi)).log()
    zarch = (le * le + pi * pi / 4).sqrt()
    require("source disks in H7 real domain", F(5999347341500) - rsf > F(5900000000000))
    require("all source disk cutoffs >= N0", Q(F(5999347341500) - rsf) > 4 * pi * n0 * n0)
    cutoff_variation = rs / (8 * pi * n0)
    require("cutoff changes at most one", cutoff_variation < 1)
    omega = Q("6722911/1000000")
    require("Omega lower on all x", omega < (Q(5999346341500) / (4 * pi)).log() / 4)
    arg = 1 - tm / (16 * n0 * n0)
    kden = 2 * (4 * pi * n0 * n0 - pi * tm / 4 - 6)
    require("floor correction positive argument", arg > 0)
    require("kappa positive denominator", kden > 0)
    flog = arg.log()
    cap, corr, kappa = -tm * flog / 4, tm / (xe * xe), tm / kden
    dg = Q("1e-11") - flog / 2
    da = 8 / (xe - 20)
    a0, a1 = zarch / 2 + da, 1 / xe + 6 / (xe * xe)
    arch = da / 2 + tm * a0 * a1 / 4
    eta, rate = thi / (4 * (xe - 6)), Q("500001/1000000")
    phase = 1 / n0 + da + thi * a0 * a1 / 2 + thi * a1 * xe.log() / 4
    beta = Q("1/2")
    require("archimedean allowance", arch < Q("1e-10"))
    require("spatial chain rate", Q("1/2") + eta < rate)
    require("reflected phase allowance", phase < beta)
    require("full reflected Y monotonicity", dg - (Q("1/2") - kappa) * l0 < 0)
    v7 = (20 * zarch + 200) / (xe - 40)
    head_size, cells, reflected_cells = 1024, 1024, 1024
    lv, dv, log3 = Q(head_size).log(), Q("1/16"), Q(3).log()
    a_first = Q((1 + 3 * hl) / 2) - cap - corr + tlo * l0 / 2
    bands, numerical = [], []

    def heat(c):
        require("heat integral-test gates", c > 1 and c > 5 / lv)
        head, integral = [arb(0), arb(0)], [arb(0), arb(0)]

        def H(v):
            u = thi * v * v / 4
            value = 1 - (1 + u) * (-u).exp()
            require("positive heat remainder", value >= 0)
            return value

        for n in range(2, head_size + 1):
            v = Q(n).log()
            mass = (-c * v + tlo * (v * v / 4 - v * maximum(l0, v) / 2)).exp() * H(v)
            require("nonnegative heat term", mass >= 0)
            head[0] += mass
            head[1] += v * mass
        for i in range(cells):
            left, right = lv + i * dv, lv + (i + 1) * dv
            decrease = (
                -(c - 1) * left + tlo * (left * left / 4 - left * maximum(l0, left) / 2)
            ).exp()
            mass = dv * decrease * H(right)
            integral[0] += mass
            integral[1] += right * mass
        end = lv + cells * dv
        q = c - 1 + tlo * end / 2
        require("heat infinite-tail domain", end > l0 and q > 0)
        pref = (-(c - 1) * end - tlo * end * end / 4).exp()
        tail = [pref / q, pref * (end / q + 1 / (q * q))]
        value = [head[k] + integral[k] + tail[k] for k in range(2)]
        return value, {
            "finite_head": list(map(text, head)),
            "log_cell_integrals": list(map(text, integral)),
            "infinite_tails": list(map(text, tail)),
            "tail_start": text(end),
            "tail_rate": text(q),
            "moment_bounds": list(map(text, value)),
        }

    def ordinary(a, k):
        require("ordinary-tail integral-test gates", a > 1 and a > Q(k) / l0)
        value = arb(0)
        for j in range(k + 1):
            value += Q(factorial(k) // factorial(k - j)) * l0 ** (k - j) / (a - 1) ** (j + 1)
        return ((1 - a) * l0).exp() * value

    def reflected(c, y):
        y = Q(y)
        b = c - y - kappa * y
        dec, effective = 1 - b, b + y
        require("reflected prefix positive exponent", dec > 0)
        k0 = (1 - (-dec * l0).exp()) / dec
        prefix_gate = (y - 1 / (l0 + beta)) * k0 - 1
        require("reflected all-N prefix", prefix_gate > 0)
        require("reflected all-N effective exponent", effective * (l0 + beta) > 1)
        a = b + tlo * l0 / 2
        require("reflected right-rectangle monotonicity", 1 - a > 0)
        step, integral = l0 / reflected_cells, arb(0)
        for k in range(1, reflected_cells + 1):
            v = k * step
            integral += step * ((1 - a) * v + tlo * v * v / 4).exp()
        endpoint = (-a * l0 + tlo * l0 * l0 / 4).exp()
        pref = (dg * y - y * l0).exp()
        mass = pref * (1 + integral + endpoint)
        require("positive reflected bound", mass > 0)
        value = [mass, (l0 + beta) * mass]
        return value, {
            "prefix_gate": text(prefix_gate),
            "effective_gate": text(effective * (l0 + beta)),
            "prefix_integral": text(integral),
            "both_endpoints": ["1", text(endpoint)],
            "gamma_prefactor": text(pref),
            "raw_jet_bounds": list(map(text, value)),
        }

    def source(yl, yh):
        yd, yu = yl - rsf, yh + rsf
        require("complete H7 disk Y domain", 0 < yd < yu < 7)
        inflation = (
            2 * ((Q(yu) * log3).exp() + (-Q(yu) * log3).exp()) / (685205 - 1) + Q("1e-10") + v7
        )

        def remainder(lower):
            return (-Q((1 + lower) / 4) * le - tlo * le * le / 16 + inflation).exp()

        power = -Q((1 + yd) / 2) + corr + cap
        require("primary cutoff decreasing exponent", power < 0)
        cut = (power * l0 - tlo * l0 * l0 / 4 + tm * (n0 + 1).log() / (2 * n0)).exp()
        ratio = (dg * Q(yu) + Q(yu) * (1 + 1 / n0).log() + kappa * Q(yu) * (n0 + 1).log()).exp()
        point, disk = remainder(yl), remainder(yd)
        raw = [Q("3e-9") + point, (Q("3e-9") + disk + cut * (1 + ratio)) / rs]
        return raw, {
            "Y_disk": [str(yd), str(yu)],
            "inflation": text(inflation),
            "point_C_error": text(point),
            "disk_C_error": text(disk),
            "cutoff_changes": [text(cut), text(cut * ratio)],
            "Cauchy_radius": str(rsf),
            "raw_jet_bounds": list(map(text, raw)),
        }

    for j in range(3):
        yl, yh = (j + 3) * hl, (j + 3) * hh
        a = a_first + Q(j * hl / 2)
        c = Q((1 + yl) / 2) - cap - corr
        require("reference analytic neighbourhood", a - rate * rs > 1)
        heat_jet, heat_record = heat(c)
        moments = [ordinary(a, k) for k in range(4)]
        taylor = [moments[0] + thi * moments[2] / 4, moments[1] + thi * moments[3] / 4]
        ref, ref_record = reflected(c, yl)
        src, src_record = source(yl, yh)
        raw0 = heat_jet[0] + taylor[0] + ref[0] + src[0]
        raw1 = rate * (heat_jet[1] + taylor[1]) + ref[1] + src[1]
        zeta = arb_series([a, arb(1)], 5).zeta()
        require("positive real zeta value", zeta[0] > 0)
        ell = zeta.log()
        W = [Q((-1) ** (k + 1) * factorial(k + 1)) * ell[k + 1] for k in range(4)]
        require("positive logarithmic zeta moments", all(w > 0 for w in W))
        modulus = (2 * a).zeta() / zeta[0]
        require("positive Euler-product lower modulus", modulus > 0)
        z0 = W[1] + W[0] * W[0]
        z1 = W[2] + 2 * W[0] * W[1]
        z2 = W[3] + 2 * W[1] * W[1] + 2 * W[0] * W[2]
        v0, v1 = W[0] + thi * z1 / 4, W[1] + thi * z2 / 4
        e0, e1 = raw0 / modulus, (raw1 + rate * W[0] * raw0) / modulus
        w0, w1 = thi * z0 / 4, thi * rate * z1 / 4
        rho = w0 + e0
        require("additive-Q strictly positive denominator", rho < 1)
        error = (e1 + w1 * rho) / (1 - rho)
        require("nonnegative normalization bound", error >= 0)
        numerical.append((v0, v1, error))
        bands.append(
            {
                "probe": j + 3,
                "Y_interval": [str(yl), str(yh)],
                "c_lower": text(c),
                "a_lower": text(a),
                "reference_neighbourhood_margin": text(a - rate * rs - 1),
                "heat": heat_record,
                "ordinary_tail_moments": list(map(text, moments)),
                "ordinary_Taylor_tail": list(map(text, taylor)),
                "reflected": ref_record,
                "source": src_record,
                "raw_R0": text(raw0),
                "raw_R1": text(raw1),
                "W": list(map(text, W)),
                "Euler_product_lower_modulus": text(modulus),
                "Z": [text(z0), text(z1), text(z2)],
                "V0": text(v0),
                "V1": text(v1),
                "relative_error": [text(e0), text(e1)],
                "heat_reference": [text(w0), text(w1)],
                "Q_defect_upper": text(rho),
                "Q_denominator_lower": text(1 - rho),
                "Q_log_derivative_error": text(error),
                "all_gates": True,
            }
        )
    aa, bb, dd, mu = Q("15/14"), Q("16/21"), Q("1/6"), Q("10/21")
    eps2, eps3 = thi * Q(hh) / (4 * (xe - 6)), thi * Q(hh) / (2 * (xe - 6))
    # One coherent positive-coefficient Dirichlet majorant; the negative
    # middle term uses ordinary signed interval arithmetic, including radii.
    main = (aa * numerical[0][0] - bb * numerical[1][0] + dd * numerical[2][0]) / 2
    require("positive coherent main cost", main > 0)
    argument = (bb * eps2 * numerical[1][1] + dd * eps3 * numerical[2][1]) / 2
    spatial = eta * (aa * numerical[0][0] + bb * numerical[1][0] + dd * numerical[2][0])
    normalization = aa * numerical[0][2] + bb * numerical[1][2] + dd * numerical[2][2]
    lower = mu * omega - main - argument - spatial - 2 * arch - normalization
    require("published strict floor " + box["id"], lower > Q(box["floor"]))
    return {
        "id": box["id"],
        "t_interval": box["t_interval"],
        "h_interval": box["h_interval"],
        "floor": box["floor"],
        "complete": True,
        "bands": bands,
        "global": {
            "logN0": text(l0),
            "Le": text(le),
            "cap": text(cap),
            "corr": text(corr),
            "kappa": text(kappa),
            "dg": text(dg),
            "arch_error": text(arch),
            "eta": text(eta),
            "rate": text(rate),
            "phase": text(phase),
            "cutoff_variation": text(cutoff_variation),
        },
        "joint_costs": {
            "main": text(main),
            "argument": text(argument),
            "spatial": text(spatial),
            "arch": text(2 * arch),
            "normalization": text(normalization),
        },
        "uniform_lower_expression": text(lower),
        "strict_floor_margin": text(lower - Q(box["floor"])),
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    if args.output and args.output.exists():
        raise SystemExit("Refuse to overwrite result")
    ctx.prec, ctx.cap = 384, 10
    path = Path(__file__).with_name("boxes.json")
    data = json.loads(path.read_text())
    expected = {
        "x_min": "5999347341500",
        "N_min": 690950,
        "weights": ["15/14", "-16/21", "1/6"],
        "height_multipliers": [3, 4, 5],
        "bits": 384,
        "source_radius": "1/20",
        "heat_head": 1024,
        "heat_log_cells": 1024,
        "heat_log_step": "1/16",
        "reflected_integral_cells": 1024,
        "series_truncation": 5,
        "ctx_cap": 10,
        "normalization": "additive_Q",
    }
    require("pinned recipe", all(data.get(k) == v for k, v in expected.items()))
    require(
        "exact 26 case ids",
        [b["id"] for b in data["boxes"]] == ["A"] + [f"{i:02}" for i in range(1, 26)],
    )
    started, results = time.monotonic(), []
    for box in data["boxes"]:
        result = evaluate(box)
        results.append(result)
        print(
            f"{box['id']}: V > {box['floor']}; lower {result['uniform_lower_expression']}",
            flush=True,
        )
    result = {
        "complete": True,
        "box_count": len(results),
        "probe_count": 3 * len(results),
        "precision_bits": ctx.prec,
        "python_flint": flint.__version__,
        "flint_version": flint.__FLINT_VERSION__,
        "python": sys.version,
        "normalization": "additive_Q only; no field/wall input",
        "inputs_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "evaluator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "elapsed_seconds": time.monotonic() - started,
        "boxes": results,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        with args.output.open("x") as f:
            json.dump(result, f, indent=2)
            f.write("\n")
    print(
        f"All {len(results)} closed source boxes passed at {ctx.prec} bits in {result['elapsed_seconds']:.2f}s"
    )


if __name__ == "__main__":
    main()
