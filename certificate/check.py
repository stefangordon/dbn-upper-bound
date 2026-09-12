#!/usr/bin/env python3
"""Exact mathematical checker for the DBN barrier certificate.

The predicates correspond to DBN.Certificate.RowSpec, Chain, checkCatalog and
checkWallTrace. Acceptance verifies a finite implication: the specified analytic
floors imply the barrier comparison. It does not establish those analytic floors.
No producer log, claimed acceptance status, or stored floating-point value is used.
"""

from collections import Counter
from fractions import Fraction as Q
import json
from pathlib import Path

DATA = Path(__file__).resolve().parent / "data/barriers.json"
BOUND = Q("3885632262767861213460393068710302759/24646172707879668706230182733520000000")
T = Q("3854824546883011627577605340293402759/24646172707879668706230182733520000000")
TSTAR = Q(
    "3727212594484883717859635359632643731427893093/23745856366798857962956857522257275000000000000"
)
TM = Q("10724023263453313712965415492196719802951/66207211195936838001560220771250000000000")
OMEGA = Q("6722911/1000000")
QFINAL = Q("1/400")
QINITIAL = Q("1000002000001/1000000000000")
START = Q("3/50")
ENTRY = Q("84648870770133/200000000000000")
TAU = Q("20000010/238529173356019")


class InvalidCertificate(ValueError):
    """A mathematical predicate or data schema failed."""


def require(condition, message):
    # Deliberately not a Python assertion: optimization must not disable checks.
    if not condition:
        raise InvalidCertificate(message)


def unique_object(pairs):
    value = {}
    for key, item in pairs:
        require(key not in value, f"duplicate JSON key: {key}")
        value[key] = item
    return value


def load(path=DATA):
    return json.loads(Path(path).read_text(), object_pairs_hook=unique_object)


def rational(value):
    require(isinstance(value, str), f"rational must be an exact string, got {value!r}")
    try:
        result = Q(value)
    except (ValueError, ZeroDivisionError) as error:
        raise InvalidCertificate(f"invalid rational: {value!r}") from error
    require(str(result) == value, f"rational must be canonical, got {value!r}")
    return result


def fields(record, expected, where):
    require(
        isinstance(record, dict) and set(record) == set(expected.split()),
        f"{where}: unexpected fields",
    )


def index(value, size, where):
    require(type(value) is int and 0 <= value < size, f"{where}: index outside [0,{size})")
    return value


def segment(row):
    return tuple(rational(row[key]) for key in ("tl", "tr", "qL", "qR"))


def affine(row, t):
    tl, tr, ql, qr = segment(row)
    require(tl < tr and tl <= t <= tr, "affine lookup outside its proper cell")
    return ql + (qr - ql) * (t - tl) / (tr - tl)


def check_chain(rows, first_t, first_q, last_t, last_q, where):
    require(bool(rows), f"{where}: empty chain")
    previous_t, previous_q = first_t, first_q
    for i, row in enumerate(rows):
        tl, tr, ql, qr = segment(row)
        require(tl == previous_t and ql == previous_q, f"{where}[{i}]: broken time/height join")
        require(tl < tr and 0 < qr <= ql, f"{where}[{i}]: invalid affine segment")
        previous_t, previous_q = tr, qr
    require((previous_t, previous_q) == (last_t, last_q), f"{where}: incorrect endpoint")


def check_source(row, source, where):
    tl, tr, ql, qr = segment(row)
    L, hlo, hhi, btl, btr = (rational(source[key]) for key in ("L", "hlo", "hhi", "btl", "btr"))
    require(btl <= tl < tr <= btr, f"{where}: source time containment")
    require(L > 0 and 0 < hlo < hhi, f"{where}: source positivity")
    require(hlo**2 <= qr < ql <= hhi**2, f"{where}: closed source height containment")
    w = (ql - qr) / (tr - tl)
    require(
        w <= Q(2, 15) or (w - Q(2, 15)) ** 2 < 16 * L**2 * qr, f"{where}: strict source speed gate"
    )


def check_field(row, field, wall, where):
    tl, tr, ql, qr = segment(row)
    p, s, c, qm, otl, otr = (rational(field[key]) for key in ("p", "s", "c", "qM", "otl", "otr"))
    require(
        otl <= tl < tr <= otr and otr - otl <= Q(1, 50000) and tr <= TM,
        f"{where}: field time domain",
    )
    require(0 < p <= 5 and s > 0 and 0 <= qm < p * p and ql < p * p, f"{where}: field probe domain")
    sg = wall[index(field["mIdx"], len(wall), where + ".mIdx")]
    require(qm == affine(sg, tl), f"{where}: incorrect wall interpolation")
    if field["signed"]:
        delta = OMEGA - s
        l0 = c - delta**2
        amax = p * (p * p - qr) / (3 * p * p - qr)
        require(c > 0 and delta > 0 and p >= Q(3, 5), f"{where}: signed positivity")
        require(qm <= (p - Q(3, 5)) ** 2 and 9 * ql <= p * p, f"{where}: signed probe separation")
        require(p * l0 <= s and 2 * amax * delta <= 1, f"{where}: signed monotonicity/Omega branch")
        k = 6 * s / p - 2 * l0 + ql * (2 * l0 / (p * p) - 2 * s / (p**3)) - 16 / (p * p - ql)
    else:
        require(c == 0, f"{where}: unused unsigned ceiling must be zero")
        require(5 * ql <= p * p, f"{where}: unsigned probe separation")
        k = 4 * s / p - 8 / (p * p - ql)
    require(k > 0, f"{where}: positive field coefficient")
    slack = 2 + k * qr - (ql - qr) / (tr - tl)
    require(slack >= 0, f"{where}: field speed gate")
    return slack


def check(data):
    fields(data, "schema_version constants sources wall reference main", "certificate")
    require(
        type(data["schema_version"]) is int and data["schema_version"] == 1, "unsupported schema"
    )
    expected = dict(
        bound=BOUND,
        T=T,
        Tstar=TSTAR,
        TM=TM,
        q0=QINITIAL,
        qFinal=QFINAL,
        aT=START,
        aQ=ENTRY,
        OmegaL=OMEGA,
        tau0=TAU,
    )
    constants = data["constants"]
    fields(constants, " ".join(expected) + " X XL", "constants")
    for key, value in expected.items():
        require(rational(constants[key]) == value, f"wrong theorem constant: {key}")
    require(type(constants["X"]) is int and constants["X"] == 5999347341500, "wrong X")
    require(type(constants["XL"]) is int and constants["XL"] == 5999346341500, "wrong XL")
    sources, wall, reference, main = (
        data[name] for name in ("sources", "wall", "reference", "main")
    )
    for name, rows, count in [
        ("sources", sources, 26),
        ("wall", wall, 1620),
        ("reference", reference, 7849),
        ("main", main, 4817),
    ]:
        require(isinstance(rows, list) and len(rows) == count, f"{name}: wrong item count")
    for i, source in enumerate(sources):
        fields(source, "id L hlo hhi btl btr", f"sources[{i}]")
        require(index(source["id"], 26, "source.id") == i, "source catalog order")
    for i, row in enumerate(wall):
        fields(row, "tl tr qL qR", f"wall[{i}]")
    check_chain(wall, Q(0), QINITIAL, TM, QFINAL, "wall")
    check_chain(reference, Q(0), QINITIAL, TSTAR, QFINAL, "reference")
    check_chain(main, START, ENTRY, T, QFINAL, "main")
    minimum_slack = None
    counts = {"reference": Counter(), "main": Counter()}
    source_counts = Counter()
    for i, row in enumerate(reference):
        where = f"reference[{i}]"
        fields(row, "tl tr qL qR field", where)
        field = row["field"]
        fields(field, "signed p s c qM mIdx otl otr oIdx", where + ".field")
        require(type(field["signed"]) is bool, f"{where}: signed must be boolean")
        require(
            index(field["oIdx"], len(reference), where + ".oIdx") == i, f"{where}: profile identity"
        )
        require(
            field["otl"] == row["tl"] and field["otr"] == row["tr"],
            f"{where}: profile cell identity",
        )
        tl, tr, ql, qr = segment(row)
        require(QFINAL <= qr < ql, f"{where}: barrier height range")
        slack = check_field(row, field, wall, where)
        minimum_slack = slack if minimum_slack is None else min(minimum_slack, slack)
        counts["reference"]["signed" if field["signed"] else "unsigned"] += 1
    for i, row in enumerate(main):
        where = f"main[{i}]"
        require(
            ("source" in row) != ("field" in row), f"{where}: exactly one certificate is required"
        )
        tl, tr, ql, qr = segment(row)
        require(QFINAL <= qr < ql, f"{where}: barrier height range")
        if "source" in row:
            fields(row, "tl tr qL qR source", where)
            j = index(row["source"], len(sources), where + ".source")
            check_source(row, sources[j], where)
            source_counts[j] += 1
            counts["main"]["source"] += 1
        else:
            fields(row, "tl tr qL qR field", where)
            field = reference[index(row["field"], len(reference), where + ".field")]["field"]
            slack = check_field(row, field, wall, where)
            minimum_slack = min(minimum_slack, slack)
            counts["main"]["signed" if field["signed"] else "unsigned"] += 1
    require(set(source_counts) == set(range(26)), "source catalog contains unused or missing boxes")
    require(counts["reference"] == {"signed": 6317, "unsigned": 1532}, "reference mode counts")
    require(counts["main"] == {"source": 541, "signed": 2772, "unsigned": 1504}, "main mode counts")
    require(reference[2999]["tr"] == str(START), "reference entry time")
    require(rational(reference[2999]["qR"]) + Q(1, 10**9) == ENTRY, "strict entry cushion")
    require(
        0 < TAU < rational(reference[0]["tr"]) and affine(reference[0], TAU) > 1,
        "positive initial-time cushion",
    )
    require(START < T < TSTAR < TM < Q(1, 5), "theorem time horizons")
    require(T + QFINAL / 2 == BOUND < Q(79, 500), "terminal de Bruijn arithmetic")
    return dict(
        status="PASS",
        scope="exact barrier predicates; analytic floors are separate inputs",
        reference_rows=len(reference),
        main_rows=len(main),
        wall_cells=len(wall),
        source_boxes=len(sources),
        mode_counts={key: dict(value) for key, value in counts.items()},
        minimum_field_speed_slack=str(minimum_slack),
        bound=str(BOUND),
    )


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=DATA)
    arguments = parser.parse_args()
    try:
        print(json.dumps(check(load(arguments.data)), indent=2))
    except (
        InvalidCertificate,
        KeyError,
        TypeError,
        ValueError,
        OSError,
        ZeroDivisionError,
    ) as error:
        parser.exit(1, f"FAIL: {error}\n")
