#!/usr/bin/env python3
"""Bind independently checked support data to the exact barrier inputs."""

from fractions import Fraction as Q
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("dbn_support_exact", HERE / "check.py")
exact = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exact)


def check():
    data = exact.load()
    root = HERE.parent
    source = json.loads(
        (root / "support/source/boxes.json").read_text(), object_pairs_hook=exact.unique_object
    )
    exact.require(len(source["boxes"]) == len(data["sources"]) == 26, "source box count")
    for i, (box, certificate) in enumerate(zip(source["boxes"], data["sources"])):
        exact.require(box["id"] == ("A" if i == 0 else f"{i:02}"), "source id")
        exact.require(Q(box["floor"]) == Q(certificate["L"]), f"source[{i}]: floor mismatch")
        exact.require(
            list(map(Q, box["t_interval"])) == [Q(certificate["btl"]), Q(certificate["btr"])],
            f"source[{i}]: time-box mismatch",
        )
        exact.require(
            list(map(Q, box["h_interval"])) == [Q(certificate["hlo"]), Q(certificate["hhi"])],
            f"source[{i}]: height-box mismatch",
        )
    wall = json.loads(
        (HERE / "data/old-M3a-wall.json").read_text(), object_pairs_hook=exact.unique_object
    )
    exact.require(len(wall["rows"]) == len(data["wall"]) == 1620, "density wall count")
    for i, (old, row) in enumerate(zip(wall["rows"], data["wall"])):
        exact.require(
            tuple(Q(old[k]) for k in ("tlo", "thi", "q_start", "q_end")) == exact.segment(row),
            f"wall[{i}]: supporting density wall differs from barrier wall",
        )
    exact.require(Q(wall["terminal"]["time"]) == exact.TM, "density horizon mismatch")
    return dict(
        status="PASS",
        source_boxes=26,
        density_wall_cells=1620,
        scope="exact identity between support inputs and the Lean/barrier data",
    )


if __name__ == "__main__":
    print(json.dumps(check(), indent=2))
