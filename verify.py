#!/usr/bin/env python3
"""Reproduce the publication's numerical evidence.

Default: all barrier, profile, source, field, and finite-boundary checks.
--regenerate additionally rebuilds the finite-sum boundary matrix from scratch.
--quick checks only the finite barrier/profiles and their input identities.
The written analytic proofs and cited literature remain part of the argument;
a successful run is not a claim of complete formal verification.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from contextlib import contextmanager
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def write_failure(tmp, name, command, error, stdout="", stderr="", returncode=None):
    def as_text(value):
        return (
            value.decode(errors="replace") if isinstance(value, bytes) else value or ""
        )

    record = dict(
        stage=name,
        command=command,
        exception=type(error).__name__,
        message=str(error),
        returncode=returncode,
        stdout=as_text(stdout),
        stderr=as_text(stderr),
    )
    text = json.dumps(record, indent=2) + "\n"
    (tmp / (name + ".failure.json")).write_text(text)
    print(text, file=sys.stderr, flush=True)


@contextmanager
def retain_workspace(results):
    """Keep requested component records on success or any verification failure."""
    with tempfile.TemporaryDirectory(prefix="dbn-verify-") as directory:
        tmp = Path(directory)
        try:
            yield tmp
        except BaseException as error:
            write_failure(tmp, "verification", [], error)
            if results is not None:
                shutil.copytree(tmp, results)
            raise
        else:
            if results is not None:
                shutil.copytree(tmp, results)


def run_process(name, command, env, tmp, timeout=3600):
    try:
        process = subprocess.run(
            command, capture_output=True, text=True, env=env, timeout=timeout
        )
    except (OSError, subprocess.SubprocessError) as error:
        write_failure(
            tmp,
            name,
            command,
            error,
            getattr(error, "stdout", ""),
            getattr(error, "stderr", ""),
        )
        raise
    if process.returncode:
        error = ValueError(f"{name} failed with exit status {process.returncode}")
        write_failure(
            tmp,
            name,
            command,
            error,
            process.stdout,
            process.stderr,
            process.returncode,
        )
        raise error
    return process


def load_module(name, relative):
    spec = importlib.util.spec_from_file_location(name, ROOT / relative)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate(name, result):
    """Check completeness in addition to process success; reject partial replays."""
    if name == "certificate":
        require(result["status"] == "PASS", "finite certificate failed")
        require(result["results"]["exact"]["main_rows"] == 4817, "main row count")
        require(
            result["results"]["exact"]["reference_rows"] == 7849, "reference row count"
        )
        for backend in ["arb", "mpmath"]:
            require(
                result["results"][backend]["status"] == "PASS",
                f"{backend} profile check failed",
            )
            require(
                result["results"][backend]["density_floors"] == 7849,
                f"{backend} density count",
            )
            require(
                result["results"][backend]["jet_ceilings"] == 6317,
                f"{backend} ceiling count",
            )
    elif name == "source":
        require(
            result["complete"] is True
            and result["box_count"] == 26
            and result["probe_count"] == 78,
            "source replay incomplete",
        )
        require(len(result["boxes"]) == 26, "source output box count")
        require(
            [box["id"] for box in result["boxes"]]
            == ["A"] + [f"{i:02}" for i in range(1, 26)],
            "source result identities",
        )
        require(
            all(
                box["complete"] is True
                and [band["probe"] for band in box["bands"]] == [3, 4, 5]
                and all(band["all_gates"] is True for band in box["bands"])
                and len(box["bands"]) == 3
                for box in result["boxes"]
            ),
            "source result band completeness",
        )
    elif name == "head":
        require(
            result["complete"] is True and result["passed"] == 800000,
            "boundary replay incomplete",
        )
        require(
            result["X"] == 5999347341500
            and result["t_interval"] == ["0", "1/5"]
            and result["y_interval"] == ["0", "1"],
            "boundary replay has the wrong domain",
        )
        require(
            result["t_cells"] == 400
            and result["y_cells"] == 2000
            and result["denominator"] == 2000,
            "boundary grid count",
        )
    elif name == "direct-sums":
        require(
            result["complete"] is True and result["bits"] >= 256,
            "direct-sum check incomplete",
        )
        require(
            [(row["t"], row["y"], row["terms_per_sum"]) for row in result["checks"]]
            == [("0", "0", 690950), ("1/5", "1", 690950)],
            "direct-sum check scope",
        )
    elif name == "h7":
        require(result["status"] == "H7_SCALAR_GATES_PASS", "H7 scalar check failed")
    elif name == "density":
        require(
            result["status"] == "M3A_INITIAL_BOTTOM_AND_HEIGHT_GATES_PASS",
            "density check failed",
        )
        require(
            result["initial_leaves"] == 855
            and result["height_rows"] == 1620
            and result["bottom_cells"] == 1620,
            "density replay incomplete",
        )
    elif name == "jet":
        require(
            result["status"] == "FIXED_C_PROFILE_TOP_HEAD_AND_GEOMETRY_GATES_PASS",
            "jet profile check failed",
        )
        require(
            len(result["initial_cells"]) == 400
            and len(result["source_geometry_cells"]) == 162,
            "jet initial/geometry replay incomplete",
        )
    elif name == "early":
        require(
            result["status"] == "EARLY_BOUNDARY_45_BOXES_PASS"
            and result["completed"] is True,
            "early boundary replay incomplete",
        )
        require(
            [row["index"] for row in result["rows"]] == list(range(45)),
            "early boundary coverage",
        )
    elif name.startswith("late-"):
        first, last = map(int, name.split("-")[1:])
        require(
            result["status"] == "LATE_BOUNDARY_RANGE_PASS"
            and result["completed"] is True,
            "late boundary replay incomplete",
        )
        require(
            result["start"] == first and result["stop"] == last,
            "late boundary range mismatch",
        )
        require(
            [row["index"] for row in result["rows"]] == list(range(first, last)),
            "late boundary coverage",
        )
        require(
            all(len(row["wide"]) == len(row["centers"]) == 9 for row in result["rows"]),
            "late boundary cutoff-band coverage",
        )
    else:
        raise ValueError(f"unknown verification stage {name}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--quick",
        action="store_true",
        help="finite barrier/profiles only; supporting computations are skipped explicitly",
    )
    parser.add_argument(
        "--regenerate",
        action="store_true",
        help="regenerate the boundary matrix before checking its cells (requires gcc and libflint-dev)",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=3,
        help="simultaneous verification processes (1..8; default 3)",
    )
    parser.add_argument(
        "--output", type=Path, help="new JSON summary file; existing paths are refused"
    )
    parser.add_argument(
        "--results",
        type=Path,
        help="new directory for component records, including diagnostics if a run fails",
    )
    args = parser.parse_args()
    try:
        require(
            sys.implementation.name == "cpython" and sys.version_info[:2] == (3, 12),
            "the supported numerical profile is CPython 3.12; use the pinned Docker image",
        )
        require(
            not sys.flags.optimize,
            "run without Python optimization; some supporting checks use assertions",
        )
        require(1 <= args.jobs <= 8, "--jobs must be in 1..8")
        require(
            not (args.quick and args.regenerate),
            "--quick and --regenerate are incompatible",
        )
        require(
            args.output is None or not args.output.exists(),
            "result output must be a new file",
        )
        require(
            args.results is None or not args.results.exists(),
            "component record directory must be new",
        )
        manifest = load_module("dbn_release_manifest", "scripts/manifest.py")
        file_count = manifest.verify()
        manifest_digest = hashlib.sha256(
            (ROOT / "MANIFEST.json").read_bytes()
        ).hexdigest()
        identities = load_module(
            "dbn_support_identities", "certificate/check_support.py"
        ).check()
        subprocess.run(
            [sys.executable, str(ROOT / "scripts/build_paper.py"), "--check-table"],
            check=True,
        )
        subprocess.run(
            [sys.executable, str(ROOT / "scripts/build_paper.py"), "--check-pdf"],
            check=True,
        )
        subprocess.run(
            [sys.executable, str(ROOT / "lean/scripts/gen_data.py"), "--check"],
            check=True,
        )
        print(
            f"PASS: {file_count} release files, support identities, and generated Lean data.",
            flush=True,
        )
        began = time.monotonic()
        env = os.environ.copy()
        for key in [
            "PYTHONPATH",
            "PYTHONHOME",
            "PYTHONOPTIMIZE",
            "LD_PRELOAD",
            "LD_LIBRARY_PATH",
            "PYTHONMALLOC",
        ]:
            env.pop(key, None)
        env["PYTHONHASHSEED"] = "0"
        with retain_workspace(args.results) as tmp:
            matrix = ROOT / "support/head/data/matrix.txt"
            regenerated = None
            if args.regenerate:
                matrix = tmp / "matrix.txt"
                print(
                    "Regenerating the 3844 boundary matrix entries from all 690950 terms...",
                    flush=True,
                )
                command = [
                    sys.executable,
                    str(ROOT / "support/head/regenerate.py"),
                    "--output",
                    str(matrix),
                    "--jobs",
                    str(min(os.cpu_count() or 1, 8)),
                ]
                process = run_process("regeneration", command, env, tmp)
                try:
                    regenerated = json.loads(
                        matrix.with_suffix(".provenance.json").read_text()
                    )
                    require(
                        regenerated["complete"] is True
                        and regenerated["terms"] == 690950
                        and regenerated["entries"] == 3844,
                        "matrix regeneration incomplete",
                    )
                except Exception as error:
                    write_failure(
                        tmp,
                        "regeneration",
                        command,
                        error,
                        process.stdout,
                        process.stderr,
                        process.returncode,
                    )
                    raise
                print("PASS: fresh finite-sum matrix.", flush=True)
            phases = [
                (
                    "certificate",
                    "certificate/verify.py",
                    ["--with-flint", "--with-mpmath"],
                )
            ]
            if not args.quick:
                phases += [
                    ("source", "support/source/verify.py", []),
                    ("head", "support/head/verify.py", ["--matrix", str(matrix)]),
                    (
                        "direct-sums",
                        "support/head/spotcheck.py",
                        ["--matrix", str(matrix)],
                    ),
                    ("h7", "support/fields/check_h7.py", []),
                    ("density", "support/fields/check_m3a.py", []),
                    ("jet", "support/fields/check_fixed_c.py", []),
                    ("early", "support/fields/check_early_boundary.py", []),
                ]
                # Every independent late box has a fresh process. No numerical
                # state is carried between boxes; exact coverage is checked below.
                phases += [
                    (
                        f"late-{a}-{b}",
                        "support/fields/check_late_boundary.py",
                        ["--start", str(a), "--stop", str(b)],
                    )
                    for a, b in [(i, i + 1) for i in range(45, 162)]
                ]

            def run(phase):
                name, relative, extra = phase
                output = tmp / (name + ".json")
                command = [
                    sys.executable,
                    str(ROOT / relative),
                    *extra,
                    "--output",
                    str(output),
                ]
                process = run_process(name, command, env, tmp)
                try:
                    require(output.is_file(), f"{name}: missing result")
                    result = json.loads(output.read_text())
                    validate(name, result)
                except Exception as error:
                    write_failure(
                        tmp,
                        name,
                        command,
                        error,
                        process.stdout,
                        process.stderr,
                        process.returncode,
                    )
                    raise
                return name, result

            results = {}
            pool = ThreadPoolExecutor(max_workers=args.jobs)
            futures = [pool.submit(run, phase) for phase in phases]
            late_count = 0
            try:
                for future in as_completed(futures):
                    name, result = future.result()
                    results[name] = result
                    if name.startswith("late-"):
                        late_count += 1
                        if late_count % 20 == 0 or late_count == 117:
                            print(
                                f"PASS: late boundary {late_count}/117 independent boxes",
                                flush=True,
                            )
                    else:
                        print(f"PASS: {name}", flush=True)
            finally:
                pool.shutdown(wait=True, cancel_futures=True)
            if not args.quick:
                covered = [
                    row["index"]
                    for key in [f"late-{i}-{i + 1}" for i in range(45, 162)]
                    for row in results[key]["rows"]
                ]
                require(
                    covered == list(range(45, 162)),
                    "late ranges do not form an exact complete cover",
                )
                geometry = hashlib.sha256(
                    (ROOT / "support/fields/data/boundary-geometry.json").read_bytes()
                ).hexdigest()
                require(
                    results["jet"]["source_geometry_sha256"] == geometry
                    and results["early"]["input_geometry_sha256"] == geometry
                    and all(
                        results[key]["geometry_sha256"] == geometry
                        for key in results
                        if key.startswith("late-")
                    ),
                    "jet boundary computations use different geometries",
                )
            require(
                hashlib.sha256((ROOT / "MANIFEST.json").read_bytes()).hexdigest()
                == manifest_digest,
                "release manifest changed during verification",
            )
            manifest.verify()
            report = dict(
                status="PASS",
                scope="quick finite checks"
                if args.quick
                else "all supporting numerical checks",
                matrix_regenerated=bool(args.regenerate),
                release_files=file_count,
                release_manifest_sha256=manifest_digest,
                support_identities=identities,
                stages=sorted(results),
                elapsed_seconds=time.monotonic() - began,
                bound="3885632262767861213460393068710302759/24646172707879668706230182733520000000",
                formal_scope="conditional Lean theorem; analytic proofs and published inputs remain separate",
                numerical_python=sys.version,
                late_box_processes=0 if args.quick else 117,
            )
            if regenerated:
                report["matrix_regeneration"] = regenerated
            if args.output:
                args.output.parent.mkdir(parents=True, exist_ok=True)
                with args.output.open("x") as file:
                    json.dump(report, file, indent=2)
                    file.write("\n")
            print(json.dumps(report, indent=2))
            return 0
    except (
        ValueError,
        KeyError,
        TypeError,
        OSError,
        subprocess.SubprocessError,
        ImportError,
    ) as error:
        parser.exit(1, f"FAIL: {error}\n")


if __name__ == "__main__":
    raise SystemExit(main())
