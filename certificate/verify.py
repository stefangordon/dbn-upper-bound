#!/usr/bin/env python3
"""Check the finite barrier certificate, optionally including P8 profiles.

For the supporting computations use ../verify.py. Success here alone does not
establish the analytic inputs to the main theorem.
"""

import argparse
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def module(name, file):
    spec = importlib.util.spec_from_file_location(name, HERE / file)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--with-flint", action="store_true", help="all P8 profiles with Arb at 512 bits"
    )
    parser.add_argument(
        "--with-mpmath",
        action="store_true",
        help="all P8 profiles with mpmath intervals at 80 digits",
    )
    parser.add_argument("--output", type=Path, help="optional JSON report; no input is modified")
    args = parser.parse_args()
    try:
        checker = module("dbn_exact", "check.py")
        data = checker.load()
        results = dict(exact=checker.check(data))
        print(
            "PASS: exact conditions for 12666 barrier rows, 1620 wall cells, and 26 source boxes.",
            flush=True,
        )
        if args.with_flint or args.with_mpmath:
            profiles = module("dbn_profiles", "profiles.py")
            if args.with_flint:
                results["arb"] = profiles.arb_profiles(data)
                print("PASS: 7849 density floors and 6317 jet ceilings, Arb 512 bits.", flush=True)
            if args.with_mpmath:
                results["mpmath"] = profiles.mpmath_profiles(data)
                print(
                    "PASS: the same profile inequalities, mpmath intervals at 80 digits.",
                    flush=True,
                )
        report = dict(
            status="PASS",
            scope="finite certificate only; supporting analytic estimates are separate",
            results=results,
        )
        if args.output:
            args.output.write_text(json.dumps(report, indent=2) + "\n")
        print("All requested finite checks passed. This does not verify the full analytic proof.")
        return 0
    except (ValueError, TypeError, KeyError, OSError, ImportError, ZeroDivisionError) as error:
        parser.exit(1, f"FAIL: {error}\n")


if __name__ == "__main__":
    raise SystemExit(main())
