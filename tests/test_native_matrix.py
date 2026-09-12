"""Small native-generator checks with ASan/UBSan and independent finite sums.

These exercise the exact lower and upper index boundaries, matrix initialization,
normalization, and early failure paths. They do not replace full regeneration.
The reproduction image includes the required compiler and FLINT headers.
"""

import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from flint import acb, arb, ctx

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("dbn_native_matrix", ROOT / "support/head/matrix.py")
matrix = importlib.util.module_from_spec(spec)
spec.loader.exec_module(matrix)


class NativeMatrixTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(prefix="dbn-native-test-")
        cls.tmp = Path(cls.directory.name)
        cls.binary = cls.tmp / "generator"
        cls.env = os.environ.copy()
        cls.env["ASAN_OPTIONS"] = "detect_leaks=1:halt_on_error=1"
        cls.env["UBSAN_OPTIONS"] = "halt_on_error=1:print_stacktrace=1"
        result = subprocess.run(
            [
                "gcc",
                "-O1",
                "-g",
                "-Wall",
                "-Wextra",
                "-Werror",
                "-fsanitize=address,undefined",
                "-fno-omit-frame-pointer",
                "-o",
                str(cls.binary),
                str(ROOT / "support/head/generate-matrix.c"),
                "-lflint",
                "-lgmp",
                "-lmpfr",
            ],
            capture_output=True,
            text=True,
        )
        if result.returncode:
            raise RuntimeError("Sanitized generator compilation failed:\n" + result.stderr)

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def test_endpoint_partitions_against_direct_finite_sums(self):
        previous = ctx.prec
        ctx.prec = 256
        try:
            for first, last in [(1, 3), (690948, 690950)]:
                with self.subTest(first=first, last=last):
                    output = self.tmp / f"matrix-{first}-{last}.txt"
                    result = subprocess.run(
                        [str(self.binary), str(first), str(last), str(output)],
                        env=self.env,
                        capture_output=True,
                        text=True,
                    )
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertNotIn("Sanitizer", result.stderr)
                    extent, values = matrix.read_matrix(output)
                    self.assertEqual(extent, (first, last))
                    direct = [[acb(0) for _ in range(62)] for _ in range(62)]
                    exponent = acb(matrix.rational("-1/2"), matrix.rational(matrix.XM / 2))
                    for n in range(first, last + 1):
                        ell = (arb(n) / 345475).log()
                        phase = (exponent * arb(n).log()).exp()
                        ev, kv = [arb(1)], [arb(1)]
                        for k in range(1, 62):
                            ev.append(ev[-1] * ell / k)
                            kv.append(kv[-1] * ell**2 / (4 * k))
                        for e in range(62):
                            for k in range(62):
                                direct[e][k] += phase * ev[e] * kv[k]
                    for e in range(62):
                        for k in range(62):
                            self.assertTrue(
                                values[e][k].overlaps(direct[e][k]),
                                f"partition {first}:{last}, entry {e},{k}",
                            )
        finally:
            ctx.prec = previous

    def test_invalid_inputs_and_existing_output_are_rejected_cleanly(self):
        existing = self.tmp / "existing.txt"
        existing.write_text("retain this file\n")
        for arguments in [
            [],
            ["0", "2", str(self.tmp / "invalid-0")],
            ["1", "690951", str(self.tmp / "invalid-hi")],
            ["3", "2", str(self.tmp / "invalid-order")],
            ["bad", "2", str(self.tmp / "invalid-text")],
            ["1", "1", str(existing)],
        ]:
            with self.subTest(arguments=arguments):
                result = subprocess.run(
                    [str(self.binary), *arguments], env=self.env, capture_output=True, text=True
                )
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertNotIn("Sanitizer", result.stderr)
        self.assertEqual(existing.read_text(), "retain this file\n")


if __name__ == "__main__":
    unittest.main()
