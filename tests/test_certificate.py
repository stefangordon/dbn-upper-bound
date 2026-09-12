"""Adversarial tests for coverage, strictness, and certificate identity."""

import copy
from fractions import Fraction as Q
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("dbn_test_exact", ROOT / "certificate/check.py")
exact = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exact)


class CertificateRejectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.valid = exact.load()

    def rejected(self, mutation, message):
        altered = copy.deepcopy(self.valid)
        mutation(altered)
        with self.assertRaisesRegex(exact.InvalidCertificate, message):
            exact.check(altered)

    def test_valid_certificate(self):
        result = exact.check(self.valid)
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(result["minimum_field_speed_slack"], "0")

    def test_missing_row(self):
        self.rejected(lambda d: d["main"].pop(), "wrong item count")

    def test_gap_cannot_be_hidden_by_valid_row_count(self):
        self.rejected(
            lambda d: d["main"][20].update(tl=str(Q(d["main"][20]["tl"]) + Q(1, 10**10))),
            "broken time/height join",
        )

    def test_wrong_source_floor(self):
        self.rejected(lambda d: d["sources"][0].update(L="1/1000000"), "strict source speed gate")

    def test_source_box_does_not_cover_whole_row(self):
        self.rejected(
            lambda d: d["sources"][0].update(btr="6001/100000"), "source time containment"
        )

    def test_wrong_field_reference(self):
        def mutation(d):
            row = next(row for row in d["main"] if "field" in row)
            row["field"] += 1

        self.rejected(mutation, "field time domain")

    def test_wrong_wall_value(self):
        self.rejected(lambda d: d["reference"][100]["field"].update(qM="0"), "wall interpolation")

    def test_negative_index_rejected(self):
        self.rejected(lambda d: d["main"][0].update(source=-1), "index outside")

    def test_boolean_is_not_index(self):
        self.rejected(lambda d: d["main"][0].update(source=False), "index outside")

    def test_changed_theorem_cannot_pass_by_self_consistency(self):
        self.rejected(lambda d: d["constants"].update(bound="1/2"), "wrong theorem constant")

    def test_duplicate_json_keys_rejected(self):
        with self.assertRaisesRegex(exact.InvalidCertificate, "duplicate JSON key"):
            json.loads('{"tl":"0","tl":"1"}', object_pairs_hook=exact.unique_object)

    def test_optimization_does_not_disable_acceptance_gates(self):
        code = (
            "import importlib.util; "
            f's=importlib.util.spec_from_file_location("check", {str(ROOT / "certificate/check.py")!r}); '
            "m=importlib.util.module_from_spec(s); s.loader.exec_module(m); "
            'm.require(False,"deliberate failure")'
        )
        result = subprocess.run([sys.executable, "-O", "-c", code], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("deliberate failure", result.stderr)


if __name__ == "__main__":
    unittest.main()
