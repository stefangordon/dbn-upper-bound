"""Independent edge cases from the Lean row specification and proof interfaces.

These test semantic boundaries rather than an optimizer's particular choices:
closed height boxes, strict source force, nonstrict field force, exact index
binding, and gap/overlap rejection. No expensive analytic computation is run.
"""

import copy
from fractions import Fraction as Q
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("integration_exact", ROOT / "certificate/check.py")
exact = importlib.util.module_from_spec(spec)
spec.loader.exec_module(exact)


class SourceForceBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.source = {"id": 0, "L": "1", "hlo": "1", "hhi": "2", "btl": "0", "btr": "23"}
        self.row = {"tl": "0", "tr": "1", "qL": "4", "qR": "1", "source": 0}

    def test_both_closed_height_endpoints_are_admissible(self):
        # qR=hlo^2 and qL=hhi^2; strict force is supplied by the speed gate.
        exact.check_source(self.row, self.source, "closed-height witness")

    def test_source_force_equality_is_rejected(self):
        # sqrt(qR)=L=1, so the limiting speed is 2/15+4=62/15.
        self.row["tr"] = "45/62"
        with self.assertRaisesRegex(exact.InvalidCertificate, "strict source speed gate"):
            exact.check_source(self.row, self.source, "source equality")

    def test_one_sided_neighbourhood_of_source_force_boundary(self):
        limiting_time = Q(45, 62)
        self.row["tr"] = str(limiting_time + Q(1, 10**6))
        exact.check_source(self.row, self.source, "slower source")
        self.row["tr"] = str(limiting_time - Q(1, 10**6))
        with self.assertRaisesRegex(exact.InvalidCertificate, "strict source speed gate"):
            exact.check_source(self.row, self.source, "faster source")

    def test_speed_equal_to_base_term_needs_no_squaring(self):
        self.row["tr"] = "45/2"
        exact.check_source(self.row, self.source, "base speed")


class FieldAndIdentityBoundaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = exact.load()
        cls.first_main_field = next(i for i, r in enumerate(cls.data["main"]) if "field" in r)
        cls.first_signed = next(
            i for i, r in enumerate(cls.data["reference"]) if r["field"]["signed"]
        )

    def rejected(self, mutation, message):
        data = copy.deepcopy(self.data)
        mutation(data)
        with self.assertRaisesRegex(exact.InvalidCertificate, message):
            exact.check(data)

    def test_terminal_field_zero_slack_is_admissible(self):
        row = self.data["main"][-1]
        field = self.data["reference"][row["field"]]["field"]
        slack = exact.check_field(row, field, self.data["wall"], "terminal equality")
        self.assertEqual(slack, Q(0))

    def test_speed_above_terminal_field_limit_is_rejected(self):
        row = copy.deepcopy(self.data["main"][-1])
        field = self.data["reference"][row["field"]]["field"]
        row["qR"] = str(Q(row["qR"]) - Q(1, 10**30))
        # Isolate the speed predicate; full check additionally rejects qR<qFinal.
        with self.assertRaisesRegex(exact.InvalidCertificate, "field speed gate"):
            exact.check_field(row, field, self.data["wall"], "faster terminal row")

    def test_omega_branch_strict_positive_gap_is_required(self):
        row = self.data["reference"][self.first_signed]
        field = copy.deepcopy(row["field"])
        field["s"] = str(exact.OMEGA)
        with self.assertRaisesRegex(exact.InvalidCertificate, "signed positivity"):
            exact.check_field(row, field, self.data["wall"], "zero Omega gap")

    def test_signed_monotonicity_cannot_be_dropped(self):
        row = self.data["reference"][self.first_signed]
        field = copy.deepcopy(row["field"])
        field["c"] = "1000000000"
        with self.assertRaisesRegex(exact.InvalidCertificate, "signed monotonicity/Omega branch"):
            exact.check_field(row, field, self.data["wall"], "invalid signed monotonicity")

    def test_boolean_field_index_is_not_zero(self):
        self.rejected(
            lambda d: d["main"][self.first_main_field].update(field=False), "index outside"
        )

    def test_boolean_wall_index_is_not_one(self):
        self.rejected(lambda d: d["reference"][0]["field"].update(mIdx=True), "index outside")

    def test_field_index_cannot_alias_python_last_element(self):
        self.rejected(lambda d: d["main"][self.first_main_field].update(field=-1), "index outside")

    def test_field_record_cannot_claim_another_profile(self):
        self.rejected(lambda d: d["reference"][10]["field"].update(oIdx=11), "profile identity")

    def test_profile_time_must_equal_evaluated_time(self):
        self.rejected(
            lambda d: d["reference"][0]["field"].update(otl="1/100000000000000000000"),
            "profile cell identity",
        )

    def test_two_certificate_modes_on_one_row_are_rejected(self):
        self.rejected(
            lambda d: d["main"][self.first_main_field].update(source=0), "exactly one certificate"
        )

    def test_overlap_cannot_hide_behind_unchanged_row_count(self):
        def mutation(data):
            data["main"][11] = copy.deepcopy(data["main"][10])

        self.rejected(mutation, "broken time/height join")


if __name__ == "__main__":
    unittest.main()
