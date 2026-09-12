import DBN.Profile
import DBN.Data.fullCRows

/-!
# Bounded kernel checks of difficult P8 endpoints

This file does **not** prove P8 for all 7849 reference rows. It checks the
smallest density margin (row 1251), the smallest jet margin (row 5845), and
both gates at row 3356, where applying the subtraction budget twice would
give a false claim. The row indices are zero-based.

The tuple theorems connect the explicit rational inputs below to the actual
frozen Lean row data. Each numerical certificate is reduced by the kernel;
there is no native verification fallback.
-/

noncomputable section

namespace DBN.Profile

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def endpointTuple (index : ℕ) : Option (ℚ × ℚ × ℚ × ℚ × ℚ × Bool) :=
  Data.fullCRows[index]?.bind fun r =>
    match r.cert with
    | .source _ => none
    | .field c => some (c.p, c.otl, c.otr, c.s, c.c, c.signed)

theorem row1251_tuple : endpointTuple 1251 = some
    (25539970073 / 10000000000, 1251 / 50000, 313 / 12500,
      6390599493443 / 1000000000000, 223078041611 / 500000000000, true) := by decide +kernel

theorem row3356_tuple : endpointTuple 3356 = some
    (21470723757 / 10000000000, 839 / 12500, 3357 / 50000,
      6406602920893 / 1000000000000, 155260644091 / 250000000000, true) := by decide +kernel

theorem row5845_tuple : endpointTuple 5845 = some
    (17715176601 / 10000000000, 1169 / 10000, 2923 / 25000,
      402706945987 / 62500000000, 746047205329 / 1000000000000, true) := by decide +kernel

/-- Smallest density margin in the conventional interval audit, approximately `4·10⁻¹²`. -/
theorem density_1251 :
    (6390599493443 / 1000000000000 : ℝ) + 1 / 100000 <
      f0 (25539970073 / 10000000000) (1251 / 50000) := by
  norm_num [f0, UY, U]
  interval_decide 20 (trust := kernel)
  all_goals simp only [div_eq_mul_inv]

theorem density_3356 :
    (6406602920893 / 1000000000000 : ℝ) + 1 / 100000 <
      f0 (21470723757 / 10000000000) (839 / 12500) := by
  norm_num [f0, UY, U]
  interval_decide 20 (trust := kernel)
  all_goals simp only [div_eq_mul_inv]

theorem jet_3356 :
    Cceil (21470723757 / 10000000000) (839 / 12500) (3357 / 50000) ≤
      (155260644091 / 250000000000 : ℝ) := by
  norm_num [Cceil, U]
  interval_decide 20 (trust := kernel)
  all_goals simp only [div_eq_mul_inv]

/-- Smallest jet margin in the conventional interval audit, approximately `4·10⁻¹²`. -/
theorem jet_5845 :
    Cceil (17715176601 / 10000000000) (1169 / 10000) (2923 / 25000) ≤
      (746047205329 / 1000000000000 : ℝ) := by
  norm_num [Cceil, U]
  interval_decide 20 (trust := kernel)
  all_goals simp only [div_eq_mul_inv]

/-- The stronger gate printed in an earlier manuscript is false at row 3356:
it subtracts `delta` inside `fM` and then the entire `10⁻⁵` budget once more. -/
theorem overderated_3356_false :
    ¬ ((6406602920893 / 1000000000000 : ℝ) <
      fM (21470723757 / 10000000000) (839 / 12500) - 1 / 100000) := by
  apply not_lt.mpr
  norm_num [fM, f0, delta, UY, U]
  rw [← sub_nonpos]
  interval_decide 20 (trust := kernel)
  all_goals simp only [div_eq_mul_inv, one_mul]

end DBN.Profile

end
