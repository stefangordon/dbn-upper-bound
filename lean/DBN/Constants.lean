import Mathlib.Tactic.NormNum
import Mathlib.Data.Rat.Defs

/-!
# Exact constants of the de Bruijn–Newman upper bound

All constants are exact rationals. The headline bound is

  Λ ≤ bound = 3885632262767861213460393068710302759 / 24646172707879668706230182733520000000
            ≈ 0.157656619095490606768…

and `bound = T + 1/800`, where `T` is the terminal time of the barrier `Q` (with `Q(T) = 1/400`)
and `1/800 = (1/400)/2` is the global de Bruijn strip contraction.
-/

namespace DBN.Const

/-- Exact upper bound for Λ proved by the barrier argument. -/
def bound : ℚ := 3885632262767861213460393068710302759 / 24646172707879668706230182733520000000
/-- Terminal time of the barrier (last row ends here with `Q(T) = 1/400`). -/
def T : ℚ := 3854824546883011627577605340293402759 / 24646172707879668706230182733520000000
/-- Terminal squared height `Q(T)`. -/
def qFinal : ℚ := 1 / 400
/-- de Bruijn tail `qFinal / 2`. -/
def tail : ℚ := 1 / 800

/-- Start of the box-A source row (end of the `q_bk + 10⁻⁹` prefix). -/
def aT : ℚ := 3 / 50
/-- Barrier value at `aT`: `q_bk(3/50) + 10⁻⁹`. -/
def aQ : ℚ := 84648870770133 / 200000000000000
/-- Entry point of the ALL source rows. -/
def allEntryT : ℚ := 601 / 10000
def allEntryQ : ℚ := 84496870770133 / 200000000000000
/-- Cut point: right endpoint of literal ALL row 224 = entry of the FORWARD rows. -/
def entryT : ℚ := 323 / 5000
def entryQ : ℚ := 388898651933663 / 1000000000000000

/-- Horizon of the M3a density/jet fields (`T_M`). -/
def TM : ℚ := 10724023263453313712965415492196719802951 / 66207211195936838001560220771250000000000
/-- Terminal time of the fullC 7849-row reference barrier `q_bk`. -/
def Tstar : ℚ := 3727212594484883717859635359632643731427893093 / 23745856366798857962956857522257275000000000000
/-- Lower bound `Ω_L < Ω(x) = log(x/(4π))/4` valid for all `x ≥ X_L`. -/
def OmegaL : ℚ := 6722911 / 1000000
/-- Source-law constant `a = 2/15` in `q' ≤ -2/15 - 4√q V`. -/
def sourceA : ℚ := 2 / 15
/-- Initial squared height of the fullC barrier, `(1000001/1000000)²`. -/
def q0 : ℚ := 1000002000001 / 1000000000000

/-- Finite head abscissa: every zero with `|Re z| ≤ X` is real for `t ∈ [0, 1/5]` (premise H4). -/
def X : ℕ := 5999347341500
def XL : ℕ := 5999346341500
def Xe : ℕ := 5900000000000

theorem T_add_tail : T + tail = bound := by norm_num [T, tail, bound]
theorem qFinal_half : qFinal / 2 = tail := by norm_num [qFinal, tail]
theorem bound_lt_79_500 : bound < 79 / 500 := by norm_num [bound]
theorem T_lt_Tstar : T < Tstar := by norm_num [T, Tstar]
theorem Tstar_lt_TM : Tstar < TM := by norm_num [Tstar, TM]
theorem TM_lt_fifth : TM < 1 / 5 := by norm_num [TM]
theorem aT_lt_allEntryT : aT < allEntryT := by norm_num [aT, allEntryT]
theorem allEntryT_lt_entryT : allEntryT < entryT := by norm_num [allEntryT, entryT]
theorem entryT_lt_T : entryT < T := by norm_num [entryT, T]
/-- The box-A row: `aQ - (38/5)(601/10000 - 3/50) = allEntryQ`. -/
theorem aRow_end : aQ - 38 / 5 * (allEntryT - aT) = allEntryQ := by
  norm_num [aQ, allEntryT, aT, allEntryQ]

end DBN.Const
