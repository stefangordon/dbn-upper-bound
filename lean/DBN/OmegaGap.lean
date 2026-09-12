import Mathlib
import DBN.Premises

/-!
# The `Ω`-gap: `Ω(x) > Ω_L` for all `x ≥ X`

`Ω(x) = log(x/(4π))/4` is increasing, so it suffices to show `Ω(X) > Ω_L = 6722911/10⁶`, i.e.
`exp(26.891644) < X/(4π)`. We bound `exp(26.891644) = e²⁶ · exp(0.891644)` from above with Mathlib's
`e < 2.7182818286` and a ten-term Taylor bound, and `X/(4π)` from below with `π < 3.141593`. The relative
margin is about `3.4·10⁻⁶`.
-/

namespace DBN

open Real

theorem exp_four_OmegaL_lt : Real.exp (4 * (Const.OmegaL : ℝ)) < (Const.X : ℝ) / (4 * π) := by
  have hO : (4 * (Const.OmegaL : ℝ)) = 26 + 0.891644 := by norm_num [Const.OmegaL]
  rw [hO, Real.exp_add]
  -- e^26 < 2.7182818286^26
  have h1 : Real.exp (26 : ℝ) = Real.exp 1 ^ 26 := by
    rw [Real.exp_one_pow]; norm_num
  have he : Real.exp 1 ^ 26 < (2.7182818286 : ℝ) ^ 26 :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  -- exp(0.891644) ≤ Taylor + remainder
  have hx1 : (0 : ℝ) ≤ 0.891644 := by norm_num
  have hx2 : (0.891644 : ℝ) ≤ 1 := by norm_num
  have hT := Real.exp_bound' hx1 hx2 (n := 10) (by norm_num)
  have hS : (∑ m ∈ Finset.range 10, (0.891644 : ℝ) ^ m / m.factorial) +
      (0.891644 : ℝ) ^ 10 * (10 + 1) / ((10 : ℕ).factorial * 10) < 2.4391364 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have hE : Real.exp 0.891644 < 2.4391364 := lt_of_le_of_lt hT hS
  -- X/(4π) > X/(4·3.141593)
  have hpi : (Const.X : ℝ) / (4 * 3.141593) < (Const.X : ℝ) / (4 * π) := by
    apply div_lt_div_of_pos_left (by norm_num [Const.X]) (by positivity)
    linarith [Real.pi_lt_d6]
  have hpos26 : (0 : ℝ) ≤ Real.exp 1 ^ 26 := by positivity
  calc Real.exp 26 * Real.exp 0.891644 = Real.exp 1 ^ 26 * Real.exp 0.891644 := by rw [h1]
    _ < (2.7182818286 : ℝ) ^ 26 * 2.4391364 := by
        apply mul_lt_mul'' he hE hpos26 (Real.exp_pos _).le
    _ < (Const.X : ℝ) / (4 * 3.141593) := by norm_num [Const.X]
    _ < (Const.X : ℝ) / (4 * π) := hpi

/-- **`Ω(x) > Ω_L` for all `x ≥ X`.** -/
theorem omegaGap_proved : ∀ x : ℝ, (Const.X : ℝ) ≤ x → (Const.OmegaL : ℝ) < Omega x := by
  intro x hx
  have hX : (0 : ℝ) < Const.X := by norm_num [Const.X]
  have hxpos : 0 < x := lt_of_lt_of_le hX hx
  have hq : 0 < x / (4 * π) := by positivity
  unfold Omega
  rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 4), mul_comm, Real.lt_log_iff_exp_lt hq]
  calc Real.exp (4 * (Const.OmegaL : ℝ)) < (Const.X : ℝ) / (4 * π) := exp_four_OmegaL_lt
    _ ≤ x / (4 * π) := by gcongr

end DBN
