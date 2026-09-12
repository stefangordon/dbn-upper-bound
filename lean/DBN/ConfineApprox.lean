import Mathlib
import DBN.Approximation
import DBN.GammaEstimate

/-!
# Positive-time confinement from the enlarged approximation

`P3` (positive-time confinement: on a compact positive time interval, zeros of height `≥ 1/40` have
bounded real part) is derived here from manuscript Lemma A.1 (`EnlargedApproximation`) alone, using
the crude bound `|γ| ≤ e^{1/10} 𝒬^{−y/2}` proved in `DBN.GammaEstimate`. This is the elementary
mechanism used in Polymath's Theorem 1.5(i), restricted here to heights at least `1/40`.
For `x > max X_e (4π e^{80/t₀})` and `t ≥ t₀`, the proved logarithmic estimates, including
the rational corrections to `Re s_A` and `Re s_B`, bound every term with
`2 ≤ n ≤ N(x,t)` in the two finite heated Dirichlet sums by `n^{−8}`. Thus
`P_N(s_B,t)` is within `1/64` of `1`, `P_N(s_A,t)` is at most `1 + 1/64`, and `|γ| ≤ e^{1/10} e^{−5}` at
heights `y ≥ 1/40`. Hence `|f^{[N]}| ≥ 9/10` while the approximation error is at most `1/10`, so
`H_t(x+iy) ≠ 0`. Negative real parts and negative heights reduce to this case by `H_t(−z) = H_t(z)`
and `H_t(z̄) = H_t(z)‾`, and the strip bound `|Im| ≤ 1` supplies the height range of Lemma A.1.

The theorem `confine_of_approximation` is stated for an arbitrary compact interval `[t₀, T] ⊂ (0, 1/5]`;
`DBN.Main` instantiates it on `[τ₀, T*]`.
-/

noncomputable section

namespace DBN

open Real Set Complex

namespace Approx

/-! ### A lower bound for `Re α` -/

theorem re_alpha_ge {s : ℂ} {x : ℝ} (hx : 0 < x) (hre : 0 ≤ s.re) (hre1 : s.re ≤ 1)
    (him : |s.im| = x / 2) :
    Real.log (x / (4 * π)) / 2 - (1 - s.re) * 4 / x ^ 2 ≤ (alpha s).re := by
  have hnorm : x / 2 ≤ ‖s‖ := him ▸ Complex.abs_im_le_norm s
  have himsq : s.im * s.im = (x / 2) ^ 2 := by
    rw [← sq, ← sq_abs, him]
  have hnsq : x ^ 2 / 4 ≤ normSq (s - 1) := by
    rw [normSq_apply]
    simp only [sub_re, sub_im, one_re, one_im, sub_zero]
    nlinarith [sq_nonneg (s.re - 1)]
  have hns : 0 < normSq s := by
    rw [normSq_apply]; nlinarith [sq_nonneg s.re]
  have h1 : (1 / (2 * s)).re = s.re / (2 * normSq s) := by
    rw [one_div, inv_re]
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, map_mul, normSq_ofNat]
    field_simp
  have h2 : (1 / (s - 1)).re = (s.re - 1) / normSq (s - 1) := by
    rw [one_div, inv_re]; simp
  have h3 : ((1 / 2 : ℂ) * Complex.log (s / (2 * (π : ℂ)))).re = Real.log (‖s‖ / (2 * π)) / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, re_ofReal_mul, log_re, norm_div,
      norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  unfold alpha
  rw [add_re, add_re, h1, h2, h3]
  have hA : 0 ≤ s.re / (2 * normSq s) := div_nonneg hre (by positivity)
  have hB : -((1 - s.re) * 4 / x ^ 2) ≤ (s.re - 1) / normSq (s - 1) := by
    rw [show (s.re - 1) / normSq (s - 1) = -((1 - s.re) / normSq (s - 1)) by ring, neg_le_neg_iff,
      div_le_div_iff₀ (by have := pow_pos hx 2; linarith) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hre1) (sub_nonneg.mpr hnsq)]
  have hC : Real.log (x / (4 * π)) ≤ Real.log (‖s‖ / (2 * π)) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.pi_pos]
  linarith

theorem sB_re_ge {t x y : ℝ} (hx : 0 < x) (ht : 0 ≤ t) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (1 + y) / 2 + t / 2 * (Real.log (x / (4 * π)) / 2 - 2 / x ^ 2) ≤ (sB t (x + y * I)).re := by
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have him : ((x : ℂ) + y * I).im = y := by simp
  have hw_re : (w (x + y * I)).re = (1 + y) / 2 := by rw [w_re, him]
  have hw_im : |(w (x + y * I)).im| = x / 2 := by
    rw [w_im, hre, abs_div, abs_neg, abs_of_pos hx]; norm_num
  have hα := re_alpha_ge hx (by rw [hw_re]; linarith) (by rw [hw_re]; linarith) hw_im
  rw [hw_re] at hα
  unfold sB
  rw [add_re, show ((t : ℂ) / 2) = ((t / 2 : ℝ) : ℂ) by push_cast; ring, re_ofReal_mul, hw_re]
  have h1 : (1 - (1 + y) / 2) * 4 / x ^ 2 ≤ 2 / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg x]
  have h2 : Real.log (x / (4 * π)) / 2 - 2 / x ^ 2 ≤ (alpha (w (x + y * I))).re := by linarith
  have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ t / 2)
  linarith

theorem sA_re_ge {t x y : ℝ} (hx : 0 < x) (ht : 0 ≤ t) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (1 - y) / 2 + t / 2 * (Real.log (x / (4 * π)) / 2 - 4 / x ^ 2) ≤ (sA t (x + y * I)).re := by
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have him : ((x : ℂ) + y * I).im = y := by simp
  have hv_re : (v (x + y * I)).re = (1 - y) / 2 := by rw [v_re, him]
  have hv_im : |(v (x + y * I)).im| = x / 2 := by
    rw [v_im, hre, abs_div, abs_of_pos hx]; norm_num
  have hα := re_alpha_ge hx (by rw [hv_re]; linarith) (by rw [hv_re]; linarith) hv_im
  rw [hv_re] at hα
  unfold sA
  rw [add_re, show ((t : ℂ) / 2) = ((t / 2 : ℝ) : ℂ) by push_cast; ring, re_ofReal_mul, hv_re]
  have h1 : (1 - (1 - y) / 2) * 4 / x ^ 2 ≤ 4 / x ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg x]
  have h2 : Real.log (x / (4 * π)) / 2 - 4 / x ^ 2 ≤ (alpha (v (x + y * I))).re := by linarith
  have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ t / 2)
  linarith

/-! ### Dirichlet polynomial bounds -/

theorem term_norm (t : ℝ) (s : ℂ) (n : ℕ) :
    ‖(bt t n : ℂ) * Complex.exp (-s * (Real.log n : ℂ))‖ =
      Real.exp (t * Real.log n ^ 2 / 4 - s.re * Real.log n) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, bt, abs_of_pos (Real.exp_pos _),
    Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  ring

theorem sum_inv_sq_le (N : ℕ) : ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
  have key : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 - 1 / N := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => rw [Finset.Icc_eq_empty (by norm_num)]; simp
    | succ N hN ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have h : (1 : ℝ) / ((N : ℝ) + 1) ^ 2 ≤ 1 / N - 1 / ((N : ℝ) + 1) := by
        rw [div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast
      linarith
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · have := key N h
    have : (0 : ℝ) ≤ 1 / N := by positivity
    linarith

theorem PN_bound {N : ℕ} {s : ℂ} {t : ℝ} (hN : 1 ≤ N)
    (hterm : ∀ n : ℕ, 2 ≤ n → n ≤ N →
      t * Real.log n ^ 2 / 4 - s.re * Real.log n ≤ -8 * Real.log n) :
    ‖PN N s t - 1‖ ≤ 1 / 64 := by
  unfold PN
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := by simp [hN]
  rw [← Finset.add_sum_erase _ _ h1]
  have hterm1 : (bt t 1 : ℂ) * Complex.exp (-s * (Real.log (1 : ℕ) : ℂ)) = 1 := by simp [bt]
  rw [hterm1, add_sub_cancel_left]
  calc ‖∑ n ∈ (Finset.Icc 1 N).erase 1, (bt t n : ℂ) * Complex.exp (-s * (Real.log n : ℂ))‖
      ≤ ∑ n ∈ (Finset.Icc 1 N).erase 1, ‖(bt t n : ℂ) * Complex.exp (-s * (Real.log n : ℂ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ (Finset.Icc 1 N).erase 1, (1 / 64) * (1 / (n : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_erase, Finset.mem_Icc] at hn
        have hn2 : 2 ≤ n := by omega
        have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        have hn0 : (0 : ℝ) < n := by linarith
        rw [term_norm]
        calc Real.exp (t * Real.log n ^ 2 / 4 - s.re * Real.log n)
            ≤ Real.exp (-8 * Real.log n) := Real.exp_le_exp.mpr (hterm n hn2 hn.2.2)
          _ = ((n : ℝ) ^ (8 : ℕ))⁻¹ := by
              rw [show (-8 : ℝ) * Real.log n = Real.log n * (-8) by ring,
                ← Real.rpow_def_of_pos hn0, Real.rpow_neg hn0.le,
                show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          _ ≤ (1 / 64) * (1 / (n : ℝ) ^ 2) := by
              rw [one_div, one_div, ← mul_inv, inv_le_inv₀ (by positivity) (by positivity)]
              have h6 : (2 : ℝ) ^ 6 ≤ (n : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) hn2' 6
              have h2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
              nlinarith
    _ = (1 / 64) * ∑ n ∈ (Finset.Icc 1 N).erase 1, (1 / (n : ℝ) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ (1 / 64) * 1 := by
        gcongr
        calc ∑ n ∈ (Finset.Icc 1 N).erase 1, (1 / (n : ℝ) ^ 2)
            ≤ ∑ n ∈ Finset.Icc 2 N, (1 / (n : ℝ) ^ 2) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro n hn
                rw [Finset.mem_erase, Finset.mem_Icc] at hn
                rw [Finset.mem_Icc]; omega
              · intros; positivity
          _ ≤ 1 := sum_inv_sq_le N
    _ = 1 / 64 := by ring

/-! ### The approximation error is at most `1/10` on the whole range -/

theorem error_le_tenth {x t y : ℝ} (hx : (Const.Xe : ℝ) ≤ x) (ht : t ∈ Icc (0 : ℝ) (1 / 5))
    (hy : y ∈ Icc (0 : ℝ) 1) : Eab x + Ec x t y ≤ 1 / 10 := by
  rw [Xe_eq] at hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hQdef : Q x = x / (4 * π) := rfl
  have hQ : (4.695e11 : ℝ) ≤ Q x := by
    rw [hQdef, le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_d6]
  have hQ0 : 0 < Q x := by linarith
  have hQ1 : 1 ≤ Q x := by linarith
  have hQx : Q x ≤ x := by
    rw [hQdef]; apply div_le_self hx0.le; linarith [Real.pi_gt_three]
  have hL0 : 0 ≤ L x := Real.log_nonneg hQ1
  have hLx : L x ≤ Real.log x := Real.log_le_log hQ0 hQx
  have hsqrt : (2.4e6 : ℝ) ≤ Real.sqrt x := by
    rw [show (2.4e6 : ℝ) = Real.sqrt ((2.4e6 : ℝ) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hlogx : Real.log x ≤ 2 * Real.sqrt x := by
    have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
    rw [Real.log_sqrt hx0.le] at h1
    linarith
  -- `E_c`
  have hEc : Ec x t y ≤ 0.0033 := by
    unfold Ec
    have hp : Q x ^ (-(1 + y) / 4) ≤ 1 / 827 := by
      calc Q x ^ (-(1 + y) / 4) ≤ Q x ^ (-(1 : ℝ) / 4) :=
            Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith [hy.1])
        _ = (Q x ^ ((1 : ℝ) / 4))⁻¹ := by rw [neg_div, Real.rpow_neg hQ0.le]
        _ ≤ (827 : ℝ)⁻¹ := by
            apply inv_anti₀ (by norm_num)
            have h4 : (((827 : ℝ) ^ (4 : ℕ)) ^ ((4 : ℕ)⁻¹ : ℝ)) = 827 :=
              Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
            have e : (((4 : ℕ) : ℝ)⁻¹) = (1 : ℝ) / 4 := by norm_num
            rw [e] at h4
            rw [← h4]
            apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
            linarith
        _ = 1 / 827 := by norm_num
    have hN : (10 : ℝ) ≤ N x t := by
      unfold N
      have h : (10 : ℕ) ≤ ⌊Real.sqrt (Q x + t / 16)⌋₊ := by
        apply Nat.le_floor
        have hq : (10 : ℝ) ^ 2 ≤ Q x + t / 16 := by nlinarith [ht.1]
        calc ((10 : ℕ) : ℝ) = Real.sqrt ((10 : ℝ) ^ 2) := by
              rw [Real.sqrt_sq (by norm_num)]; norm_num
          _ ≤ Real.sqrt (Q x + t / 16) := Real.sqrt_le_sqrt hq
      exact_mod_cast h
    have hZ : Z x ≤ L x + 2 := by
      unfold Z
      calc Real.sqrt (L x ^ 2 + π ^ 2 / 4) ≤ Real.sqrt ((L x + 2) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_d6, Real.pi_gt_d6])
        _ = L x + 2 := Real.sqrt_sq (by linarith)
    have hV : V7 x ≤ 1e-4 := by
      unfold V7
      rw [div_le_iff₀ (by linarith)]
      have h1 : 240 * Real.sqrt x ≤ 1e-4 * (Real.sqrt x * Real.sqrt x) := by nlinarith
      rw [hsq] at h1
      linarith
    have h3 := pow3_le hy
    have h3' : 0 ≤ (3 : ℝ) ^ y + (3 : ℝ) ^ (-y) := by positivity
    have hfrac : 2 * ((3 : ℝ) ^ y + (3 : ℝ) ^ (-y)) / ((N x t : ℝ) - 1) ≤ 8 / 9 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    have hL : 0 ≤ t * L x ^ 2 / 16 := by have := ht.1; positivity
    have hexp : Real.exp (-(t * L x ^ 2 / 16) +
        2 * ((3 : ℝ) ^ y + (3 : ℝ) ^ (-y)) / ((N x t : ℝ) - 1) + 1e-10 + V7 x) ≤ 2.72 := by
      calc Real.exp _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num at hfrac hV ⊢; linarith)
        _ ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
    exact (mul_le_mul hp hexp (Real.exp_pos _).le (by norm_num)).trans (by norm_num)
  -- `E_ab`
  have hEab : Eab x ≤ 5e-6 := by
    unfold Eab
    have hc : (1.001 : ℝ) ^ (0.501 : ℝ) ≤ 1.001 := by
      calc (1.001 : ℝ) ^ (0.501 : ℝ) ≤ (1.001 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 1.001 := Real.rpow_one _
    have hc0 : 0 ≤ (1.001 : ℝ) ^ (0.501 : ℝ) := Real.rpow_nonneg (by norm_num) _
    have hq : Q x ^ (0.2505 : ℝ) ≤ x ^ (0.2505 : ℝ) := Real.rpow_le_rpow hQ0.le hQx (by norm_num)
    have hq0 : 0 ≤ Q x ^ (0.2505 : ℝ) := Real.rpow_nonneg hQ0.le _
    -- `L ≤ 10 x^{0.1}`
    have hL10 : L x ≤ 10 * x ^ (0.1 : ℝ) := by
      have h1 : Real.log (x ^ (0.1 : ℝ)) ≤ x ^ (0.1 : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 _)
      rw [Real.log_rpow hx0] at h1
      linarith
    have hx01 : 1 ≤ x ^ (0.1 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    have hx02 : (x ^ (0.1 : ℝ)) ^ 2 = x ^ (0.2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    have hL2 : L x ^ 2 ≤ 100 * x ^ (0.2 : ℝ) := by
      rw [← hx02]
      have := pow_le_pow_left₀ hL0 hL10 2
      linarith
    have hx1' : 1 ≤ x ^ (0.2 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
    have hd : d x ≤ 2 * x ^ (0.2 : ℝ) / x := by
      unfold d
      rw [div_le_div_iff₀ (by linarith) hx0]
      nlinarith
    have hd0 : 0 ≤ d x := by
      unfold d
      apply div_nonneg (by positivity) (by linarith)
    have hpow : x ^ (0.2505 : ℝ) * (2 * x ^ (0.2 : ℝ) / x) ≤ 2 / Real.sqrt x := by
      rw [show x ^ (0.2505 : ℝ) * (2 * x ^ (0.2 : ℝ) / x) = 2 * (x ^ (0.2505 : ℝ) * x ^ (0.2 : ℝ)) / x by ring,
        ← Real.rpow_add hx0]
      have h1 : x ^ ((0.2505 : ℝ) + 0.2) ≤ x ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      rw [← Real.sqrt_eq_rpow] at h1
      rw [div_le_div_iff₀ hx0 (Real.sqrt_pos.mpr hx0)]
      nlinarith [Real.sqrt_nonneg x]
    have hsx : 2 / Real.sqrt x ≤ 1e-6 := by
      rw [div_le_iff₀ (Real.sqrt_pos.mpr hx0)]; linarith
    calc 2.01 * (1000 / 999) * ((1.001 : ℝ) ^ (0.501 : ℝ) / 0.501) * Q x ^ (0.2505 : ℝ) * d x
        ≤ 2.01 * (1000 / 999) * (1.001 / 0.501) * x ^ (0.2505 : ℝ) * (2 * x ^ (0.2 : ℝ) / x) := by
          gcongr
      _ = 2.01 * (1000 / 999) * (1.001 / 0.501) * (x ^ (0.2505 : ℝ) * (2 * x ^ (0.2 : ℝ) / x)) := by
          ring
      _ ≤ 2.01 * (1000 / 999) * (1.001 / 0.501) * 1e-6 :=
          mul_le_mul_of_nonneg_left (hpow.trans hsx) (by norm_num)
      _ ≤ 5e-6 := by norm_num
  linarith

end Approx

/-- Lower bound for `|P_B + γ P_A|` from the three estimates. -/
theorem fN_lower {PB PA G : ℂ} (h1 : ‖PB - 1‖ ≤ 1 / 64) (h2 : ‖PA - 1‖ ≤ 1 / 64)
    (h3 : ‖G‖ ≤ 0.008) : 9 / 10 ≤ ‖PB + G * PA‖ := by
  have hB : 1 - 1 / 64 ≤ ‖PB‖ := by
    have := norm_sub_norm_le (1 : ℂ) PB
    rw [norm_one, norm_sub_rev] at this
    linarith
  have hA : ‖PA‖ ≤ 1 + 1 / 64 := by
    have := norm_add_le (PA - 1) 1
    rw [sub_add_cancel, norm_one] at this
    linarith
  have hGA : ‖G * PA‖ ≤ 0.008 * (1 + 1 / 64) := by
    rw [norm_mul]
    exact mul_le_mul h3 hA (norm_nonneg _) (by positivity)
  have h4 : ‖PB‖ - ‖G * PA‖ ≤ ‖PB + G * PA‖ := by
    have := norm_sub_le (PB + G * PA) (G * PA)
    rw [add_sub_cancel_right] at this
    linarith
  linarith

set_option maxHeartbeats 1000000 in
/-- **P3 from Lemma A.1.** On any compact positive time interval `[t₀, T] ⊂ (0, 1/5]`,
zeros of height at least `1/40` have real part bounded by `max(X_e, 4π e^{80/t₀})`. -/
theorem confine_of_approximation (hA : EnlargedApproximation) {t0 T : ℝ}
    (ht0 : 0 < t0) (hT : T ≤ 1 / 5) :
    ∃ R : ℝ, ∀ t ∈ Icc t0 T, ∀ z : ℂ, H t z = 0 → 1 / 40 ≤ |z.im| → |z.re| ≤ R := by
  refine ⟨max (Const.Xe : ℝ) (4 * π * Real.exp (80 / t0)), ?_⟩
  intro t ht z hz hy
  by_contra hR
  push_neg at hR
  have ht0' : 0 ≤ t := by linarith [ht.1]
  have hstrip := strip_all t ht0' z hz
  -- the main case: `x` large, `1/40 ≤ y ≤ 1`
  have key : ∀ x y : ℝ, max (Const.Xe : ℝ) (4 * π * Real.exp (80 / t0)) < x → 1 / 40 ≤ y →
      y ≤ 1 → H t (x + y * I) ≠ 0 := by
    intro x y hx hy1 hy2 h0
    have hXe : (Const.Xe : ℝ) ≤ x := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx)
    have hxpos : 0 < x := by
      have : (0 : ℝ) < Const.Xe := by norm_num [Const.Xe]
      linarith
    have hexp : 4 * π * Real.exp (80 / t0) < x := lt_of_le_of_lt (le_max_right _ _) hx
    have htT : t ∈ Icc (0 : ℝ) (1 / 5) := ⟨ht0', ht.2.trans hT⟩
    have hyI : y ∈ Icc (0 : ℝ) 1 := ⟨by linarith, hy2⟩
    obtain ⟨_, hE⟩ := hA x hXe t htT y ⟨hyI.1, hy2.trans (by norm_num)⟩
    have hγ := Approx.gamma_crude hXe htT hyI
    have herr := Approx.error_le_tenth hXe htT hyI
    rw [h0, zero_div, zero_sub, norm_neg] at hE
    -- the logarithm `L`
    set L := Real.log (x / (4 * π)) with hLdef
    have hL1 : 80 / t0 < L := by
      rw [hLdef, Real.lt_log_iff_exp_lt (by positivity), lt_div_iff₀ (by positivity)]
      linarith
    have hL2 : 80 / t ≤ 80 / t0 := div_le_div_of_nonneg_left (by norm_num) ht0 ht.1
    have htL : 80 ≤ t * L := by
      have h : 80 / t < L := lt_of_le_of_lt hL2 hL1
      rw [div_lt_iff₀ (by linarith [ht.1])] at h
      linarith
    have hLpos : 0 < L := lt_trans (by positivity) hL1
    have hL400 : 400 ≤ L := by
      have := mul_le_mul_of_nonneg_right (ht.2.trans hT) hLpos.le
      linarith
    have hL0 : 0 ≤ L := hLpos.le
    have hQdef : Approx.Q x = x / (4 * π) := rfl
    have hQpos : 0 < Approx.Q x := by rw [hQdef]; positivity
    have hlogQ : Real.log (Approx.Q x) = L := by rw [hLdef, hQdef]
    have hQ1 : 1 ≤ Approx.Q x := by
      have := Real.exp_log hQpos
      rw [hlogQ] at this
      rw [← this]
      exact Real.one_le_exp (by linarith)
    -- cutoff
    have hN1 : 1 ≤ Approx.N x t := by
      unfold Approx.N
      apply Nat.le_floor
      calc ((1 : ℕ) : ℝ) = Real.sqrt 1 := by simp
        _ ≤ Real.sqrt (Approx.Q x + t / 16) := Real.sqrt_le_sqrt (by linarith)
    have hNle : ∀ n : ℕ, 2 ≤ n → n ≤ Approx.N x t → Real.log n ≤ (L + 0.7) / 2 := by
      intro n hn2 hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have h1 : (n : ℝ) ≤ Real.sqrt (2 * Approx.Q x) := by
        calc (n : ℝ) ≤ (Approx.N x t : ℝ) := by exact_mod_cast hn
          _ ≤ Real.sqrt (Approx.Q x + t / 16) := Nat.floor_le (Real.sqrt_nonneg _)
          _ ≤ Real.sqrt (2 * Approx.Q x) := Real.sqrt_le_sqrt (by linarith [ht.2])
      calc Real.log n ≤ Real.log (Real.sqrt (2 * Approx.Q x)) := Real.log_le_log hn0 h1
        _ = Real.log (2 * Approx.Q x) / 2 := Real.log_sqrt (by positivity)
        _ = (Real.log 2 + L) / 2 := by rw [Real.log_mul (by norm_num) hQpos.ne', hlogQ]
        _ ≤ (L + 0.7) / 2 := by linarith [Real.log_two_lt_d9]
    -- real parts of the two Dirichlet arguments
    have hsB := Approx.sB_re_ge hxpos ht0' hyI.1 hy2
    have hsA := Approx.sA_re_ge hxpos ht0' hyI.1 hy2
    rw [← hLdef] at hsB hsA
    have hx2 : 4 / x ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (5900000000000 : ℝ) ≤ x := by rw [Approx.Xe_eq] at hXe; exact hXe
      nlinarith
    have hx2' : 2 / x ^ 2 ≤ 1 := by
      have : 2 / x ^ 2 ≤ 4 / x ^ 2 := by gcongr; norm_num
      linarith
    have hexpB : ∀ n : ℕ, 2 ≤ n → n ≤ Approx.N x t →
        t * Real.log n ^ 2 / 4 - (Approx.sB t (x + y * I)).re * Real.log n ≤ -8 * Real.log n := by
      intro n hn2 hnN
      have hl := hNle n hn2 hnN
      have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      have h1 : t * Real.log n ^ 2 / 4 ≤ t * Real.log n * (L + 0.7) / 8 := by
        have := mul_le_mul_of_nonneg_left hl (mul_nonneg ht0' hl0)
        linarith
      have h2 : 1 / 2 + t * L / 4 - t / 2 ≤ (Approx.sB t (x + y * I)).re := by
        have : t / 2 * (L / 2 - 2 / x ^ 2) ≥ t * L / 4 - t / 2 := by
          have := mul_le_mul_of_nonneg_left hx2' (by linarith : (0 : ℝ) ≤ t / 2)
          linarith
        linarith [hyI.1]
      have h3 := mul_le_mul_of_nonneg_right h2 hl0
      have h4 := mul_le_mul_of_nonneg_right htL hl0
      have h5 := mul_le_mul_of_nonneg_right (ht.2.trans hT) hl0
      linarith
    have hexpA : ∀ n : ℕ, 2 ≤ n → n ≤ Approx.N x t →
        t * Real.log n ^ 2 / 4 - (Approx.sA t (x + y * I)).re * Real.log n ≤ -8 * Real.log n := by
      intro n hn2 hnN
      have hl := hNle n hn2 hnN
      have hl0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      have h1 : t * Real.log n ^ 2 / 4 ≤ t * Real.log n * (L + 0.7) / 8 := by
        have := mul_le_mul_of_nonneg_left hl (mul_nonneg ht0' hl0)
        linarith
      have h2 : t * L / 4 - t ≤ (Approx.sA t (x + y * I)).re := by
        have : t / 2 * (L / 2 - 4 / x ^ 2) ≥ t * L / 4 - t := by
          have := mul_le_mul_of_nonneg_left hx2 (by linarith : (0 : ℝ) ≤ t / 2)
          linarith
        linarith [hy2]
      have h3 := mul_le_mul_of_nonneg_right h2 hl0
      have h4 := mul_le_mul_of_nonneg_right htL hl0
      have h5 := mul_le_mul_of_nonneg_right (ht.2.trans hT) hl0
      linarith
    have hPB := Approx.PN_bound hN1 hexpB
    have hPA := Approx.PN_bound hN1 hexpA
    -- the reflected coefficient
    have hexp5 : Real.exp (-5) ≤ 0.007 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have h5 : Real.exp (5 : ℝ) = Real.exp 1 ^ 5 := by rw [Real.exp_one_pow]; norm_num
      rw [h5]
      have : (2.7182818283 : ℝ) ^ 5 < Real.exp 1 ^ 5 :=
        pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
      have : (1 / 0.007 : ℝ) ≤ 2.7182818283 ^ 5 := by norm_num
      linarith
    have hγ' : ‖Approx.gamma t (x + y * I)‖ ≤ 0.008 := by
      calc ‖Approx.gamma t (x + y * I)‖ ≤ Real.exp (1 / 10) * Approx.Q x ^ (-y / 2) := hγ
        _ ≤ 1.11 * 0.007 := by
            apply mul_le_mul _ _ (by positivity) (by norm_num)
            · have h2 := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 1 / 10) (by norm_num) (n := 2)
                (by norm_num)
              simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
              norm_num at h2 ⊢
              linarith
            · rw [Real.rpow_def_of_pos hQpos, hlogQ]
              calc Real.exp (L * (-y / 2)) ≤ Real.exp (-5) :=
                    Real.exp_le_exp.mpr (by nlinarith)
                _ ≤ 0.007 := hexp5
        _ ≤ 0.008 := by norm_num
    -- assemble the lower bound on `|f^{[N]}|`
    have hre : ((x : ℂ) + y * I).re = x := by simp
    have hf : 9 / 10 ≤ ‖Approx.fN t (x + y * I)‖ := by
      unfold Approx.fN
      rw [hre]
      exact fN_lower hPB hPA hγ'
    linarith
  -- reduce to the main case by the symmetries `z ↦ −z`, `z ↦ z̄`
  obtain ⟨hz2, hz3⟩ := symm_all t z hz
  have hs1 := (abs_le.mp hstrip).1
  have hs2 := (abs_le.mp hstrip).2
  rcases le_or_gt 0 z.re with hre | hre
  · have hxr : max (Const.Xe : ℝ) (4 * π * Real.exp (80 / t0)) < z.re := by
      rwa [abs_of_nonneg hre] at hR
    rcases le_or_gt 0 z.im with him | him
    · exact key z.re z.im hxr (by rwa [abs_of_nonneg him] at hy) hs2 (by rw [re_add_im]; exact hz)
    · refine key z.re (-z.im) hxr (by rwa [abs_of_neg him] at hy) (by linarith) ?_
      have e : (z.re : ℂ) + ((-z.im : ℝ) : ℂ) * I = starRingEnd ℂ z := by
        apply Complex.ext <;> simp
      rw [e]; exact hz3
  · have hxr : max (Const.Xe : ℝ) (4 * π * Real.exp (80 / t0)) < -z.re := by
      rwa [abs_of_neg hre] at hR
    rcases le_or_gt 0 z.im with him | him
    · refine key (-z.re) z.im hxr (by rwa [abs_of_nonneg him] at hy) hs2 ?_
      have e : ((-z.re : ℝ) : ℂ) + (z.im : ℂ) * I = -(starRingEnd ℂ z) := by
        apply Complex.ext <;> simp
      rw [e]; exact (symm_all t _ hz3).1
    · refine key (-z.re) (-z.im) hxr (by rwa [abs_of_neg him] at hy) (by linarith) ?_
      have e : ((-z.re : ℝ) : ℂ) + ((-z.im : ℝ) : ℂ) * I = -z := by
        apply Complex.ext <;> simp
      rw [e]; exact hz2

end DBN
