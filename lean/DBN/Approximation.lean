import Mathlib
import DBN.Premises
import DBN.External
import DBN.Head

/-!
# The enlarged approximation (manuscript Lemma A.1) and the boundary certificate

Several remaining analytic estimates use an effective approximation of
`H_t(x + iy)` for `x ≥ X_e = 5.9·10¹²`: manuscript Lemma A.1 (Appendix A.1), whose proof cites the
generic-real-part Riemann–Siegel expansion of Arias de Reyna in the explicit form of
[Po19, Proposition 6.2, (58)] and adds new error estimates. This file collects its residual bound
and the nonzero normalizer as the unproved proposition `EnlargedApproximation`, with the constants and functions
exactly (`Approx.*`; principal logarithms are Mathlib's `Complex.log`).

It then proves the reduction of the finite-head boundary certificate (Appendix C.2, Proposition C.1):
`BoundaryNonvanishing` follows from `EnlargedApproximation` and `BoundaryMainTermBound`,
which assumes that the actual-cutoff finite-sum approximation `f^{[N]}` has modulus above
`1/500` at every point of `X + i[0,1]` for `t ∈ [0, 1/5]`. This is a continuous lower-bound
assumption, not a formalized finite grid. The conventional argument derives it from the
800,000-cell polynomial certificate (C8) together with the evaluation error (C7).
Neither that polynomial evaluation nor the error bridge is proved here.
The scalar error bound (C4) at `x = X`, `E_ab(X) + E_c(X,t,y) < 1/500`, is proved
here from Mathlib's bounds on `π` and `e`.
-/

noncomputable section

namespace DBN

open Real Set Complex

namespace Approx

/-- `M_0(s) = s(s−1)/16 · π^{−s/2} · √(2π) · exp[(s/2 − 1/2) Log(s/2) − s/2]`. -/
def M0 (s : ℂ) : ℂ :=
  s * (s - 1) / 16 * Complex.exp (-(s / 2) * (Real.log π : ℂ)) * (Real.sqrt (2 * π) : ℂ) *
    Complex.exp ((s / 2 - 1 / 2) * Complex.log (s / 2) - s / 2)

/-- `α(s) = 1/(2s) + 1/(s−1) + (1/2) Log(s/(2π))`. -/
def alpha (s : ℂ) : ℂ := 1 / (2 * s) + 1 / (s - 1) + (1 / 2) * Complex.log (s / (2 * (π : ℂ)))

/-- `M_t(s) = M_0(s) e^{t α(s)²/4}`. -/
def Mt (t : ℝ) (s : ℂ) : ℂ := M0 s * Complex.exp ((t : ℂ) * alpha s ^ 2 / 4)

/-- `w = (1 − iz)/2`. -/
def w (z : ℂ) : ℂ := (1 - I * z) / 2
/-- `v = 1 − w`. -/
def v (z : ℂ) : ℂ := 1 - w z
/-- `B_t(z) = M_t(w)`. -/
def Bt (t : ℝ) (z : ℂ) : ℂ := Mt t (w z)
/-- `s_B = w + (t/2) α(w)`. -/
def sB (t : ℝ) (z : ℂ) : ℂ := w z + ((t : ℂ) / 2) * alpha (w z)
/-- `s_A = v + (t/2) α(v)`. -/
def sA (t : ℝ) (z : ℂ) : ℂ := v z + ((t : ℂ) / 2) * alpha (v z)
/-- `γ = M_t(v)/M_t(w)`. -/
def gamma (t : ℝ) (z : ℂ) : ℂ := Mt t (v z) / Mt t (w z)
/-- `b_t(n) = e^{t log²n/4}`. -/
def bt (t : ℝ) (n : ℕ) : ℝ := Real.exp (t * Real.log n ^ 2 / 4)
/-- `P_N(s,t) = Σ_{n=1}^N b_t(n) n^{−s}`. -/
def PN (N : ℕ) (s : ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (bt t n : ℂ) * Complex.exp (-s * (Real.log n : ℂ))
/-- `𝒬 = x/(4π)`. -/
def Q (x : ℝ) : ℝ := x / (4 * π)
/-- `L = log 𝒬`. -/
def L (x : ℝ) : ℝ := Real.log (Q x)
/-- `Z = (L² + π²/4)^{1/2}`. -/
def Z (x : ℝ) : ℝ := Real.sqrt (L x ^ 2 + π ^ 2 / 4)
/-- `N = ⌊√(𝒬 + t/16)⌋`. -/
def N (x t : ℝ) : ℕ := ⌊Real.sqrt (Q x + t / 16)⌋₊
/-- `d(x) = (t_m² L²/16 + 0.626)/(x − 6.66)` with `t_m = 1/5`. -/
def d (x : ℝ) : ℝ := ((1 / 5 : ℝ) ^ 2 * L x ^ 2 / 16 + 0.626) / (x - 6.66)
/-- `E_ab(x) = 2.01 · (1000/999) · (1.001^{0.501}/0.501) · 𝒬^{0.2505} · d(x)`. -/
def Eab (x : ℝ) : ℝ :=
  2.01 * (1000 / 999) * ((1.001 : ℝ) ^ (0.501 : ℝ) / 0.501) * Q x ^ (0.2505 : ℝ) * d x
/-- `V_7(x) = (20 Z + 200)/(x − 40)`. -/
def V7 (x : ℝ) : ℝ := (20 * Z x + 200) / (x - 40)
/-- `E_c(x,t,y) = 𝒬^{−(1+y)/4} exp[−tL²/16 + 2(3^y + 3^{−y})/(N − 1) + 10⁻¹⁰ + V_7(x)]`. -/
def Ec (x t y : ℝ) : ℝ :=
  Q x ^ (-(1 + y) / 4) * Real.exp (-(t * L x ^ 2 / 16) +
    2 * ((3 : ℝ) ^ y + (3 : ℝ) ^ (-y)) / ((N x t : ℝ) - 1) + 1e-10 + V7 x)
/-- The finite-sum approximation with the actual cutoff `N = N(Re z, t)`.
Its global definition is not a holomorphic fixed-cutoff function. -/
def fN (t : ℝ) (z : ℂ) : ℂ :=
  PN (N z.re t) (sB t z) t + gamma t z * PN (N z.re t) (sA t z) t

end Approx

/-- **Manuscript Lemma A.1 (enlarged approximation).** For `x ≥ X_e`, `0 ≤ t ≤ 1/5` and
`0 ≤ y ≤ 7`, `B_t(x+iy) ≠ 0` and `|H_t(z)/B_t(z) − f^{[N]}(z)| ≤ E_ab(x) + E_c(x,t,y)`. -/
def EnlargedApproximation : Prop :=
  ∀ x : ℝ, (Const.Xe : ℝ) ≤ x → ∀ t ∈ Icc (0 : ℝ) (1 / 5), ∀ y ∈ Icc (0 : ℝ) 7,
    Approx.Bt t (x + y * I) ≠ 0 ∧
      ‖H t (x + y * I) / Approx.Bt t (x + y * I) - Approx.fN t (x + y * I)‖ ≤
        Approx.Eab x + Approx.Ec x t y

/-- Continuous boundary lower bound for the finite-sum approximation.
The conventional proof uses both the polynomial grid (C8) and the error bound (C7);
their formal certification remains open. -/
def BoundaryMainTermBound : Prop :=
  ∀ t ∈ Icc (0 : ℝ) (1 / 5), ∀ y ∈ Icc (0 : ℝ) 1, 1 / 500 < ‖Approx.fN t ((Const.X : ℝ) + y * I)‖

namespace Approx

/-! ### The scalar error bound (C4) at `x = X` -/

theorem X_eq : (Const.X : ℝ) = 5999347341500 := by norm_num [Const.X]

theorem Q_X_bounds : (4.774e11 : ℝ) < Q Const.X ∧ Q Const.X < 4.7742e11 := by
  unfold Q
  rw [X_eq]
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    linarith [Real.pi_lt_d6]
  · rw [div_lt_iff₀ (by positivity)]
    linarith [Real.pi_gt_d6]

theorem Q_X_pos : 0 < Q Const.X := by linarith [Q_X_bounds.1]

theorem L_X_le : L Const.X ≤ 27 := by
  unfold L
  rw [Real.log_le_iff_le_exp Q_X_pos]
  have h1 : Real.exp (27 : ℝ) = Real.exp 1 ^ 27 := by rw [Real.exp_one_pow]; norm_num
  rw [h1]
  have h2 : (2.7182818283 : ℝ) ^ 27 < Real.exp 1 ^ 27 :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have h3 : (4.7742e11 : ℝ) < 2.7182818283 ^ 27 := by norm_num
  linarith [Q_X_bounds.2]

theorem L_X_nonneg : 0 ≤ L Const.X := Real.log_nonneg (by linarith [Q_X_bounds.1])

theorem Z_X_le : Z Const.X ≤ 29 := by
  unfold Z
  have h := L_X_le
  have h0 := L_X_nonneg
  calc Real.sqrt (L Const.X ^ 2 + π ^ 2 / 4) ≤ Real.sqrt (29 ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_d6, Real.pi_gt_d6])
    _ = 29 := Real.sqrt_sq (by norm_num)

theorem N_X_ge {t : ℝ} (ht : 0 ≤ t) : (690001 : ℝ) ≤ N Const.X t := by
  unfold N
  have h : (690001 : ℕ) ≤ ⌊Real.sqrt (Q Const.X + t / 16)⌋₊ := by
    apply Nat.le_floor
    have hq : (690001 : ℝ) ^ 2 ≤ Q Const.X + t / 16 := by nlinarith [Q_X_bounds.1]
    calc ((690001 : ℕ) : ℝ) = Real.sqrt ((690001 : ℝ) ^ 2) := by
          rw [Real.sqrt_sq (by norm_num)]; norm_num
      _ ≤ Real.sqrt (Q Const.X + t / 16) := Real.sqrt_le_sqrt hq
  exact_mod_cast h

theorem V7_X_le : V7 Const.X ≤ 1.4e-10 := by
  unfold V7
  have hden : (Const.X : ℝ) - 40 = 5999347341500 - 40 := by rw [X_eq]
  rw [hden, div_le_iff₀ (by norm_num)]
  have := Z_X_le
  have hZ0 : 0 ≤ Z Const.X := Real.sqrt_nonneg _
  nlinarith

theorem V7_X_nonneg : 0 ≤ V7 Const.X := by
  unfold V7
  have hden : (Const.X : ℝ) - 40 = 5999347341500 - 40 := by rw [X_eq]
  rw [hden]
  have hZ0 : 0 ≤ Z Const.X := Real.sqrt_nonneg _
  positivity

theorem pow3_le {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : (3 : ℝ) ^ y + (3 : ℝ) ^ (-y) ≤ 4 := by
  have h1 : (3 : ℝ) ^ y ≤ 3 := by
    calc (3 : ℝ) ^ y ≤ (3 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hy.2
      _ = 3 := Real.rpow_one 3
  have h2 : (3 : ℝ) ^ (-y) ≤ 1 := by
    calc (3 : ℝ) ^ (-y) ≤ (3 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hy.1])
      _ = 1 := Real.rpow_zero 3
  linarith

theorem Ec_X_le {t y : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 5)) (hy : y ∈ Icc (0 : ℝ) 1) :
    Ec Const.X t y ≤ 0.00121 := by
  unfold Ec
  have hQ1 : (1 : ℝ) ≤ Q Const.X := by linarith [Q_X_bounds.1]
  have hQ0 := Q_X_pos
  -- the power factor
  have hp : Q Const.X ^ (-(1 + y) / 4) ≤ 1 / 827 := by
    calc Q Const.X ^ (-(1 + y) / 4) ≤ Q Const.X ^ (-(1 : ℝ) / 4) :=
          Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith [hy.1])
      _ = (Q Const.X ^ ((1 : ℝ) / 4))⁻¹ := by rw [neg_div, Real.rpow_neg hQ0.le]
      _ ≤ (827 : ℝ)⁻¹ := by
          apply inv_anti₀ (by norm_num)
          have h4 : (((827 : ℝ) ^ (4 : ℕ)) ^ ((4 : ℕ)⁻¹ : ℝ)) = 827 :=
            Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
          have e : (((4 : ℕ) : ℝ)⁻¹) = (1 : ℝ) / 4 := by norm_num
          rw [e] at h4
          rw [← h4]
          apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
          linarith [Q_X_bounds.1]
      _ = 1 / 827 := by norm_num
  -- the exponential factor
  have hexp : Real.exp (-(t * L Const.X ^ 2 / 16) +
      2 * ((3 : ℝ) ^ y + (3 : ℝ) ^ (-y)) / ((N Const.X t : ℝ) - 1) + 1e-10 + V7 Const.X) ≤
      1.00003 := by
    have hN := N_X_ge ht.1
    have h3 := pow3_le hy
    have h3' : 0 ≤ (3 : ℝ) ^ y + (3 : ℝ) ^ (-y) := by positivity
    have hV := V7_X_le
    have hL : 0 ≤ t * L Const.X ^ 2 / 16 := by have := ht.1; positivity
    have hfrac : 2 * ((3 : ℝ) ^ y + (3 : ℝ) ^ (-y)) / ((N Const.X t : ℝ) - 1) ≤ 8 / 690000 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    set e := -(t * L Const.X ^ 2 / 16) +
      2 * ((3 : ℝ) ^ y + (3 : ℝ) ^ (-y)) / ((N Const.X t : ℝ) - 1) + 1e-10 + V7 Const.X with he
    have he1 : e ≤ 1.2e-5 := by rw [he]; norm_num at hfrac hV ⊢; linarith
    rcases le_or_gt 0 e with h0 | h0
    · have := Real.exp_bound' h0 (by linarith) (n := 1) (by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
      norm_num at this ⊢
      linarith
    · have := Real.exp_le_one_iff.mpr h0.le
      linarith
  exact (mul_le_mul hp hexp (Real.exp_pos _).le (by norm_num)).trans (by norm_num)

theorem Q_rpow_le : Q Const.X ^ (0.2505 : ℝ) ≤ 870 := by
  rw [Real.rpow_def_of_pos Q_X_pos]
  have hL := L_X_le
  have h1 : Real.log (Q Const.X) * 0.2505 ≤ 6.7635 := by unfold L at hL; nlinarith
  calc Real.exp (Real.log (Q Const.X) * 0.2505) ≤ Real.exp 6.7635 := Real.exp_le_exp.mpr h1
    _ = Real.exp 6 * Real.exp 0.7635 := by rw [← Real.exp_add]; norm_num
    _ ≤ 2.7182818286 ^ 6 * 2.1458 := by
        apply mul_le_mul _ _ (Real.exp_pos _).le (by norm_num)
        · have h6 : Real.exp (6 : ℝ) = Real.exp 1 ^ 6 := by rw [Real.exp_one_pow]; norm_num
          rw [h6]
          exact (pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)).le
        · have hT := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.7635) (by norm_num) (n := 10)
            (by norm_num)
          have hS : (∑ m ∈ Finset.range 10, (0.7635 : ℝ) ^ m / m.factorial) +
              (0.7635 : ℝ) ^ 10 * (10 + 1) / ((10 : ℕ).factorial * 10) ≤ 2.1458 := by
            simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
            norm_num
          linarith
    _ ≤ 870 := by norm_num

theorem d_X_le : d Const.X ≤ 4.1e-13 := by
  unfold d
  have hden : (Const.X : ℝ) - 6.66 = 5999347341500 - 6.66 := by rw [X_eq]
  rw [hden, div_le_iff₀ (by norm_num)]
  have := L_X_le
  have h0 := L_X_nonneg
  nlinarith

theorem d_X_nonneg : 0 ≤ d Const.X := by
  unfold d
  have hden : (Const.X : ℝ) - 6.66 = 5999347341500 - 6.66 := by rw [X_eq]
  rw [hden]
  positivity

theorem Eab_X_le : Eab Const.X ≤ 3e-9 := by
  unfold Eab
  have h1 : (1.001 : ℝ) ^ (0.501 : ℝ) ≤ 1.001 := by
    calc (1.001 : ℝ) ^ (0.501 : ℝ) ≤ (1.001 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 1.001 := Real.rpow_one _
  have h2 := Q_rpow_le
  have h3 := d_X_le
  have hd0 := d_X_nonneg
  have hq0 : 0 ≤ Q Const.X ^ (0.2505 : ℝ) := Real.rpow_nonneg Q_X_pos.le _
  have hp0 : 0 ≤ (1.001 : ℝ) ^ (0.501 : ℝ) := Real.rpow_nonneg (by norm_num) _
  calc 2.01 * (1000 / 999) * ((1.001 : ℝ) ^ (0.501 : ℝ) / 0.501) * Q Const.X ^ (0.2505 : ℝ) *
        d Const.X
      ≤ 2.01 * (1000 / 999) * (1.001 / 0.501) * 870 * 4.1e-13 := by gcongr
    _ ≤ 3e-9 := by norm_num

/-! ### Real and imaginary parts of `w` and `v` -/

theorem w_re (z : ℂ) : (w z).re = (1 + z.im) / 2 := by
  rw [w, Complex.div_re]; simp [Complex.normSq_apply]; ring

theorem w_im (z : ℂ) : (w z).im = -z.re / 2 := by
  rw [w, Complex.div_im]; simp [Complex.normSq_apply]; ring

theorem v_re (z : ℂ) : (v z).re = (1 - z.im) / 2 := by
  rw [v, Complex.sub_re, w_re]; simp; ring

theorem v_im (z : ℂ) : (v z).im = z.re / 2 := by
  rw [v, Complex.sub_im, w_im]; simp; ring

theorem Xe_eq : (Const.Xe : ℝ) = 5900000000000 := by norm_num [Const.Xe]

/-- **(C4) at `x = X`.** -/
theorem error_X_lt {t y : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 5)) (hy : y ∈ Icc (0 : ℝ) 1) :
    Eab Const.X + Ec Const.X t y < 1 / 500 := by
  have h1 := Eab_X_le
  have h2 := Ec_X_le ht hy
  norm_num at h1 h2 ⊢
  linarith

end Approx

/-- Proposition C.1 from the approximation and a continuous main-term lower bound. -/
theorem boundaryNonvanishing_of_approximation (hA : EnlargedApproximation) (hG : BoundaryMainTermBound) :
    BoundaryNonvanishing := by
  intro t ht y hy h0
  have hX : (Const.Xe : ℝ) ≤ Const.X := by norm_num [Const.X, Const.Xe]
  obtain ⟨_, hE⟩ := hA (Const.X : ℝ) hX t ht y ⟨hy.1, hy.2.trans (by norm_num)⟩
  have hf := hG t ht y hy
  have herr := Approx.error_X_lt ht hy
  rw [h0, zero_div, zero_sub, norm_neg] at hE
  linarith

end DBN
