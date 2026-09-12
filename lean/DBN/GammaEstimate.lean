import Mathlib
import DBN.Approximation

/-!
# A crude bound for the reflected coefficient `γ`

Manuscript (A.3) gives `|γ_t(x+iy)| ≤ e^{10⁻¹¹ y} 𝒬^{−y/2}`. This file proves the cruder
`|γ_t(x+iy)| ≤ e^{1/10} 𝒬^{−y/2}` for `x ≥ X_e`, `t ∈ [0, 1/5]`, `y ∈ [0, 1]` directly from the
definitions, which is all that positive-time confinement needs (`DBN.ConfineApprox`).

With `w = (1+y)/2 − ix/2` and `v = 1 − w = (1−y)/2 + ix/2` one has `v(v−1) = w(w−1)`, so
`|γ| = exp(E(v) − E(w))` with
`E(s) = −(Re s/2) log π + Re[(s/2 − 1/2) Log(s/2)] − Re s/2 + t Re(α(s)²)/4`.
The difference is `(y/2) log(2π) − ((1+y)/4) log|v| + ((1−y)/4) log|w| − (x/4)(arg v + arg w) + y/2`
plus the heat term. Elementary estimates give `log|v|, log|w| ∈ [log(x/2), log(x/2) + 2/x²]`,
`arg v + arg w = arctan((1+y)/x) − arctan((1−y)/x) ∈ [2y/x − 8/x³, 2/x]`, and
`|Re(α(v)² − α(w)²)| ≤ 1`, whence `E(v) − E(w) ≤ −(y/2) log(x/(4π)) + 1/10`.
-/

noncomputable section

namespace DBN

open Real Set Complex

namespace Approx

/-! ### Two arctangent bounds -/

theorem arctan_le_self {u : ℝ} (hu : 0 ≤ u) : Real.arctan u ≤ u := by
  have h1 : 0 ≤ Real.arctan u := Real.arctan_nonneg.mpr hu
  have h2 := Real.arctan_lt_pi_div_two u
  have := Real.le_tan h1 h2
  rwa [Real.tan_arctan] at this

theorem sub_cube_le_arctan {u : ℝ} (hu : 0 ≤ u) : u - u ^ 3 ≤ Real.arctan u := by
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Real.arctan s - s + s ^ 3)
      (1 / (1 + s ^ 2) - 1 + 3 * s ^ 2) s := by
    intro s
    have h := ((Real.hasDerivAt_arctan s).sub (hasDerivAt_id' s)).add (hasDerivAt_pow 3 s)
    have e : ((Real.arctan - fun x : ℝ => x) + fun x : ℝ => x ^ 3) =
        fun s : ℝ => Real.arctan s - s + s ^ 3 := by
      funext s; simp
    rw [e] at h
    exact h.congr_deriv (by norm_num)
  have hmono : MonotoneOn (fun s : ℝ => Real.arctan s - s + s ^ 3) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (continuous_iff_continuousAt.mpr fun s => (hderiv s).continuousAt).continuousOn
    · intro s _; exact (hderiv s).differentiableAt.differentiableWithinAt
    · intro s _
      rw [(hderiv s).deriv]
      have : 1 - s ^ 2 ≤ 1 / (1 + s ^ 2) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg s, sq_nonneg (s ^ 2)]
      nlinarith [sq_nonneg s]
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hu) hu
  simp only [Real.arctan_zero] at this
  linarith

/-! ### Arguments of `w` and `v` -/

theorem arg_eq_arctan {z : ℂ} (hz : 0 < z.re) : arg z = Real.arctan (z.im / z.re) := by
  have h := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [← Complex.tan_arg z, Real.arctan_tan (by linarith [(abs_lt.mp h).1]) (abs_lt.mp h).2]

theorem arg_w {x y : ℝ} (hx : 0 < x) (hy0 : 0 ≤ y) :
    arg (w (x + y * I)) = -Real.arctan (x / (1 + y)) := by
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have him : ((x : ℂ) + y * I).im = y := by simp
  have h1y : (1 : ℝ) + y ≠ 0 := by linarith
  rw [arg_eq_arctan (by rw [w_re, him]; linarith), w_re, w_im, hre, him,
    show -x / 2 / ((1 + y) / 2) = -(x / (1 + y)) by field_simp, Real.arctan_neg]

theorem arg_v {x y : ℝ} (hx : 0 < x) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    arg (v (x + y * I)) = π / 2 - Real.arctan ((1 - y) / x) := by
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have him : ((x : ℂ) + y * I).im = y := by simp
  rcases lt_or_eq_of_le hy1 with hlt | heq
  · have hpos : 0 < (1 - y) / x := by apply div_pos (by linarith) hx
    rw [arg_eq_arctan (by rw [v_re, him]; linarith), v_re, v_im, hre, him,
      show x / 2 / ((1 - y) / 2) = ((1 - y) / x)⁻¹ by
        field_simp,
      Real.arctan_inv_of_pos hpos]
  · subst heq
    have hv : v (x + (1 : ℝ) * I) = ((x / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext
      · rw [v_re]; simp
      · rw [v_im]; simp
    rw [hv, Complex.arg_real_mul I (by linarith), Complex.arg_I]
    simp

theorem arg_sum {x y : ℝ} (hx : 0 < x) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    arg (v (x + y * I)) + arg (w (x + y * I)) =
      Real.arctan ((1 + y) / x) - Real.arctan ((1 - y) / x) := by
  rw [arg_v hx hy0 hy1, arg_w hx hy0]
  have hpos : 0 < (1 + y) / x := by apply div_pos (by linarith) hx
  have h := Real.arctan_inv_of_pos hpos
  rw [show ((1 + y) / x)⁻¹ = x / (1 + y) by rw [inv_div]] at h
  rw [h]; ring

theorem arg_sum_bounds {x y : ℝ} (hx : 1 ≤ x) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    2 * y / x - 8 / x ^ 3 ≤ arg (v (x + y * I)) + arg (w (x + y * I)) ∧
      0 ≤ arg (v (x + y * I)) + arg (w (x + y * I)) ∧
      arg (v (x + y * I)) + arg (w (x + y * I)) ≤ 2 / x := by
  have hx0 : 0 < x := by linarith
  rw [arg_sum hx0 hy0 hy1]
  set a := (1 + y) / x with ha
  set b := (1 - y) / x with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by rw [hb]; apply div_nonneg (by linarith) hx0.le
  have hab : b ≤ a := by rw [ha, hb]; apply div_le_div_of_nonneg_right (by linarith) hx0.le
  have ha2 : a ≤ 2 / x := by rw [ha]; apply div_le_div_of_nonneg_right (by linarith) hx0.le
  have h1 := sub_cube_le_arctan ha0
  have h2 := arctan_le_self hb0
  have h3 := arctan_le_self ha0
  have h4 := Real.arctan_nonneg.mpr hb0
  have h5 : Real.arctan b ≤ Real.arctan a := Real.arctan_mono hab
  have hcube : a ^ 3 ≤ 8 / x ^ 3 := by
    calc a ^ 3 ≤ (2 / x) ^ 3 := pow_le_pow_left₀ ha0 ha2 3
      _ = 8 / x ^ 3 := by rw [div_pow]; norm_num
  have hab' : a - b = 2 * y / x := by rw [ha, hb]; field_simp; ring
  refine ⟨?_, by linarith, by linarith⟩
  linarith

/-! ### Norms of `w` and `v` -/

theorem normSq_w {x y : ℝ} : normSq (w (x + y * I)) = ((1 + y) / 2) ^ 2 + (x / 2) ^ 2 := by
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have him : ((x : ℂ) + y * I).im = y := by simp
  rw [normSq_apply, w_re, w_im, hre, him]; ring

theorem normSq_v {x y : ℝ} : normSq (v (x + y * I)) = ((1 - y) / 2) ^ 2 + (x / 2) ^ 2 := by
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have him : ((x : ℂ) + y * I).im = y := by simp
  rw [normSq_apply, v_re, v_im, hre, him]; ring

/-- `log ‖s‖ ∈ [log(x/2), log(x/2) + 2/x²]` when `normSq s = σ² + (x/2)²` with `σ² ≤ 1`. -/
theorem log_norm_bounds {s : ℂ} {x σ : ℝ} (hx : 0 < x) (hσ : σ ^ 2 ≤ 1)
    (hs : normSq s = σ ^ 2 + (x / 2) ^ 2) :
    Real.log (x / 2) ≤ Real.log ‖s‖ ∧ Real.log ‖s‖ ≤ Real.log (x / 2) + 2 / x ^ 2 := by
  have hpos : 0 < (x / 2) ^ 2 := by positivity
  have hn : Real.log ‖s‖ = Real.log (normSq s) / 2 := by
    rw [Complex.norm_def, Real.log_sqrt (normSq_nonneg _)]
  rw [hn, hs]
  have hl2 : Real.log ((x / 2) ^ 2) = 2 * Real.log (x / 2) := by
    rw [Real.log_pow]; norm_num
  constructor
  · have : Real.log ((x / 2) ^ 2) ≤ Real.log (σ ^ 2 + (x / 2) ^ 2) :=
      Real.log_le_log hpos (by nlinarith [sq_nonneg σ])
    linarith
  · have e : σ ^ 2 + (x / 2) ^ 2 = (x / 2) ^ 2 * (1 + 4 * σ ^ 2 / x ^ 2) := by
      field_simp; ring
    rw [e, Real.log_mul hpos.ne' (by positivity), hl2]
    have h1 : Real.log (1 + 4 * σ ^ 2 / x ^ 2) ≤ 4 * σ ^ 2 / x ^ 2 := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 4 * σ ^ 2 / x ^ 2)
      linarith
    have h2 : 4 * σ ^ 2 / x ^ 2 ≤ 4 / x ^ 2 := by
      apply div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h3 : (4 : ℝ) / x ^ 2 = 2 * (2 / x ^ 2) := by ring
    linarith

/-! ### The rational parts of `α` -/

theorem norm_rational_le {s : ℂ} {x : ℝ} (hx : 0 < x) (him : |s.im| = x / 2) :
    ‖1 / (2 * s) + 1 / (s - 1)‖ ≤ 3 / x := by
  have hnorm : x / 2 ≤ ‖s‖ := him ▸ Complex.abs_im_le_norm s
  have hnorm1 : x / 2 ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1)
    simp only [sub_im, one_im, sub_zero] at this
    linarith
  have h1 : ‖1 / (2 * s)‖ ≤ 1 / x := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat]
    rw [div_le_div_iff₀ (by linarith) hx]
    linarith
  have h2 : ‖1 / (s - 1)‖ ≤ 2 / x := by
    rw [norm_div, norm_one]
    rw [div_le_div_iff₀ (by linarith) hx]
    linarith
  calc ‖1 / (2 * s) + 1 / (s - 1)‖ ≤ ‖1 / (2 * s)‖ + ‖1 / (s - 1)‖ := norm_add_le _ _
    _ ≤ 1 / x + 2 / x := add_le_add h1 h2
    _ = 3 / x := by ring

/-- `α(s) = ρ(s) + ℓ(s) + i θ(s)` with `ρ` the rational part, `ℓ = (log‖s‖ − log 2π)/2`,
`θ = arg s / 2`. -/
theorem alpha_decomp {s : ℂ} (hs : s ≠ 0) :
    alpha s = (1 / (2 * s) + 1 / (s - 1)) +
      (((Real.log ‖s‖ - Real.log (2 * π)) / 2 : ℝ) : ℂ) + ((arg s / 2 : ℝ) : ℂ) * I := by
  unfold alpha
  have e1 : s / (2 * (π : ℂ)) = s * (((2 * π)⁻¹ : ℝ) : ℂ) := by
    push_cast; field_simp
  have hnorm : ‖s / (2 * (π : ℂ))‖ = ‖s‖ / (2 * π) := by
    rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have harg : arg (s / (2 * (π : ℂ))) = arg s := by
    rw [e1, Complex.arg_mul_real (by positivity)]
  have hlog : Complex.log (s / (2 * (π : ℂ))) =
      ((Real.log ‖s‖ - Real.log (2 * π) : ℝ) : ℂ) + ((arg s : ℝ) : ℂ) * I := by
    rw [Complex.log, hnorm, harg, Real.log_div (norm_ne_zero_iff.mpr hs) (by positivity)]
  rw [hlog]; push_cast; ring

/-! ### The real part of `α(v)² − α(w)²` -/

theorem abs_add_le' (a b : ℝ) : |a + b| ≤ |a| + |b| :=
  abs_le.mpr ⟨by linarith [neg_abs_le a, neg_abs_le b], by linarith [le_abs_self a, le_abs_self b]⟩

theorem abs_sub_le' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  exact (abs_add_le' a (-b)).trans (by rw [abs_neg])

theorem re_prod_bound (P R : ℂ) (a b c d : ℝ) :
    |((P + (a : ℂ) + (b : ℂ) * I) * (R + (c : ℂ) + (d : ℂ) * I)).re| ≤
      (‖P‖ + |a|) * (‖R‖ + |c|) + (‖P‖ + |b|) * (‖R‖ + |d|) := by
  have hre : ((P + (a : ℂ) + (b : ℂ) * I) * (R + (c : ℂ) + (d : ℂ) * I)).re =
      (P.re + a) * (R.re + c) - (P.im + b) * (R.im + d) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
      zero_mul, zero_add]
  rw [hre]
  have h1 : |(P.re + a) * (R.re + c)| ≤ (‖P‖ + |a|) * (‖R‖ + |c|) := by
    rw [abs_mul]
    apply mul_le_mul (le_trans (abs_add_le' _ _) (add_le_add (Complex.abs_re_le_norm P) le_rfl))
      (le_trans (abs_add_le' _ _) (add_le_add (Complex.abs_re_le_norm R) le_rfl)) (abs_nonneg _)
      (by positivity)
  have h2 : |(P.im + b) * (R.im + d)| ≤ (‖P‖ + |b|) * (‖R‖ + |d|) := by
    rw [abs_mul]
    apply mul_le_mul (le_trans (abs_add_le' _ _) (add_le_add (Complex.abs_im_le_norm P) le_rfl))
      (le_trans (abs_add_le' _ _) (add_le_add (Complex.abs_im_le_norm R) le_rfl)) (abs_nonneg _)
      (by positivity)
  calc |(P.re + a) * (R.re + c) - (P.im + b) * (R.im + d)|
      ≤ |(P.re + a) * (R.re + c)| + |(P.im + b) * (R.im + d)| := abs_sub_le' _ _
    _ ≤ _ := add_le_add h1 h2

theorem v_ne_zero {x y : ℝ} (hx : 0 < x) : v (x + y * I) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  rw [v_im] at this
  simp at this
  linarith

theorem w_ne_zero {x y : ℝ} (hx : 0 < x) : w (x + y * I) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  rw [w_im] at this
  simp at this
  linarith

theorem sqrt_facts {x : ℝ} (hx : (5900000000000 : ℝ) ≤ x) :
    (2400000 : ℝ) ≤ Real.sqrt x ∧ Real.sqrt x * Real.sqrt x = x ∧ Real.log x ≤ 2 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  refine ⟨?_, Real.mul_self_sqrt hx0.le, ?_⟩
  · rw [show (2400000 : ℝ) = Real.sqrt ((2400000 : ℝ) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  · have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
    rw [Real.log_sqrt hx0.le] at h1
    linarith

set_option maxHeartbeats 1000000 in
theorem re_alpha_sq_diff_le {x y : ℝ} (hx : (5900000000000 : ℝ) ≤ x) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |(alpha (v (x + y * I)) ^ 2 - alpha (w (x + y * I)) ^ 2).re| ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have hv0 := v_ne_zero (y := y) hx0
  have hw0 := w_ne_zero (y := y) hx0
  -- bounds on the pieces
  have hρv' : ‖1 / (2 * v (x + y * I)) + 1 / (v (x + y * I) - 1)‖ ≤ 3 / x :=
    norm_rational_le hx0 (by rw [v_im, hre, abs_div, abs_of_pos hx0]; norm_num)
  have hρw' : ‖1 / (2 * w (x + y * I)) + 1 / (w (x + y * I) - 1)‖ ≤ 3 / x :=
    norm_rational_le hx0 (by rw [w_im, hre, abs_div, abs_neg, abs_of_pos hx0]; norm_num)
  have hlv := log_norm_bounds hx0 (σ := (1 - y) / 2) (by nlinarith) normSq_v
  have hlw := log_norm_bounds hx0 (σ := (1 + y) / 2) (by nlinarith) normSq_w
  have hargv := Complex.abs_arg_le_pi (v (x + y * I))
  have hargw := Complex.abs_arg_le_pi (w (x + y * I))
  obtain ⟨_, h0, h2⟩ := arg_sum_bounds hx1 hy0 hy1
  have hlogx2 : Real.log (x / 2) ≤ Real.log x := Real.log_le_log (by positivity) (by linarith)
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hL : 0 < Real.log (x / 2) - Real.log (2 * π) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    apply Real.log_pos
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [Real.pi_lt_d6]
  have hlog2pi : 1 ≤ Real.log (2 * π) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith [Real.exp_one_lt_d9, Real.pi_gt_three]
  have hx2 : 2 / x ^ 2 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hxinv : 0 < 1 / x := by positivity
  -- the product in the decomposed form
  have hαv := alpha_decomp hv0
  have hαw := alpha_decomp hw0
  have hprod : alpha (v (x + y * I)) ^ 2 - alpha (w (x + y * I)) ^ 2 =
      (alpha (v (x + y * I)) - alpha (w (x + y * I))) *
        (alpha (v (x + y * I)) + alpha (w (x + y * I))) := by ring
  rw [hprod, hαv, hαw]
  have e : ∀ (ρv ρw : ℂ) (ℓv ℓw θv θw : ℝ),
      (ρv + (ℓv : ℂ) + (θv : ℂ) * I - (ρw + (ℓw : ℂ) + (θw : ℂ) * I)) *
        (ρv + (ℓv : ℂ) + (θv : ℂ) * I + (ρw + (ℓw : ℂ) + (θw : ℂ) * I)) =
      ((ρv - ρw) + ((ℓv - ℓw : ℝ) : ℂ) + ((θv - θw : ℝ) : ℂ) * I) *
        ((ρv + ρw) + ((ℓv + ℓw : ℝ) : ℂ) + ((θv + θw : ℝ) : ℂ) * I) := by
    intros; push_cast; ring
  rw [e]
  refine le_trans (re_prod_bound _ _ _ _ _ _) ?_
  generalize hρv : 1 / (2 * v (x + y * I)) + 1 / (v (x + y * I) - 1) = ρv at hρv' ⊢
  generalize hρw : 1 / (2 * w (x + y * I)) + 1 / (w (x + y * I) - 1) = ρw at hρw' ⊢
  generalize hLv : Real.log ‖v (x + y * I)‖ = Lv at hlv ⊢
  generalize hLw : Real.log ‖w (x + y * I)‖ = Lw at hlw ⊢
  generalize hAv : arg (v (x + y * I)) = Av at hargv h0 h2 ⊢
  generalize hAw : arg (w (x + y * I)) = Aw at hargw h0 h2 ⊢
  have h6x : (6 : ℝ) / x = 3 / x + 3 / x := by ring
  have h2x : (2 : ℝ) / x ^ 2 = 2 * (1 / x ^ 2) := by ring
  have h2x' : (2 : ℝ) / x = 2 * (1 / x) := by ring
  have h7x : (7 : ℝ) / x = 6 / x + 1 / x := by ring
  have hP : ‖ρv - ρw‖ ≤ 6 / x := by
    calc ‖ρv - ρw‖ ≤ ‖ρv‖ + ‖ρw‖ := norm_sub_le _ _
      _ ≤ 6 / x := by linarith only [hρv', hρw', h6x]
  have hR : ‖ρv + ρw‖ ≤ 6 / x := by
    calc ‖ρv + ρw‖ ≤ ‖ρv‖ + ‖ρw‖ := norm_add_le _ _
      _ ≤ 6 / x := by linarith only [hρv', hρw', h6x]
  have ha : |(Lv - Real.log (2 * π)) / 2 - (Lw - Real.log (2 * π)) / 2| ≤ 1 / x ^ 2 := by
    rw [abs_le]; constructor <;> linarith only [hlv.1, hlv.2, hlw.1, hlw.2, h2x]
  have hb : |Av / 2 - Aw / 2| ≤ 4 := by
    rw [abs_le] at hargv hargw ⊢
    constructor <;> linarith only [hargv.1, hargv.2, hargw.1, hargw.2, Real.pi_lt_d6]
  have hc : |(Lv - Real.log (2 * π)) / 2 + (Lw - Real.log (2 * π)) / 2| ≤ Real.log x := by
    rw [abs_le]
    constructor
    · linarith only [hlv.1, hlw.1, hL, hlogx0]
    · linarith only [hlv.2, hlw.2, hlogx2, hx2, hlog2pi]
  have hd : |Av / 2 + Aw / 2| ≤ 1 / x := by
    rw [abs_le]; constructor <;> linarith only [h0, h2, hxinv, h2x']
  obtain ⟨hsqrt, hsq, hlogx⟩ := sqrt_facts hx
  have hs0 : 0 < Real.sqrt x := by linarith
  calc _ ≤ (6 / x + 1 / x ^ 2) * (6 / x + Real.log x) + (6 / x + 4) * (6 / x + 1 / x) := by
        gcongr
    _ ≤ (7 / x) * (3 * Real.sqrt x) + 5 * (7 / x) := by
        have h1 : 1 / x ^ 2 ≤ 1 / x := by
          rw [div_le_div_iff₀ (by positivity) hx0]
          have hxx : 0 ≤ x * (x - 1) := mul_nonneg hx0.le (by linarith only [hx1])
          linarith only [hxx]
        have h2 : 6 / x ≤ Real.sqrt x := by
          rw [div_le_iff₀ hx0]
          have := mul_le_mul hsqrt hx (by norm_num) hs0.le
          linarith only [this]
        have h3 : 6 / x ≤ 1 := by rw [div_le_one hx0]; linarith only [hx]
        have h4 : 0 ≤ 6 / x + Real.log x := by positivity
        have h5 : 0 ≤ 6 / x + 1 / x := by positivity
        have h6 : 6 / x + 1 / x ^ 2 ≤ 7 / x := by linarith only [h1, h7x]
        have h7 : 6 / x + Real.log x ≤ 3 * Real.sqrt x := by linarith only [h2, hlogx]
        have h8 : 6 / x + 4 ≤ 5 := by linarith only [h3]
        have h9 : 6 / x + 1 / x ≤ 7 / x := le_of_eq h7x.symm
        exact add_le_add (mul_le_mul h6 h7 h4 (by positivity))
          (mul_le_mul h8 h9 h5 (by norm_num))
    _ ≤ 1 := by
        have h1 : 7 / x * (3 * Real.sqrt x) ≤ 1 / 100000 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hx0]
          have := mul_le_mul_of_nonneg_left hsqrt hs0.le
          linarith only [this, hsq, hs0]
        have h3 : 5 * (7 / x) ≤ 1 / 100000 := by
          rw [show 5 * (7 / x) = 35 / x by ring, div_le_div_iff₀ hx0 (by norm_num)]
          linarith only [hx]
        linarith only [h1, h3]

/-! ### The norm of `M_t` -/

theorem arg_div_two (s : ℂ) : arg (s / 2) = arg s := by
  rw [show s / 2 = s * ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.arg_mul_real (by norm_num)]

theorem norm_Mt (t : ℝ) (s : ℂ) :
    ‖Mt t s‖ = ‖s * (s - 1)‖ / 16 * Real.sqrt (2 * π) *
      Real.exp (-(s.re / 2) * Real.log π +
        ((s.re / 2 - 1 / 2) * Real.log (‖s‖ / 2) - s.im / 2 * arg s - s.re / 2) +
        t * (alpha s ^ 2).re / 4) := by
  have e : Mt t s = (s * (s - 1) / 16 * (Real.sqrt (2 * π) : ℂ)) *
      Complex.exp (-(s / 2) * (Real.log π : ℂ) + ((s / 2 - 1 / 2) * Complex.log (s / 2) - s / 2) +
        (t : ℂ) * alpha s ^ 2 / 4) := by
    unfold Mt M0
    rw [Complex.exp_add, Complex.exp_add]
    ring
  rw [e, norm_mul, norm_mul, norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp]
  congr 2
  have h1 : (-(s / 2) * (Real.log π : ℂ)).re = -(s.re / 2) * Real.log π := by
    simp [Complex.mul_re]
  have h2 : ((s / 2 - 1 / 2) * Complex.log (s / 2) - s / 2).re =
      (s.re / 2 - 1 / 2) * Real.log (‖s‖ / 2) - s.im / 2 * arg s - s.re / 2 := by
    rw [sub_re, mul_re, log_re, log_im, arg_div_two, norm_div, Complex.norm_ofNat]
    simp [Complex.div_ofNat_re, Complex.div_ofNat_im]
  have h3 : ((t : ℂ) * alpha s ^ 2 / 4).re = t * (alpha s ^ 2).re / 4 := by
    rw [show (t : ℂ) * alpha s ^ 2 / 4 = ((t / 4 : ℝ) : ℂ) * alpha s ^ 2 by push_cast; ring,
      re_ofReal_mul]
    ring
  rw [add_re, add_re, h1, h2, h3]

/-! ### The bound -/

/-- **A crude form of (A.3).** `|γ_t(x+iy)| ≤ e^{1/10} 𝒬^{−y/2}` for `x ≥ X_e`, `t ∈ [0, 1/5]`,
`y ∈ [0, 1]`. -/
theorem gamma_crude {x t y : ℝ} (hx : (Const.Xe : ℝ) ≤ x) (ht : t ∈ Icc (0 : ℝ) (1 / 5))
    (hy : y ∈ Icc (0 : ℝ) 1) :
    ‖gamma t (x + y * I)‖ ≤ Real.exp (1 / 10) * Q x ^ (-y / 2) := by
  have hx' : (5900000000000 : ℝ) ≤ x := by
    have : (Const.Xe : ℝ) = 5900000000000 := by norm_num [Const.Xe]
    linarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have him : ((x : ℂ) + y * I).im = y := by simp
  have hv0 := v_ne_zero (y := y) hx0
  have hw0 := w_ne_zero (y := y) hx0
  have hw1 : w (x + y * I) - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [sub_im, w_im, hre] at this
    simp at this
    linarith
  unfold gamma
  rw [norm_div, norm_Mt, norm_Mt]
  have hvw : v (x + y * I) * (v (x + y * I) - 1) = w (x + y * I) * (w (x + y * I) - 1) := by
    unfold v; ring
  rw [hvw]
  have hK : 0 < ‖w (x + y * I) * (w (x + y * I) - 1)‖ / 16 * Real.sqrt (2 * π) := by
    have : 0 < ‖w (x + y * I) * (w (x + y * I) - 1)‖ :=
      norm_pos_iff.mpr (mul_ne_zero hw0 hw1)
    positivity
  rw [mul_div_mul_left _ _ hK.ne', ← Real.exp_sub]
  have hQdef : Q x = x / (4 * π) := rfl
  have hQpos : 0 < Q x := by rw [hQdef]; positivity
  rw [Real.rpow_def_of_pos hQpos, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  -- the pieces
  rw [v_re, w_re, v_im, w_im, hre, him]
  have hlv := log_norm_bounds hx0 (σ := (1 - y) / 2) (by nlinarith [hy.1, hy.2]) normSq_v
  have hlw := log_norm_bounds hx0 (σ := (1 + y) / 2) (by nlinarith [hy.1, hy.2]) normSq_w
  obtain ⟨harg, _, _⟩ := arg_sum_bounds hx1 hy.1 hy.2
  have hRe := re_alpha_sq_diff_le hx' hy.1 hy.2
  rw [sub_re, abs_le] at hRe
  have hlogv : Real.log (‖v (x + y * I)‖ / 2) = Real.log ‖v (x + y * I)‖ - Real.log 2 :=
    Real.log_div (norm_ne_zero_iff.mpr hv0) two_ne_zero
  have hlogw : Real.log (‖w (x + y * I)‖ / 2) = Real.log ‖w (x + y * I)‖ - Real.log 2 :=
    Real.log_div (norm_ne_zero_iff.mpr hw0) two_ne_zero
  have hlx2 : Real.log (x / 2) = Real.log x - Real.log 2 := Real.log_div hx0.ne' two_ne_zero
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [hlogv, hlogw, hQdef, Real.log_div hx0.ne' (by positivity),
    Real.log_mul (by norm_num) Real.pi_pos.ne']
  rw [hlx2] at hlv hlw
  -- product facts
  have h1 : -((1 + y) / 4) * Real.log ‖v (x + y * I)‖ ≤ -((1 + y) / 4) * (Real.log x - Real.log 2) :=
    mul_le_mul_of_nonpos_left hlv.1 (by linarith [hy.1])
  have h2 : (1 - y) / 4 * Real.log ‖w (x + y * I)‖ ≤
      (1 - y) / 4 * (Real.log x - Real.log 2 + 2 / x ^ 2) :=
    mul_le_mul_of_nonneg_left hlw.2 (by linarith [hy.2])
  have h3 : -(x / 4) * (arg (v (x + y * I)) + arg (w (x + y * I))) ≤
      -(x / 4) * (2 * y / x - 8 / x ^ 3) :=
    mul_le_mul_of_nonpos_left harg (by linarith)
  have h4 : -(x / 4) * (2 * y / x - 8 / x ^ 3) = -(y / 2) + 2 / x ^ 2 := by
    field_simp; ring
  have h5 : t * ((alpha (v (x + y * I)) ^ 2).re - (alpha (w (x + y * I)) ^ 2).re) ≤ 1 / 5 := by
    have := mul_le_mul_of_nonneg_left hRe.2 ht.1
    linarith [ht.2]
  have hx2 : 2 / x ^ 2 ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hy2 : (1 - y) / 4 * (2 / x ^ 2) ≤ 2 / x ^ 2 := by
    have : (1 - y) / 4 ≤ 1 := by linarith [hy.1]
    have : 0 ≤ 2 / x ^ 2 := by positivity
    nlinarith
  rw [hlog4]
  linarith [h1, h2, h3, h4, h5, hx2, hy2, hy.1, hy.2]

end Approx

end DBN
