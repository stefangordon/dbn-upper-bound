import Mathlib

/-!
# Zeta estimates for the source recipe (Appendix C.3)

Two self-contained results used by the uniform source recipe:

* the Euler-product lower bound `|ζ(s)| ≥ ζ(2a)/ζ(a)` for `Re s ≥ a > 1` (Appendix C.3.5,
  `m(a) = ζ(2a)/ζ(a)`), proved from Mathlib's Euler product in exponential-logarithmic form;
* the termwise inequality underlying the common-phase combination (C25), for `n ≥ 1`,
  `Re s₁ ≥ a₁ + 3(h − h₋)/2` and `0 < h₋ ≤ h`. It uses positivity of
  `A − Bv + Dv²` and monotonicity of `A u³ − B u⁴ + D u⁵` on `[0,1]`,
  with `A = 15/14`, `B = 16/21` and `D = 1/6`. The weighted infinite-series
  specialization and its connection to the source floors are not proved here.
-/

noncomputable section

namespace DBN.Zeta

open Real Complex

/-! ### Elementary logarithm bounds -/

theorem neg_log_one_sub_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    0 ≤ -Real.log (1 - u) ∧ -Real.log (1 - u) ≤ 2 * u := by
  have h1 : 0 < 1 - u := by linarith
  constructor
  · have := Real.log_nonpos h1.le (by linarith)
    linarith
  · have := Real.one_sub_inv_le_log_of_pos h1
    have h3 : (1 - u)⁻¹ - 1 ≤ 2 * u := by
      rw [inv_eq_one_div, div_sub_one h1.ne', div_le_iff₀ h1]
      nlinarith
    linarith

theorem log_one_add_bounds {u : ℝ} (hu0 : 0 ≤ u) :
    0 ≤ Real.log (1 + u) ∧ Real.log (1 + u) ≤ u := by
  constructor
  · exact Real.log_nonneg (by linarith)
  · have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + u)
    linarith

/-! ### Prime powers -/

theorem prime_two_le (p : Nat.Primes) : (2 : ℝ) ≤ (p : ℝ) := by
  exact_mod_cast p.2.two_le

theorem prime_rpow_bounds {a : ℝ} (ha : 1 ≤ a) (p : Nat.Primes) :
    0 ≤ (p : ℝ) ^ (-a) ∧ (p : ℝ) ^ (-a) ≤ 1 / 2 := by
  have hp := prime_two_le p
  refine ⟨Real.rpow_nonneg (by linarith) _, ?_⟩
  calc (p : ℝ) ^ (-a) = ((p : ℝ) ^ a)⁻¹ := Real.rpow_neg (by linarith) a
    _ ≤ ((2 : ℝ) ^ a)⁻¹ := by
        apply inv_anti₀ (by positivity)
        exact Real.rpow_le_rpow (by norm_num) hp (by linarith)
    _ ≤ ((2 : ℝ) ^ (1 : ℝ))⁻¹ := by
        apply inv_anti₀ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
    _ = 1 / 2 := by rw [Real.rpow_one]; norm_num

theorem summable_neg_log_one_sub_prime {a : ℝ} (ha : 1 < a) :
    Summable (fun p : Nat.Primes => -Real.log (1 - (p : ℝ) ^ (-a))) := by
  have hS : Summable (fun p : Nat.Primes => 2 * (p : ℝ) ^ (-a)) :=
    (Nat.Primes.summable_rpow.mpr (by linarith)).mul_left 2
  refine Summable.of_nonneg_of_le (fun p => (neg_log_one_sub_bounds (prime_rpow_bounds ha.le p).1
    (prime_rpow_bounds ha.le p).2).1) (fun p => (neg_log_one_sub_bounds (prime_rpow_bounds ha.le p).1
    (prime_rpow_bounds ha.le p).2).2) hS

theorem summable_neg_log_one_add_prime {a : ℝ} (ha : 1 < a) :
    Summable (fun p : Nat.Primes => -Real.log (1 + (p : ℝ) ^ (-a))) := by
  have hS : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-a)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  refine (Summable.of_nonneg_of_le (fun p => (log_one_add_bounds (prime_rpow_bounds ha.le p).1).1)
    (fun p => (log_one_add_bounds (prime_rpow_bounds ha.le p).1).2) hS).neg

/-! ### The real zeta values through the Euler product -/

set_option maxHeartbeats 1000000 in
theorem norm_zeta_real {a : ℝ} (ha : 1 < a) :
    ‖riemannZeta (a : ℂ)‖ =
      Real.exp (∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-a))) := by
  have hre : 1 < (a : ℂ).re := by simpa using ha
  rw [← riemannZeta_eulerProduct_exp_log hre]
  have e : ∀ p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(a : ℂ))) =
      ((-Real.log (1 - (p : ℝ) ^ (-a)) : ℝ) : ℂ) := by
    intro p
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
    have h1 : ((p : ℕ) : ℂ) ^ (-(a : ℂ)) = (((p : ℝ) ^ (-a) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hp0, Complex.ofReal_natCast, Complex.ofReal_neg]
    have h2 : (0 : ℝ) ≤ 1 - (p : ℝ) ^ (-a) := by
      linarith [(prime_rpow_bounds ha.le p).2]
    rw [h1, show (1 : ℂ) - (((p : ℝ) ^ (-a) : ℝ) : ℂ) = ((1 - (p : ℝ) ^ (-a) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log h2]
    push_cast
    ring
  rw [tsum_congr e, ← Complex.ofReal_tsum, Complex.norm_exp, Complex.ofReal_re]

set_option maxHeartbeats 1000000 in
/-- **Euler-product lower bound**: `|ζ(s)| ≥ ζ(2a)/ζ(a)` for `Re s ≥ a > 1`. -/
theorem norm_zeta_ge {a : ℝ} (ha : 1 < a) {s : ℂ} (hs : a ≤ s.re) :
    ‖riemannZeta ((2 * a : ℝ) : ℂ)‖ / ‖riemannZeta (a : ℂ)‖ ≤ ‖riemannZeta s‖ := by
  have hs1 : 1 < s.re := by linarith
  have hf : Summable (fun p : Nat.Primes => (p : ℂ) ^ (-s)) := by
    have h1 : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-s.re)) :=
      Nat.Primes.summable_rpow.mpr (by linarith)
    have h2 : Summable (fun p : Nat.Primes => ‖(p : ℂ) ^ (-s)‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) h1
      rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
    exact h2.of_norm
  have hsum := hf.clog_one_sub.neg
  rw [← riemannZeta_eulerProduct_exp_log hs1, Complex.norm_exp, Complex.re_tsum hsum,
    norm_zeta_real (by linarith : 1 < 2 * a), norm_zeta_real ha, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hS1 := summable_neg_log_one_sub_prime ha
  have hS2 := summable_neg_log_one_sub_prime (by linarith : 1 < 2 * a)
  have hSre : Summable (fun p : Nat.Primes => (-Complex.log (1 - (p : ℂ) ^ (-s))).re) :=
    (Complex.hasSum_re hsum.hasSum).summable
  rw [← hS2.tsum_sub hS1]
  apply Summable.tsum_le_tsum _ (hS2.sub hS1) hSre
  intro p
  have hp := prime_two_le p
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  obtain ⟨hu0, hu⟩ := prime_rpow_bounds ha.le p
  set u := (p : ℝ) ^ (-a) with hu_def
  have h2a : (p : ℝ) ^ (-(2 * a)) = u ^ 2 := by
    rw [hu_def, show -(2 * a) = (-a) * (2 : ℕ) by ring, Real.rpow_mul hp0.le, Real.rpow_natCast]
  have hlog : -Real.log (1 - (p : ℝ) ^ (-(2 * a))) - -Real.log (1 - u) = -Real.log (1 + u) := by
    rw [h2a, show (1 : ℝ) - u ^ 2 = (1 - u) * (1 + u) by ring,
      Real.log_mul (by linarith) (by linarith)]
    ring
  rw [hlog, Complex.neg_re, Complex.log_re, neg_le_neg_iff]
  -- `‖1 − p^{−s}‖ ≤ 1 + p^{−a}`
  have hnorm : ‖(p : ℂ) ^ (-s)‖ ≤ u := by
    rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re, hu_def]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hpos : 0 < ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
    rw [norm_one] at this
    linarith
  apply Real.log_le_log hpos
  calc ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ 1 + u := by rw [norm_one]; linarith

/-! ### The common-phase combination (C25) -/

/-- `q(u) = A u³ − B u⁴ + D u⁵` with `A = 15/14`, `B = 16/21`, `D = 1/6`. -/
def q (u : ℝ) : ℝ := 15 / 14 * u ^ 3 - 16 / 21 * u ^ 4 + 1 / 6 * u ^ 5

theorem hasDerivAt_q (s : ℝ) :
    HasDerivAt q (s ^ 2 * (45 / 14 - 64 / 21 * s + 5 / 6 * s ^ 2)) s := by
  have h := (((hasDerivAt_pow 3 s).const_mul (15 / 14 : ℝ)).sub
    ((hasDerivAt_pow 4 s).const_mul (16 / 21 : ℝ))).add ((hasDerivAt_pow 5 s).const_mul (1 / 6 : ℝ))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by simp [q])
  push_cast
  ring

theorem q_mono {u um : ℝ} (hu : 0 ≤ u) (hum : u ≤ um) (hum1 : um ≤ 1) : q u ≤ q um := by
  have hmono : MonotoneOn q (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact (continuous_iff_continuousAt.mpr fun s => (hasDerivAt_q s).continuousAt).continuousOn
    · intro s _; exact (hasDerivAt_q s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hasDerivAt_q s).deriv]
      apply mul_nonneg (sq_nonneg s)
      nlinarith [hs.1, hs.2, sq_nonneg s]
  exact hmono ⟨hu, by linarith⟩ ⟨by linarith, hum1⟩ hum

/-- `P(v) = A − Bv + Dv²` is positive on `[0, 1]`. -/
theorem P_pos {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : 0 < 15 / 14 - 16 / 21 * v + 1 / 6 * v ^ 2 := by
  nlinarith [sq_nonneg v]

/-- **(C25), termwise.** For `n ≥ 1`, `Re s₁ ≥ a₁ + 3(h − h₋)/2`, `0 < h₋ ≤ h`,
`Re[n^{−s₁}(A − B n^{−h/2} + D n^{−h})] ≤ n^{−a₁}(A − B n^{−h₋/2} + D n^{−h₋})`. -/
theorem term_le {n : ℕ} (hn : 1 ≤ n) {a1 h hm : ℝ} (hm0 : 0 < hm) (hh : hm ≤ h) {s1 : ℂ}
    (hs : a1 + 3 * (h - hm) / 2 ≤ s1.re) :
    ((n : ℂ) ^ (-s1) * (15 / 14 - 16 / 21 * (((n : ℝ) ^ (-(h / 2)) : ℝ) : ℂ) +
      1 / 6 * (((n : ℝ) ^ (-h) : ℝ) : ℂ))).re ≤
      (n : ℝ) ^ (-a1) * (15 / 14 - 16 / 21 * (n : ℝ) ^ (-(hm / 2)) + 1 / 6 * (n : ℝ) ^ (-hm)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set u := (n : ℝ) ^ (-(h / 2)) with hu
  set um := (n : ℝ) ^ (-(hm / 2)) with hum
  have hu0 : 0 ≤ u := Real.rpow_nonneg hn0.le _
  have hum1 : um ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have huum : u ≤ um := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hu2 : (n : ℝ) ^ (-h) = u ^ 2 := by
    rw [hu, show -h = -(h / 2) * (2 : ℕ) by ring, Real.rpow_mul hn0.le, Real.rpow_natCast]
  have hum2 : (n : ℝ) ^ (-hm) = um ^ 2 := by
    rw [hum, show -hm = -(hm / 2) * (2 : ℕ) by ring, Real.rpow_mul hn0.le, Real.rpow_natCast]
  -- the complex factor is a real number times `n^{−s₁}`
  have hP : (15 / 14 - 16 / 21 * (((n : ℝ) ^ (-(h / 2)) : ℝ) : ℂ) + 1 / 6 * (((n : ℝ) ^ (-h) : ℝ) : ℂ)) =
      ((15 / 14 - 16 / 21 * u + 1 / 6 * u ^ 2 : ℝ) : ℂ) := by
    rw [hu2]; push_cast; ring
  rw [hP, mul_comm, Complex.re_ofReal_mul]
  have hPpos := P_pos hu0 (huum.trans hum1)
  have hre : ((n : ℂ) ^ (-s1)).re ≤ (n : ℝ) ^ (-s1.re) := by
    calc ((n : ℂ) ^ (-s1)).re ≤ ‖(n : ℂ) ^ (-s1)‖ := Complex.re_le_norm _
      _ = (n : ℝ) ^ (-s1.re) := by rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  have hstep1 : (15 / 14 - 16 / 21 * u + 1 / 6 * u ^ 2) * ((n : ℂ) ^ (-s1)).re ≤
      (15 / 14 - 16 / 21 * u + 1 / 6 * u ^ 2) * (n : ℝ) ^ (-(a1 + 3 * (h - hm) / 2)) := by
    apply mul_le_mul_of_nonneg_left _ hPpos.le
    exact hre.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  -- `n^{−(a₁ + 3(h−h₋)/2)} P(u) = n^{−a₁} n^{3h₋/2} q(u)`, and `q u ≤ q um`
  have hq : (n : ℝ) ^ (-(a1 + 3 * (h - hm) / 2)) * (15 / 14 - 16 / 21 * u + 1 / 6 * u ^ 2) =
      (n : ℝ) ^ (-a1) * (n : ℝ) ^ (3 * hm / 2) * q u := by
    have e1 : (n : ℝ) ^ (-(a1 + 3 * (h - hm) / 2)) =
        (n : ℝ) ^ (-a1) * (n : ℝ) ^ (3 * hm / 2) * (n : ℝ) ^ (-(3 * h / 2)) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]; congr 1; ring
    have e2 : (n : ℝ) ^ (-(3 * h / 2)) = u ^ 3 := by
      rw [hu, show -(3 * h / 2) = -(h / 2) * (3 : ℕ) by ring, Real.rpow_mul hn0.le, Real.rpow_natCast]
    rw [e1, e2, q]; ring
  have hq' : (n : ℝ) ^ (-a1) * (n : ℝ) ^ (3 * hm / 2) * q um =
      (n : ℝ) ^ (-a1) * (15 / 14 - 16 / 21 * um + 1 / 6 * um ^ 2) := by
    have e2 : (n : ℝ) ^ (3 * hm / 2) * um ^ 3 = 1 := by
      rw [hum, show (3 * hm / 2) = -(hm / 2) * (-(3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_mul hn0.le,
        Real.rpow_neg (Real.rpow_nonneg hn0.le _), Real.rpow_natCast]
      have : (0 : ℝ) < (n : ℝ) ^ (-(hm / 2)) := Real.rpow_pos_of_pos hn0 _
      field_simp
    rw [q]
    have : (n : ℝ) ^ (-a1) * (n : ℝ) ^ (3 * hm / 2) * (15 / 14 * um ^ 3 - 16 / 21 * um ^ 4 + 1 / 6 * um ^ 5) =
        (n : ℝ) ^ (-a1) * ((n : ℝ) ^ (3 * hm / 2) * um ^ 3) * (15 / 14 - 16 / 21 * um + 1 / 6 * um ^ 2) := by
      ring
    rw [this, e2, mul_one]
  have hqq := q_mono hu0 huum hum1
  have hpos : 0 ≤ (n : ℝ) ^ (-a1) * (n : ℝ) ^ (3 * hm / 2) := by positivity
  calc (15 / 14 - 16 / 21 * u + 1 / 6 * u ^ 2) * ((n : ℂ) ^ (-s1)).re
      ≤ (15 / 14 - 16 / 21 * u + 1 / 6 * u ^ 2) * (n : ℝ) ^ (-(a1 + 3 * (h - hm) / 2)) := hstep1
    _ = (n : ℝ) ^ (-a1) * (n : ℝ) ^ (3 * hm / 2) * q u := by rw [mul_comm, hq]
    _ ≤ (n : ℝ) ^ (-a1) * (n : ℝ) ^ (3 * hm / 2) * q um := mul_le_mul_of_nonneg_left hqq hpos
    _ = (n : ℝ) ^ (-a1) * (15 / 14 - 16 / 21 * um + 1 / 6 * um ^ 2) := hq'
    _ = (n : ℝ) ^ (-a1) * (15 / 14 - 16 / 21 * (n : ℝ) ^ (-(hm / 2)) + 1 / 6 * (n : ℝ) ^ (-hm)) := by
        rw [hum2]

end DBN.Zeta
