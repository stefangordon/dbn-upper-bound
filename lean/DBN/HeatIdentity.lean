import Mathlib
import DBN.Approximation
import DBN.VonMangoldtSeries

/-!
# The heat identity (C13)

For `Re s > 1`,
`P_N(s,t) = ζ(s) + (t/4) ζ''(s) + R_heat − T_N`, where
`R_heat = Σ_{n ≤ N} (e^{t log²n/4} − 1 − t log²n/4) n^{−s}` and
`T_N = Σ_{n > N} (1 + t log²n/4) n^{−s}`,
proved from `ζ = L(1)` and `ζ'' = L(log² · 1)` on the half-plane and splitting the Dirichlet
series at `N`. The finite remainder has a real majorant for arbitrary `t` and `s`
(`norm_Rheat_le`). The infinite-tail norm bound (`norm_TN_le`) requires `t ≥ 0` and `Re s > 1`.
No infinite positive-time heated Dirichlet series is introduced.
-/

noncomputable section

namespace DBN.Zeta

open Complex LSeries
open scoped LSeries.notation

/-- `R_heat = Σ_{n ≤ N} (e^{t log²n/4} − 1 − t log²n/4) n^{−s}`. -/
def Rheat (N : ℕ) (s : ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, ((Approx.bt t n - 1 - t * Real.log n ^ 2 / 4 : ℝ) : ℂ) * (n : ℂ) ^ (-s)

/-- `T_N = Σ_{n > N} (1 + t log²n/4) n^{−s}`, indexed by `n = i + N + 1`. -/
def TN (N : ℕ) (s : ℂ) (t : ℝ) : ℂ :=
  ∑' i : ℕ, ((1 + t * Real.log ((i + N + 1 : ℕ) : ℝ) ^ 2 / 4 : ℝ) : ℂ) * ((i + N + 1 : ℕ) : ℂ) ^ (-s)

theorem cpow_neg_eq_exp {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    (n : ℂ) ^ (-s) = Complex.exp (-s * (Real.log n : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), ← Complex.natCast_log]
  ring_nf

theorem term_one_eq {n : ℕ} (hn : n ≠ 0) (s : ℂ) : term 1 s n = (n : ℂ) ^ (-s) := by
  rw [LSeries.term_def, if_neg hn, Pi.one_apply, Complex.cpow_neg, one_div]

theorem term_log2_eq {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    term (logMul^[2] 1) s n = ((Real.log n ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
  rw [LSeries.term_def, if_neg hn]
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, logMul,
    Pi.one_apply, mul_one]
  rw [Complex.cpow_neg, ← Complex.natCast_log]
  push_cast
  ring

theorem summable_log2 {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (logMul^[2] 1) s := by
  have habs : abscissaOfAbsConv (logMul 1) < s.re := by
    rw [LSeries.abscissaOfAbsConv_logMul, LSeries.abscissaOfAbsConv_one]; exact_mod_cast hs
  have := LSeriesSummable_logMul_of_lt_re habs
  simpa [Function.iterate_succ, Function.iterate_zero] using this

/-- The coefficient `c_n = (1 + t log²n/4) n^{−s}`. -/
def cN (s : ℂ) (t : ℝ) (n : ℕ) : ℂ := ((1 + t * Real.log n ^ 2 / 4 : ℝ) : ℂ) * (n : ℂ) ^ (-s)

theorem cN_eq_term {s : ℂ} (hs : 1 < s.re) (t : ℝ) :
    cN s t = fun n => term 1 s n + ((t : ℂ) / 4) * term (logMul^[2] 1) s n := by
  funext n
  rcases eq_or_ne n 0 with h | h
  · subst h
    have hs0 : -s ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    simp [cN, LSeries.term_zero, Complex.zero_cpow hs0]
  · rw [cN, term_one_eq h, term_log2_eq h]; push_cast; ring

theorem summable_cN {s : ℂ} (hs : 1 < s.re) (t : ℝ) : Summable (cN s t) := by
  have h1 : Summable (term 1 s) := LSeriesSummable_one_iff.mpr hs
  have h2 : Summable (term (logMul^[2] 1) s) := summable_log2 hs
  have h3 := Summable.add h1 (Summable.mul_left ((t : ℂ) / 4) h2)
  rw [cN_eq_term hs]
  exact h3

/-- `ζ(s) + (t/4) ζ''(s) = Σ_n c_n`. -/
theorem zeta_heat_eq_tsum {s : ℂ} (hs : 1 < s.re) (t : ℝ) :
    riemannZeta s + ((t : ℂ) / 4) * deriv (deriv riemannZeta) s = ∑' n, cN s t n := by
  have hmem : {z : ℂ | 1 < z.re} ∈ nhds s := isOpen_halfPlane.mem_nhds hs
  have hEq : riemannZeta =ᶠ[nhds s] LSeries 1 :=
    Filter.eventuallyEq_of_mem hmem fun z hz => (LSeries_one_eq_riemannZeta hz).symm
  have habs : abscissaOfAbsConv 1 < s.re := by
    rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hs
  have hζ'' : deriv (deriv riemannZeta) s = LSeries (logMul^[2] 1) s := by
    rw [hEq.deriv.deriv_eq, ← iteratedDeriv_one, ← iteratedDeriv_succ', LSeries_iteratedDeriv 2 habs]
    norm_num
  have h1 : Summable (term 1 s) := LSeriesSummable_one_iff.mpr hs
  have h2 : Summable (term (logMul^[2] 1) s) := summable_log2 hs
  rw [← LSeries_one_eq_riemannZeta hs, hζ'', LSeries, LSeries, ← tsum_mul_left,
    ← Summable.tsum_add h1 (Summable.mul_left ((t : ℂ) / 4) h2), cN_eq_term hs]

/-- **(C13).** `P_N(s,t) = ζ(s) + (t/4) ζ''(s) + R_heat − T_N` for `Re s > 1`. -/
theorem heat_identity {N : ℕ} {s : ℂ} (hs : 1 < s.re) (t : ℝ) :
    Approx.PN N s t =
      riemannZeta s + ((t : ℂ) / 4) * deriv (deriv riemannZeta) s + Rheat N s t - TN N s t := by
  have hcsum := summable_cN hs t
  have hc0 : cN s t 0 = 0 := by
    have hs0 : -s ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    simp [cN, Complex.zero_cpow hs0]
  have hsplit := hcsum.sum_add_tsum_nat_add (N + 1)
  have hrange : ∑ i ∈ Finset.range (N + 1), cN s t i = ∑ n ∈ Finset.Icc 1 N, cN s t n := by
    have e : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [Finset.sum_range_succ', hc0, add_zero, e, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun i _ => by rw [add_comm]
  have htail : ∑' i, cN s t (i + (N + 1)) = TN N s t := by
    unfold TN
    apply tsum_congr
    intro i
    simp only [cN]
    rw [show i + (N + 1) = i + N + 1 by ring]
  have hPN : Approx.PN N s t = ∑ n ∈ Finset.Icc 1 N, (Approx.bt t n : ℂ) * (n : ℂ) ^ (-s) := by
    unfold Approx.PN
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [cpow_neg_eq_exp (by omega)]
  have hR : Rheat N s t =
      (∑ n ∈ Finset.Icc 1 N, (Approx.bt t n : ℂ) * (n : ℂ) ^ (-s)) - ∑ n ∈ Finset.Icc 1 N, cN s t n := by
    unfold Rheat
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    simp only [cN]
    push_cast
    ring
  rw [zeta_heat_eq_tsum hs, ← hsplit, hrange, htail, hPN, hR]
  ring

/-! ### Norm bounds by the real series at `Re s` -/

/-- The real tail `Σ_{n > N} (1 + t log²n/4) n^{−a}`. -/
def TNR (N : ℕ) (a t : ℝ) : ℝ :=
  ∑' i : ℕ, (1 + t * Real.log ((i + N + 1 : ℕ) : ℝ) ^ 2 / 4) / ((i + N + 1 : ℕ) : ℝ) ^ a

/-- The real heat remainder `Σ_{n ≤ N} (e^{t log²n/4} − 1 − t log²n/4) n^{−a}`. -/
def RheatR (N : ℕ) (a t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (Approx.bt t n - 1 - t * Real.log n ^ 2 / 4) / (n : ℝ) ^ a

theorem bt_sub_nonneg (t : ℝ) (n : ℕ) : 0 ≤ Approx.bt t n - 1 - t * Real.log n ^ 2 / 4 := by
  unfold Approx.bt
  have := Real.add_one_le_exp (t * Real.log n ^ 2 / 4)
  linarith

theorem norm_Rheat_le (N : ℕ) (s : ℂ) (t : ℝ) : ‖Rheat N s t‖ ≤ RheatR N s.re t := by
  unfold Rheat RheatR
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n hn => ?_))
  rw [Finset.mem_Icc] at hn
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bt_sub_nonneg t n),
    Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re, Real.rpow_neg (by positivity)]
  try ring

theorem summable_log2_real {a : ℝ} (ha : 1 < a) :
    Summable (fun n : ℕ => Real.log n ^ 2 / (n : ℝ) ^ a) := by
  have h1 : LSeriesSummable (logMul^[2] 1) (a : ℂ) := summable_log2 (by simpa using ha)
  have e : ∀ n : ℕ, term (logMul^[2] 1) (a : ℂ) n = ((Real.log n ^ 2 / (n : ℝ) ^ a : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with h | h
    · subst h; simp [LSeries.term_zero, Real.zero_rpow (show a ≠ 0 by linarith)]
    · rw [term_log2_eq h, Complex.ofReal_div, Complex.cpow_neg, div_eq_mul_inv,
        Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  exact Complex.summable_ofReal.mp (h1.congr e)

theorem summable_one_real {a : ℝ} (ha : 1 < a) : Summable (fun n : ℕ => 1 / (n : ℝ) ^ a) := by
  have h1 : LSeriesSummable 1 (a : ℂ) := LSeriesSummable_one_iff.mpr (by simpa using ha)
  have e : ∀ n : ℕ, term 1 (a : ℂ) n = ((1 / (n : ℝ) ^ a : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with h | h
    · subst h; simp [LSeries.term_zero, Real.zero_rpow (show a ≠ 0 by linarith)]
    · rw [term_one_eq h, Complex.cpow_neg, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, one_div]
  exact Complex.summable_ofReal.mp (h1.congr e)

theorem summable_TNR_terms {a : ℝ} (ha : 1 < a) (t : ℝ) (N : ℕ) :
    Summable (fun i : ℕ => (1 + t * Real.log ((i + N + 1 : ℕ) : ℝ) ^ 2 / 4) /
      ((i + N + 1 : ℕ) : ℝ) ^ a) := by
  have h : Summable (fun n : ℕ => (1 + t * Real.log n ^ 2 / 4) / (n : ℝ) ^ a) := by
    have := (summable_one_real ha).add ((summable_log2_real ha).mul_left (t / 4))
    refine this.congr fun n => ?_
    ring
  have := (summable_nat_add_iff (N + 1)).mpr h
  refine this.congr fun i => ?_
  simp only [Nat.cast_add, Nat.cast_one]
  ring_nf

theorem norm_TN_le {t : ℝ} (ht : 0 ≤ t) (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ‖TN N s t‖ ≤ TNR N s.re t := by
  unfold TN TNR
  have hterm : ∀ i : ℕ, ‖((1 + t * Real.log ((i + N + 1 : ℕ) : ℝ) ^ 2 / 4 : ℝ) : ℂ) *
      ((i + N + 1 : ℕ) : ℂ) ^ (-s)‖ =
      (1 + t * Real.log ((i + N + 1 : ℕ) : ℝ) ^ 2 / 4) / ((i + N + 1 : ℕ) : ℝ) ^ s.re := by
    intro i
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re, Real.rpow_neg (by positivity)]
    try ring
  have hsum : Summable fun i => ‖((1 + t * Real.log ((i + N + 1 : ℕ) : ℝ) ^ 2 / 4 : ℝ) : ℂ) *
      ((i + N + 1 : ℕ) : ℂ) ^ (-s)‖ :=
    (summable_TNR_terms hs t N).congr fun i => (hterm i).symm
  exact (norm_tsum_le_tsum_norm hsum).trans (le_of_eq (tsum_congr hterm))

end DBN.Zeta
