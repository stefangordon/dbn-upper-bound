import Mathlib
import DBN.ZetaBounds

/-!
# The Dirichlet series `Φ_t = −ζ'/ζ − (t/4)(ζ''/ζ)'` (Appendix C.3.6)

For `Re s > 1`,
`Φ_t(s) = Σ_{n ≥ 2} A_t(n) n^{−s}`, `A_t(n) = Λ(n) + (t/4)[Λ(n) log²n + log n Σ_{ab=n} Λ(a)Λ(b)]`,
with coefficients that are nondecreasing in `t` and nonnegative when `t ≥ 0`. This is derived from Mathlib's
`L(Λ) = −ζ'/ζ` on `Re s > 1`, the termwise derivative of Dirichlet series and the Dirichlet
convolution identity `L(f)·L(g) = L(f ⍟ g)`. For `t ≥ 0`, the value bound
`|Φ_t(s)| ≤ Φ_t(Re s)` is proved. The real series `PhiR1` is defined for future
derivative estimates, but no bound for `|Φ_t'(s)|` is proved in this file.
-/

noncomputable section

namespace DBN.Zeta

open Complex LSeries
open scoped LSeries.notation

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- `A_t(n) = Λ(n) + (t/4)[Λ(n) log²n + log n · (Λ ∗ Λ)(n)]`. -/
def At (t : ℝ) (n : ℕ) : ℝ :=
  Λ n + t / 4 * (Λ n * Real.log n ^ 2 + Real.log n * (Λ * Λ) n)

theorem conv_nonneg (n : ℕ) : 0 ≤ (Λ * Λ) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun p _ =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg

theorem bracket_nonneg (n : ℕ) : 0 ≤ Λ n * Real.log n ^ 2 + Real.log n * (Λ * Λ) n := by
  have h0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have := conv_nonneg n
  have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  positivity

theorem At_nonneg {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : 0 ≤ At t n := by
  unfold At
  have := bracket_nonneg n
  have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  positivity

theorem At_mono {t t' : ℝ} (h : t ≤ t') (n : ℕ) : At t n ≤ At t' n := by
  unfold At
  have := bracket_nonneg n
  nlinarith

/-- `Φ_t(s) = −ζ'/ζ(s) − (t/4)(ζ''/ζ)'(s)`. -/
def Phi (t : ℝ) (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s -
    ((t : ℂ) / 4) * deriv (fun z => deriv (deriv riemannZeta) z / riemannZeta z) s

/-! ### L-series facts -/

theorem abscissa_vonMangoldt_le : abscissaOfAbsConv ↗Λ ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy)

theorem abscissa_vonMangoldt_lt {s : ℂ} (hs : 1 < s.re) : abscissaOfAbsConv ↗Λ < s.re :=
  lt_of_le_of_lt abscissa_vonMangoldt_le (by exact_mod_cast hs)

/-- `g = log·Λ + Λ ⍟ Λ`, the coefficients of `ζ''/ζ`. -/
def gcoef : ℕ → ℂ := fun n => logMul ↗Λ n + (↗Λ ⍟ ↗Λ) n

theorem gcoef_summable {s : ℂ} (hs : 1 < s.re) : LSeriesSummable gcoef s :=
  (LSeriesSummable_logMul_of_lt_re (abscissa_vonMangoldt_lt hs)).add
    ((ArithmeticFunction.LSeriesSummable_vonMangoldt hs).convolution
      (ArithmeticFunction.LSeriesSummable_vonMangoldt hs))

theorem abscissa_gcoef_lt {s : ℂ} (hs : 1 < s.re) : abscissaOfAbsConv gcoef < s.re :=
  lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    gcoef_summable (by simpa using hy)) (by exact_mod_cast hs)

/-- `ζ'/ζ = −L(Λ)` on `Re s > 1`. -/
theorem logDeriv_zeta_eq {s : ℂ} (hs : 1 < s.re) :
    deriv riemannZeta s / riemannZeta s = -LSeries ↗Λ s := by
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div, neg_neg]

theorem isOpen_halfPlane : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re

theorem zeta_analytic : AnalyticOnNhd ℂ riemannZeta {z : ℂ | 1 < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_halfPlane
  intro z hz
  exact (differentiableAt_riemannZeta (by intro h; rw [h] at hz; simp at hz)).differentiableWithinAt

/-- `ζ''/ζ = L(g)` on `Re s > 1`. -/
theorem zeta2_div_eq {s : ℂ} (hs : 1 < s.re) :
    deriv (deriv riemannZeta) s / riemannZeta s = LSeries gcoef s := by
  have hmem : {z : ℂ | 1 < z.re} ∈ nhds s := isOpen_halfPlane.mem_nhds hs
  have hEq : (fun z => deriv riemannZeta z / riemannZeta z) =ᶠ[nhds s] (fun z => -LSeries ↗Λ z) :=
    Filter.eventuallyEq_of_mem hmem fun z hz => logDeriv_zeta_eq hz
  have hd1 := hEq.deriv_eq
  have hLd : HasDerivAt (fun z => -LSeries ↗Λ z) (-(-LSeries (logMul ↗Λ) s)) s :=
    (LSeries_hasDerivAt (abscissa_vonMangoldt_lt hs)).neg
  rw [hLd.deriv, neg_neg] at hd1
  have hζ : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta (by intro h; rw [h] at hs; simp at hs)
  have hζ' : DifferentiableAt ℂ (deriv riemannZeta) s :=
    (zeta_analytic.deriv s hs).differentiableAt
  have hne := riemannZeta_ne_zero_of_one_lt_re hs
  have hq : deriv (fun z => deriv riemannZeta z / riemannZeta z) s =
      (deriv (deriv riemannZeta) s * riemannZeta s - deriv riemannZeta s * deriv riemannZeta s) /
        riemannZeta s ^ 2 :=
    (hζ'.hasDerivAt.div hζ.hasDerivAt hne).deriv
  rw [hq] at hd1
  -- `(ζ''ζ − ζ'ζ')/ζ² = L(log Λ)`; hence `ζ''/ζ = L(log Λ) + (ζ'/ζ)²`
  have hsq : deriv riemannZeta s / riemannZeta s * (deriv riemannZeta s / riemannZeta s) =
      LSeries (↗Λ ⍟ ↗Λ) s := by
    rw [logDeriv_zeta_eq hs, neg_mul_neg,
      ← LSeries_convolution' (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
        (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)]
  have hL : LSeries gcoef s = LSeries (logMul ↗Λ) s + LSeries (↗Λ ⍟ ↗Λ) s := by
    unfold gcoef
    exact LSeries_add (LSeriesSummable_logMul_of_lt_re (abscissa_vonMangoldt_lt hs))
      ((ArithmeticFunction.LSeriesSummable_vonMangoldt hs).convolution
        (ArithmeticFunction.LSeriesSummable_vonMangoldt hs))
  rw [hL, ← hd1, ← hsq]
  field_simp
  ring

/-- The coefficient identity `Λ + (t/4)·log·g = A_t`. -/
theorem coef_eq (t : ℝ) : (↗Λ + ((t : ℂ) / 4) • logMul gcoef) = fun n => (At t n : ℂ) := by
  funext n
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, gcoef, logMul, LSeries.convolution_def, At]
  rw [← Complex.natCast_log]
  have hconv : ((Λ * Λ) n : ℂ) =
      ∑ p ∈ n.divisorsAntidiagonal, ((Λ p.1 : ℝ) : ℂ) * ((Λ p.2 : ℝ) : ℂ) := by
    rw [ArithmeticFunction.mul_apply]; push_cast; rfl
  push_cast
  rw [hconv]
  ring

theorem summable_smul_logMul_gcoef {t : ℝ} {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (((t : ℂ) / 4) • logMul gcoef) s :=
  (LSeriesSummable_logMul_of_lt_re (abscissa_gcoef_lt hs)).smul _

/-- **`Φ_t = L(A_t)` on `Re s > 1`.** -/
theorem Phi_eq {t : ℝ} {s : ℂ} (hs : 1 < s.re) : Phi t s = LSeries (fun n => (At t n : ℂ)) s := by
  have hmem : {z : ℂ | 1 < z.re} ∈ nhds s := isOpen_halfPlane.mem_nhds hs
  have hEq : (fun z => deriv (deriv riemannZeta) z / riemannZeta z) =ᶠ[nhds s] LSeries gcoef :=
    Filter.eventuallyEq_of_mem hmem fun z hz => zeta2_div_eq hz
  unfold Phi
  rw [hEq.deriv_eq, LSeries_deriv (abscissa_gcoef_lt hs), neg_div, logDeriv_zeta_eq hs, neg_neg]
  have hsum1 := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hsum2 := summable_smul_logMul_gcoef (t := t) hs
  rw [show LSeries ↗Λ s - (t : ℂ) / 4 * -LSeries (logMul gcoef) s =
      LSeries ↗Λ s + LSeries (((t : ℂ) / 4) • logMul gcoef) s by rw [LSeries_smul]; ring,
    ← LSeries_add hsum1 hsum2, coef_eq]

/-- The real Dirichlet series `Φ_t(a) = Σ A_t(n) n^{−a}` for real `a`. -/
def PhiR (t a : ℝ) : ℝ := ∑' n : ℕ, At t n / (n : ℝ) ^ a

/-- The real series bounding `|Φ_t'|`. -/
def PhiR1 (t a : ℝ) : ℝ := ∑' n : ℕ, At t n * Real.log n / (n : ℝ) ^ a

theorem norm_term_At {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    ‖term (fun n => (At t n : ℂ)) s n‖ = At t n / (n : ℝ) ^ s.re := by
  rw [LSeries.norm_term_eq]
  split_ifs with h
  · subst h; simp [Real.zero_rpow (show s.re ≠ 0 by linarith)]
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (At_nonneg ht n)]

theorem summable_At {t : ℝ} {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (At t n : ℂ)) s := by
  rw [← coef_eq t]
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).add (summable_smul_logMul_gcoef hs)

/-- The real series `Σ A_t(n) n^{−a}` converges for `a > 1`. -/
theorem summable_real {t : ℝ} {a : ℝ} (ha : 1 < a) :
    Summable (fun n : ℕ => At t n / (n : ℝ) ^ a) := by
  have h1 : LSeriesSummable (fun n => (At t n : ℂ)) (a : ℂ) := summable_At (by simpa using ha)
  have e : ∀ n : ℕ, term (fun n => (At t n : ℂ)) (a : ℂ) n = ((At t n / (n : ℝ) ^ a : ℝ) : ℂ) := by
    intro n
    rw [LSeries.term_def]
    split_ifs with h
    · subst h; simp [Real.zero_rpow (show a ≠ 0 by linarith)]
    · rw [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  have : Summable (fun n : ℕ => ((At t n / (n : ℝ) ^ a : ℝ) : ℂ)) := h1.congr e
  exact Complex.summable_ofReal.mp this

/-- `|Φ_t(s)| ≤ Φ_t(Re s)`. -/
theorem norm_Phi_le {t : ℝ} (ht : 0 ≤ t) {s : ℂ} (hs : 1 < s.re) : ‖Phi t s‖ ≤ PhiR t s.re := by
  rw [Phi_eq hs, LSeries, PhiR]
  have hsum : Summable fun n => ‖term (fun n => (At t n : ℂ)) s n‖ :=
    (summable_real (t := t) hs).congr fun n => (norm_term_At ht hs n).symm
  calc ‖∑' n, term (fun n => (At t n : ℂ)) s n‖ ≤ ∑' n, ‖term (fun n => (At t n : ℂ)) s n‖ :=
        norm_tsum_le_tsum_norm hsum
    _ = ∑' n, At t n / (n : ℝ) ^ s.re := tsum_congr fun n => norm_term_At ht hs n

end DBN.Zeta
