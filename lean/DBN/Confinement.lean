import DBN.External

/-!
# The positive-time confinement interface

`PolymathPositiveTimeRealTail` is the real-zero conclusion of Polymath,
*Effective approximation of heat flow evolution of the Riemann xi function,
and a new upper bound for the de Bruijn–Newman constant*, arXiv:1904.12438v2,
Theorem 1.5(i), in the normalization `H₀(z) = ξ((1+iz)/2)/8`.

The literature theorem itself is **not formalized here**. It is an explicit
proposition parameter, never an axiom. The theorem below proves its exact
consequence needed for first-contact compactness, using the proved evenness
of the concrete heat flow.
-/

namespace DBN

open Set

/-- The real-zero tail conclusion of Polymath, arXiv:1904.12438v2, Theorem 1.5(i).
The additional asymptotic description of real zeros in that theorem is unused. -/
def PolymathPositiveTimeRealTail : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ioc (0 : ℝ) (1 / 2), ∀ z : ℂ,
    H t z = 0 → Real.exp (C / t) ≤ z.re → z.im = 0

/-- A common finite bound on every nonreal zero on a compact positive-time
interval follows from the literature tail proposition. The witness is
`R = exp (C / t0)`; evenness supplies the negative-real-part half-plane. -/
theorem confinement_of_polymathPositiveTimeRealTail
    (hP : PolymathPositiveTimeRealTail) {t0 T η : ℝ}
    (ht0 : 0 < t0) (hT : T ≤ 1 / 2) (hη : 0 < η) :
    ∃ R : ℝ, ∀ t ∈ Icc t0 T, ∀ z : ℂ,
      H t z = 0 → η ≤ |z.im| → |z.re| ≤ R := by
  obtain ⟨C, hC, htail⟩ := hP
  refine ⟨Real.exp (C / t0), ?_⟩
  intro t ht z hz hzim
  by_contra hbound
  have hlarge : Real.exp (C / t0) < |z.re| := lt_of_not_ge hbound
  have ht' : t ∈ Ioc (0 : ℝ) (1 / 2) :=
    ⟨lt_of_lt_of_le ht0 ht.1, le_trans ht.2 hT⟩
  have hthreshold : Real.exp (C / t) ≤ Real.exp (C / t0) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hC.le ht0 ht.1)
  have him : z.im = 0 := by
    by_cases hre : 0 ≤ z.re
    · apply htail t ht' z hz
      simpa only [abs_of_nonneg hre] using le_trans hthreshold hlarge.le
    · have hneg : H t (-z) = 0 := (symm_all t z hz).1
      have hreal : (-z).im = 0 := htail t ht' (-z) hneg (by
        simpa only [Complex.neg_re, abs_of_neg (lt_of_not_ge hre)] using
          le_trans hthreshold hlarge.le)
      simpa only [Complex.neg_im, neg_eq_zero] using hreal
  rw [him, abs_zero] at hzim
  exact (not_le_of_gt hη) hzim

end DBN
