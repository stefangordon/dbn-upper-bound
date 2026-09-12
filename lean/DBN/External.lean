import Mathlib
import LeanCert.Analysis.DBN.HeatFlow
import LeanCert.Analysis.DBN.HeatSymmetry
import LeanCert.Analysis.DBN.HeatRegularity
import LeanCert.Analysis.DBN.ForwardPreservation
import LeanCert.Analysis.DBN.XiIdentity
import LeanCert.Analysis.DBN.BadTime
import LeanCert.Analysis.DBN.Threshold
import DBN.Heat
import DBN.Premises
import DBN.Identification

/-!
# Bridge to `LeanCert.Analysis.DBN` (alerad/leancert, Apache-2.0)

leancert's `Analysis/DBN` library defines the heat flow `H_t` by the same integral as `DBN.Heat`
(same `Φ`, same integrand), so the two definitions are definitionally equal (`H_eq`). From its theorems
we discharge:

* `TailPremises` — de Bruijn's strip contraction (`H_forward_strip`) and `Λ > −∞`
  (`realZeroTimes_bddBelow`);
* the fields `strip`, `symm`, `closed` of `AnalyticPremises`;
* the identification `H₀ = ξ((1+iz)/2)/8` (`H_zero_eq_riemannXi`), hence `RH ↔ RealZeros 0`.

Nothing here is assumed; every statement is a theorem of leancert or Mathlib.
-/

noncomputable section

namespace DBN

open Set

theorem Phi_eq : DBN.Phi = LeanCert.Analysis.DBN.Phi := by
  funext u
  rfl

theorem H_eq : DBN.H = LeanCert.Analysis.DBN.H := by
  funext t z
  unfold DBN.H LeanCert.Analysis.DBN.H LeanCert.Analysis.DBN.heatIntegrand
  rw [Phi_eq]

theorem H_eq_apply (t : ℝ) (z : ℂ) : H t z = LeanCert.Analysis.DBN.H t z := by rw [H_eq]

theorem realZeroTimes_eq : DBN.realZeroTimes = LeanCert.Analysis.DBN.realZeroTimes := by
  unfold DBN.realZeroTimes DBN.RealZeros LeanCert.Analysis.DBN.realZeroTimes
  rw [H_eq]

theorem Lambda_eq : DBN.Lambda = LeanCert.Analysis.DBN.Lambda := by
  unfold DBN.Lambda LeanCert.Analysis.DBN.Lambda
  rw [realZeroTimes_eq]

/-- de Bruijn's strip contraction in our normalization, from `LeanCert.Analysis.DBN.H_forward_strip`. -/
theorem deBruijn_strip (t y : ℝ) (_hy : 0 ≤ y) (h : ZerosInStrip t y) : RealZeros (t + y ^ 2 / 2) := by
  intro z hz
  have hstrip : ∀ w : ℂ, LeanCert.Analysis.DBN.H t w = 0 → w.im ^ 2 ≤ y ^ 2 := by
    intro w hw
    have h1 : |w.im| ≤ y := h w (by rw [H_eq]; exact hw)
    have h2 : |w.im| ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rwa [sq_abs] at h2
  have hz' : LeanCert.Analysis.DBN.H (t + y ^ 2 / 2) z = 0 := by rw [← H_eq]; exact hz
  have h3 := LeanCert.Analysis.DBN.H_forward_strip t y (y ^ 2 / 2) (by positivity) hstrip hz'
  have e : y ^ 2 - 2 * (y ^ 2 / 2) = 0 := by ring
  rw [e, max_self] at h3
  nlinarith [sq_nonneg z.im]

/-- **The tail premises are theorems.** -/
theorem tailPremises : TailPremises where
  deBruijn := deBruijn_strip
  bddBelow := by rw [realZeroTimes_eq]; exact LeanCert.Analysis.DBN.realZeroTimes_bddBelow

/-- Global strip: every zero of `H_t`, `t ≥ 0`, has `|Im| ≤ 1`. -/
theorem strip_all (t : ℝ) (ht : 0 ≤ t) (z : ℂ) (hz : H t z = 0) : |z.im| ≤ 1 := by
  have h0 : ∀ w : ℂ, LeanCert.Analysis.DBN.H 0 w = 0 → w.im ^ 2 ≤ (1 : ℝ) ^ 2 := by
    intro w hw
    have h1 := LeanCert.Analysis.DBN.H_zero_strip hw
    have h2 : |w.im| ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rwa [sq_abs] at h2
  have hz' : LeanCert.Analysis.DBN.H (0 + t) z = 0 := by rw [zero_add, ← H_eq]; exact hz
  have h3 := LeanCert.Analysis.DBN.H_forward_strip 0 1 t ht h0 hz'
  have h4 : z.im ^ 2 ≤ 1 := le_trans h3 (max_le (by nlinarith) zero_le_one)
  exact (sq_le_one_iff_abs_le_one z.im).mp h4

/-- Evenness and reality of `H_t`: zeros come with `−z` and `conj z`. -/
theorem symm_all (t : ℝ) (z : ℂ) (hz : H t z = 0) : H t (-z) = 0 ∧ H t (starRingEnd ℂ z) = 0 := by
  rw [H_eq] at hz ⊢
  refine ⟨?_, ?_⟩
  · rw [LeanCert.Analysis.DBN.H_even]; exact hz
  · rw [LeanCert.Analysis.DBN.H_conj, hz, map_zero]

theorem continuous_H : Continuous (fun p : ℝ × ℂ => H p.1 p.2) := by
  rw [H_eq]; exact LeanCert.Analysis.DBN.continuous_H

/-- The zero set over a compact time interval is closed. -/
theorem closed_zeros (t0 T : ℝ) : IsClosed {p : ℝ × ℂ | p.1 ∈ Icc t0 T ∧ H p.1 p.2 = 0} := by
  have e : {p : ℝ × ℂ | p.1 ∈ Icc t0 T ∧ H p.1 p.2 = 0}
      = (Icc t0 T ×ˢ (univ : Set ℂ)) ∩ ((fun p : ℝ × ℂ => H p.1 p.2) ⁻¹' {0}) := by
    ext p; simp [Set.mem_prod]
  rw [e]
  exact (isClosed_Icc.prod isClosed_univ).inter (isClosed_singleton.preimage continuous_H)

/-- `H₀(z) = ξ((1+iz)/2)/8`, from leancert's theta–Mellin computation. -/
theorem h0_eq_xi : H0_eq_xi := by
  intro z
  rw [H_eq_apply, LeanCert.Analysis.DBN.H_zero_eq_riemannXi]
  have e : (1 + Complex.I * z) / 2 = 1 / 2 + Complex.I * z / 2 := by ring
  rw [e]
  rfl

/-- RH is equivalent to all zeros of `H₀` being real. -/
theorem realZeros_zero_iff_RH : RealZeros 0 ↔ ∀ s : ℂ, xi s = 0 → s.re = 1 / 2 :=
  realZeros_zero_iff_of_H0_eq_xi h0_eq_xi

/-- de Bruijn's bound `Λ ≤ 1/2`, from leancert. -/
theorem Lambda_le_half : Lambda ≤ 1 / 2 := by
  rw [Lambda_eq]; exact LeanCert.Analysis.DBN.Lambda_le_half

end DBN

end
