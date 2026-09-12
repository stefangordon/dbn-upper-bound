import Mathlib
import DBN.Heat

/-!
# Identification of `H₀` with the Riemann ξ function (obligation B.9)

`H_t` is *defined* in `DBN.Heat` by the integral `∫₀^∞ e^{tu²} Φ(u) cos(zu) du`, which is all that
the statement `Λ ≤ bound` needs. Connecting `Λ` to the Riemann Hypothesis requires Riemann's identity
`H₀(z) = ξ((1+iz)/2)/8`. We use the entire form `ξ(s) = (s(s−1)Λ₀(s) + 1)/2` with
`Λ₀ = completedRiemannZeta₀` (Mathlib's entire completed zeta), which agrees with the classical
`½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)` for `s ≠ 0, 1` (`xi_eq_classical`). The identity itself is proved in
`DBN.External` from `LeanCert.Analysis.DBN.H_zero_eq_riemannXi`.
-/

noncomputable section

namespace DBN

open Complex

/-- Riemann's `ξ`, entire form: `ξ(s) = (s (s − 1) Λ₀(s) + 1)/2`. -/
def xi (s : ℂ) : ℂ := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- Off `s = 0, 1` this is the classical `½ s (s−1) completedRiemannZeta s`. -/
theorem xi_eq_classical {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  rw [xi, completedRiemannZeta_eq]
  have h : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

/-- **Statement B.9.** `H₀(z) = ξ((1 + iz)/2) / 8` for all `z`. -/
def H0_eq_xi : Prop := ∀ z : ℂ, H 0 z = xi ((1 + I * z) / 2) / 8

/-- The zeros of `H₀` are the images `z = −i(2s − 1)` of the zeros `s` of `ξ`; RH says they are real. -/
theorem realZeros_zero_iff_of_H0_eq_xi (hid : H0_eq_xi) :
    RealZeros 0 ↔ ∀ s : ℂ, xi s = 0 → s.re = 1 / 2 := by
  constructor
  · intro hR s hs
    have hz : H 0 ((2 * s - 1) / I) = 0 := by
      rw [hid]
      have : (1 + I * ((2 * s - 1) / I)) / 2 = s := by
        field_simp
        ring
      rw [this, hs]; simp
    have := hR _ hz
    have e : ((2 * s - 1) / I).im = -(2 * s.re - 1) := by
      rw [div_I]; simp
    rw [e] at this
    linarith
  · intro hX z hz
    have hs : xi ((1 + I * z) / 2) = 0 := by
      rw [hid] at hz
      simpa using hz
    have := hX _ hs
    simp only [div_ofNat_re, add_re, one_re, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub] at this
    linarith

end DBN

end
