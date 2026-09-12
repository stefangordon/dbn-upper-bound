import Mathlib

/-!
# The de Bruijn–Newman heat flow and the constant Λ

Normalization (Polymath 15): with
`Φ(u) = Σ_{n≥1} (2π²n⁴e^{9u} - 3πn²e^{5u}) exp(-πn²e^{4u})`,

  `H_t(z) = ∫_0^∞ e^{tu²} Φ(u) cos(zu) du`,  so `∂_t H_t = -∂_z² H_t` and
  `H_0(z) = ξ((1+iz)/2)/8`.

`Λ` is the infimum of the times `t` for which `H_t` has only real zeros.

This file also isolates the two literature facts used in the *last* step of the proof:
de Bruijn's strip contraction and boundedness below of the set of real-zero times.
Everything else (the barrier comparison) enters through the hypothesis of
`Lambda_le_of_barrier_terminal`.
-/

noncomputable section

open Real

namespace DBN

/-- `Φ(u) = Σ_{n ≥ 1} (2π² n⁴ e^{9u} − 3π n² e^{5u}) exp(−π n² e^{4u})`. -/
def Phi (u : ℝ) : ℝ :=
  ∑' n : ℕ, (2 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * rexp (9 * u) - 3 * π * ((n : ℝ) + 1) ^ 2 * rexp (5 * u))
      * rexp (-π * ((n : ℝ) + 1) ^ 2 * rexp (4 * u))

/-- `H_t(z) = ∫_0^∞ e^{t u²} Φ(u) cos(z u) du`. -/
def H (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ), ((rexp (t * u ^ 2) * Phi u : ℝ) : ℂ) * Complex.cos (z * u)

/-- `H_t` has only real zeros. -/
def RealZeros (t : ℝ) : Prop := ∀ z : ℂ, H t z = 0 → z.im = 0

def realZeroTimes : Set ℝ := {t | RealZeros t}

/-- The de Bruijn–Newman constant `Λ = inf { t | H_t has only real zeros }`. -/
def Lambda : ℝ := sInf realZeroTimes

/-- Every zero of `H_t` lies in the closed strip `|Im z| ≤ y`. -/
def ZerosInStrip (t y : ℝ) : Prop := ∀ z : ℂ, H t z = 0 → |z.im| ≤ y

/-- Literature premises used only in the final step.

* `deBruijn` — de Bruijn (1950), in this normalization: if the zeros of `H_t` lie in the strip
  `|Im z| ≤ y` then `H_{t + y²/2}` has only real zeros.
* `bddBelow` — the set of real-zero times is bounded below (Newman 1976 proved `Λ > -∞`;
  Rodgers–Tao 2018 proved `Λ ≥ 0`). This is only needed so that `sInf` is the honest infimum. -/
structure TailPremises : Prop where
  deBruijn : ∀ t y : ℝ, 0 ≤ y → ZerosInStrip t y → RealZeros (t + y ^ 2 / 2)
  bddBelow : BddBelow realZeroTimes

theorem Lambda_le_of_realZeros (P : TailPremises) {t : ℝ} (h : RealZeros t) : Lambda ≤ t :=
  csInf_le P.bddBelow h

theorem Lambda_le_of_strip (P : TailPremises) {t y : ℝ} (hy : 0 ≤ y) (h : ZerosInStrip t y) :
    Lambda ≤ t + y ^ 2 / 2 :=
  Lambda_le_of_realZeros P (P.deBruijn t y hy h)

/-- A strict squared-height bound `Im(ρ)² < q` at time `t` puts all zeros in the strip `|Im| ≤ √q`. -/
theorem zerosInStrip_of_sq_lt {t q : ℝ} (hq : 0 ≤ q)
    (h : ∀ z : ℂ, H t z = 0 → z.im ^ 2 < q) : ZerosInStrip t (Real.sqrt q) := by
  intro z hz
  have h1 := h z hz
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h1.le

/-- **Final step.** If every zero of `H_T` satisfies `Im(ρ)² < 1/400`, then `Λ ≤ T + 1/800`. -/
theorem Lambda_le_of_barrier_terminal (P : TailPremises) {T : ℝ}
    (hT : ∀ z : ℂ, H T z = 0 → z.im ^ 2 < 1 / 400) : Lambda ≤ T + 1 / 800 := by
  have hs := zerosInStrip_of_sq_lt (by norm_num) hT
  have := Lambda_le_of_strip P (Real.sqrt_nonneg _) hs
  rwa [Real.sq_sqrt (by norm_num), show (1 / 400 : ℝ) / 2 = 1 / 800 by norm_num] at this

end DBN
