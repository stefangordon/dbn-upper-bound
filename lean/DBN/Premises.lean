import Mathlib
import DBN.Heat
import DBN.Barrier
import DBN.Data.Wall
import DBN.Data.Catalog

/-!
# Analytic premises (manuscript §4), stated exactly over the concrete `H`

Everything the barrier argument uses from analysis is collected here as `Prop`-valued structure
fields; they are the hypotheses of the formal barrier theorem in `DBN.FirstContact`. Several are now
theorems: `strip`, `symm`, `closed` (`DBN.External`, from leancert), `omegaGap` (`DBN.OmegaGap`), and
`dynamics` (`DBN.ZeroBranch` + `DBN.Hermite` + `DBN.PairSum`, see `DBN.zeroDynamics_proved`). The
written proofs of the rest (`confine`, `head`, `sourceFloor`, `fieldFloor`) are in the publication's
`manuscript/` supplements; `DEPENDENCIES.md` records the exact interfaces.

Notation: `S x Y t = −Im(H_t'/H_t)(x+iY)`, `SY = ∂_Y S = −Re(u_z)` with `u = H_t'/H_t`,
`Ω(x) = log(x/(4π))/4`, `J = |u_z| + (Re u + π/8)² + (S − Ω)²`,
`V x h t = (15/14)S(x,3h,t) − (16/21)S(x,4h,t) + (1/6)S(x,5h,t)`.
-/

noncomputable section

namespace DBN

open Real Set

/-- Logarithmic derivative `u = H_t'/H_t` at `x + iY`. -/
def u (x Y t : ℝ) : ℂ := deriv (H t) (x + Y * Complex.I) / H t (x + Y * Complex.I)
/-- `u_z = (H_t'/H_t)' = H''/H − (H'/H)²`. -/
def uz (x Y t : ℝ) : ℂ :=
  deriv (deriv (H t)) (x + Y * Complex.I) / H t (x + Y * Complex.I) - (u x Y t) ^ 2
/-- Density `S = −Im u`. -/
def S (x Y t : ℝ) : ℝ := -(u x Y t).im
/-- `S_Y = ∂_Y S = −Re u_z`. -/
def SY (x Y t : ℝ) : ℝ := -(uz x Y t).re
/-- `Ω(x) = log(x/(4π))/4`. -/
def Omega (x : ℝ) : ℝ := Real.log (x / (4 * π)) / 4
/-- Jet functional. -/
def J (x Y t : ℝ) : ℝ := ‖uz x Y t‖ + ((u x Y t).re + π / 8) ^ 2 + (S x Y t - Omega x) ^ 2
/-- Three-probe observable. -/
def V (x h t : ℝ) : ℝ := 15 / 14 * S x (3 * h) t - 16 / 21 * S x (4 * h) t + 1 / 6 * S x (5 * h) t

/-- View a reference cell as a (certificate-free) row. -/
def Seg.toRow (s : Seg) : Row := ⟨s.tl, s.tr, s.qL, s.qR, Cert.source default⟩

/-- The M3a wall `q_M` as a real function (piecewise affine on its 1620 cells). -/
def qM (t : ℝ) : ℝ := Q (Data.wall.toList.map Seg.toRow) t

/-- The source-law velocity bound at a highest simple zero `x + ih`: `q' ≤ −2/15 − 4h V`. -/
def SourceForce (x h t v : ℝ) : Prop := v ≤ -2 / 15 - 4 * h * V x h t

/-- Unsigned field-law velocity bound at probe `p` (requires `p² ≥ 5h²`, `H_t(x+ip) ≠ 0`). -/
def UnsignedForce (x h t v : ℝ) : Prop :=
  ∀ p : ℝ, 5 * h ^ 2 ≤ p ^ 2 → H t (x + p * Complex.I) ≠ 0 →
    v ≤ -2 - 4 * h ^ 2 * S x p t / p + 8 * h ^ 2 / (p ^ 2 - h ^ 2)

/-- Signed field-law velocity bound at probe `p` (requires `p² ≥ 9h²`):
`q' ≤ −2 − 4hα D + 16q/(p²−q)`, `α = h(3p²−q)/(2p³)`, `D = S − a S_Y`, `a = p(p²−q)/(3p²−q)`. -/
def SignedForce (x h t v : ℝ) : Prop :=
  ∀ p : ℝ, 9 * h ^ 2 ≤ p ^ 2 → H t (x + p * Complex.I) ≠ 0 →
    v ≤ -2 - 4 * h * (h * (3 * p ^ 2 - h ^ 2) / (2 * p ^ 3)) *
          (S x p t - (p * (p ^ 2 - h ^ 2) / (3 * p ^ 2 - h ^ 2)) * SY x p t)
        + 16 * h ^ 2 / (p ^ 2 - h ^ 2)

/-- **Zero dynamics at a highest zero** (P1 + P6 + backward Hermite splitting).
If `ρ = x + ih` is a zero of `H_{t₁}` of maximal imaginary part with `x > X`, `h > 0`, then either
(multiple zero) for all small `ε` there is a zero of `H_{t₁−ε}` at height `≥ h + c√ε − Cε`, or
(simple zero) there is a left zero-branch `γ` through `ρ` whose squared height has a left
derivative `v` obeying the source law and both field laws.

`DBN.ZeroBranch.zeroDynamics_of` proves this from `HermiteSplit` (the multiple-zero case) and
`PairSumForce` (the three laws for the exact velocity `zeroVel = 2 Im ρ · Im(H''/H')(ρ)`); the branch
`γ` and its velocity are theorems (`DBN.ZeroBranch.zero_branch`), and so are `HermiteSplit`
(`DBN.hermiteSplit_proved`) and `PairSumForce` (`DBN.pairSumForce_proved`). -/
def ZeroDynamics (t0 T : ℝ) : Prop :=
  ∀ t1 ∈ Ioc t0 T, ∀ ρ : ℂ, H t1 ρ = 0 → (Const.X : ℝ) < ρ.re → 0 < ρ.im →
    (∀ z : ℂ, H t1 z = 0 → z.im ≤ ρ.im) →
    (∃ c > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ ε0 > (0 : ℝ), ∀ ε ∈ Ioo (0 : ℝ) ε0,
        ∃ z : ℂ, H (t1 - ε) z = 0 ∧ ρ.im + c * Real.sqrt ε - C * ε ≤ z.im) ∨
    (∃ ε0 > (0 : ℝ), ∃ γ : ℝ → ℂ, γ t1 = ρ ∧ (∀ s ∈ Icc (t1 - ε0) t1, H s (γ s) = 0) ∧
        ContinuousOn γ (Icc (t1 - ε0) t1) ∧
        ∃ v : ℝ, HasDerivWithinAt (fun s => (γ s).im ^ 2) v (Iic t1) t1 ∧
          SourceForce ρ.re ρ.im t1 v ∧ UnsignedForce ρ.re ρ.im t1 v ∧ SignedForce ρ.re ρ.im t1 v)

/-- All analytic inputs of the barrier comparison for the barrier `Q l` of a row list `l` on `[t0, T]`. -/
structure AnalyticPremises (t0 T : ℝ) (l : List Row) : Prop where
  /-- P1: global strip `|Im ρ| ≤ 1` for `t ≥ 0`. -/
  strip : ∀ t : ℝ, 0 ≤ t → ∀ z : ℂ, H t z = 0 → |z.im| ≤ 1
  /-- P1: `H_t` is even and real on the real axis, so zeros come with `−z` and `conj z`. -/
  symm : ∀ t : ℝ, ∀ z : ℂ, H t z = 0 → H t (-z) = 0 ∧ H t (starRingEnd ℂ z) = 0
  /-- Joint continuity: the zero set in `[t0,T] × ℂ` is closed. -/
  closed : IsClosed {p : ℝ × ℂ | p.1 ∈ Icc t0 T ∧ H p.1 p.2 = 0}
  /-- P3 (positive-time confinement): zeros of height `≥ 1/40` have bounded real part on `[t0,T]`. -/
  confine : ∃ R : ℝ, ∀ t ∈ Icc t0 T, ∀ z : ℂ, H t z = 0 → 1 / 40 ≤ |z.im| → |z.re| ≤ R
  /-- P2 (finite head H4): zeros with `|Re z| ≤ X` are real for `t ∈ [0, 1/5]`. -/
  head : ∀ t ∈ Icc (0 : ℝ) (1 / 5), ∀ z : ℂ, H t z = 0 → |z.re| ≤ Const.X → z.im = 0
  /-- Strict entry at `t0`. -/
  entry : ∀ z : ℂ, H t0 z = 0 → z.im ^ 2 < Q l t0
  /-- Zero dynamics (P1 + P6 + backward Hermite). -/
  dynamics : ZeroDynamics t0 T
  /-- P7: source floors on the boxes used by the rows, for all `x ≥ X`. -/
  sourceFloor : ∀ r ∈ l, ∀ c : SourceCert, r.cert = .source c → ∀ x : ℝ, (Const.X : ℝ) ≤ x →
    ∀ t ∈ Icc (c.btl : ℝ) c.btr, ∀ h ∈ Icc (c.hlo : ℝ) c.hhi, (c.L : ℝ) ≤ V x h t
  /-- P4 + P5 + P8: field floors on the old cells of the rows: for all `x ≥ X` and `t` in the old cell,
  `H_t(x+ip) ≠ 0`, `S > s`, and in signed mode `J ≤ c`. -/
  fieldFloor : ∀ r ∈ l, ∀ c : FieldCert, r.cert = .field c →
    ∀ x : ℝ, (Const.X : ℝ) ≤ x → ∀ t ∈ Icc (c.otl : ℝ) c.otr,
      H t (x + (c.p : ℝ) * Complex.I) ≠ 0 ∧ (c.s : ℝ) < S x c.p t ∧
      (c.signed = true → J x c.p t ≤ c.c)
  /-- `Ω(x) > Ω_L` for `x ≥ X` (a theorem: `DBN.OmegaGap.omegaGap_proved`). -/
  omegaGap : ∀ x : ℝ, (Const.X : ℝ) ≤ x → (Const.OmegaL : ℝ) < Omega x

end DBN
