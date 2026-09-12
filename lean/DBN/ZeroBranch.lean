import Mathlib
import DBN.Premises
import DBN.External

/-!
# The simple-zero branch and the decomposition of the zero dynamics

At a *simple* zero `ρ` of `H_{t₁}` (`H_{t₁}'(ρ) ≠ 0`) the implicit function theorem applied to
`(t, z) ↦ H_t(z)` gives a differentiable zero branch `γ` through `ρ` with
`γ'(t₁) = −∂_tH/∂_zH = H_{t₁}''(ρ)/H_{t₁}'(ρ)`, since `∂_t H = −∂_z² H`. Hence the squared height along
the branch has derivative `zeroVel t₁ ρ = 2 Im ρ · Im(H''/H')(ρ)`.

This file proves that branch (`zero_branch`) from leancert's partial derivatives of `H` and Mathlib's
bivariate implicit function theorem, and splits the zero-dynamics statement `ZeroDynamics` into the two
analytic inputs (both proved later, in `DBN.Hermite` and `DBN.PairSum`)

* `HermiteSplit`: backward Hermite splitting at a *multiple* highest zero;
* `PairSumForce`: the three force laws (source, unsigned field, signed field) for the exact velocity
  `zeroVel` at a *simple* highest zero (P6 + the pair-sum evaluation of `H''/H'`).

`zeroDynamics_of` recombines them.
-/

noncomputable section

namespace DBN

open Set Filter Topology
open LeanCert.Analysis.DBN (moment continuous_moment hasDerivAt_H_z hasDerivAt_H_t deriv_H_z deriv2_H_z)

/-! ### Continuity of the implicit function near the base point -/

section ImplicitContinuity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- The implicit function of `HasStrictFDerivAt.implicitFunctionOfProdDomain` is continuous on a
neighbourhood of the base point (it is a slice of the inverse of an open partial homeomorphism). -/
theorem eventually_continuousAt_implicitFunctionOfProdDomain
    {u : E₁ × E₂} {f : E₁ × E₂ → F} {f'u : E₁ × E₂ →L[𝕜] F}
    (dfu : HasStrictFDerivAt f f'u u) (if₂u : (f'u ∘L .inr 𝕜 E₁ E₂).IsInvertible) :
    ∀ᶠ x in 𝓝 u.1, ContinuousAt (dfu.implicitFunctionOfProdDomain if₂u) x := by
  set φ := dfu.implicitFunctionDataOfProdDomain if₂u with hφ
  have hmem : (f u, u.1) ∈ φ.toOpenPartialHomeomorph.target :=
    φ.map_pt_mem_toOpenPartialHomeomorph_target
  have hopen : φ.toOpenPartialHomeomorph.target ∈ 𝓝 (f u, u.1) :=
    φ.toOpenPartialHomeomorph.open_target.mem_nhds hmem
  have hc : Continuous (fun x : E₁ => (f u, x)) := continuous_const.prodMk continuous_id
  have hpre : (fun x : E₁ => (f u, x)) ⁻¹' φ.toOpenPartialHomeomorph.target ∈ 𝓝 u.1 :=
    hc.continuousAt.preimage_mem_nhds hopen
  filter_upwards [hpre] with x hx
  rw [HasStrictFDerivAt.implicitFunctionOfProdDomain_def]
  apply continuous_snd.continuousAt.comp
  show ContinuousAt (fun x => φ.toOpenPartialHomeomorph.symm (f u, x)) x
  exact (φ.toOpenPartialHomeomorph.continuousAt_symm hx).comp hc.continuousAt

variable [IsRCLikeNormedField 𝕜] {u : E₁ × E₂}
  {f : E₁ → E₂ → F} {f₁ : E₁ → E₂ → E₁ →L[𝕜] F} {f₂ : E₁ → E₂ → E₂ →L[𝕜] F}
  (df₁ : ∀ᶠ v in 𝓝 u, HasFDerivAt (f · v.2) (f₁ v.1 v.2) v.1)
  (df₂ : ∀ᶠ v in 𝓝 u, HasFDerivAt (f v.1 ·) (f₂ v.1 v.2) v.2)
  (cf₁ : ContinuousAt ↿f₁ u) (cf₂ : ContinuousAt ↿f₂ u) (if₂u : (f₂ u.1 u.2).IsInvertible)

theorem eventually_continuousAt_implicitFunctionOfBivariate :
    ∀ᶠ x in 𝓝 u.1, ContinuousAt (implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u) x := by
  rw [implicitFunctionOfBivariate_def]
  exact eventually_continuousAt_implicitFunctionOfProdDomain _ _

end ImplicitContinuity

/-! ### Partial derivatives of `H` as real-linear maps -/

/-- `∂_t H` at `(t, z)` as a real-linear map `ℝ →L[ℝ] ℂ`: `s ↦ s · (−moment 2 t z)`. -/
def dT (t : ℝ) (z : ℂ) : ℝ →L[ℝ] ℂ :=
  (1 : ℝ →L[ℝ] ℝ).smulRight (-moment 2 t z)

/-- `∂_z H` at `(t, z)` as a real-linear map `ℂ →L[ℝ] ℂ`: multiplication by `moment 1 t z = H_t'(z)`. -/
def dZ (t : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (moment 1 t z) • ContinuousLinearMap.id ℝ ℂ

theorem dT_apply (t : ℝ) (z : ℂ) (s : ℝ) : dT t z s = s • (-moment 2 t z) := rfl
theorem dZ_apply (t : ℝ) (z w : ℂ) : dZ t z w = moment 1 t z * w := rfl

theorem hasFDerivAt_H_t (t : ℝ) (z : ℂ) : HasFDerivAt (fun s : ℝ => H s z) (dT t z) t := by
  rw [H_eq]; exact (hasDerivAt_H_t t z).hasFDerivAt

theorem hasFDerivAt_H_z (t : ℝ) (z : ℂ) : HasFDerivAt (H t) (dZ t z) z := by
  rw [H_eq]
  refine ((hasDerivAt_H_z t z).hasFDerivAt.restrictScalars ℝ).congr_fderiv ?_
  ext w
  simp [dZ, mul_comm]

theorem continuous_dT : Continuous (fun p : ℝ × ℂ => dT p.1 p.2) := by
  have h : (fun p : ℝ × ℂ => dT p.1 p.2) =
      (ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1 : ℝ →L[ℝ] ℝ)) ∘ (fun p : ℝ × ℂ => -moment 2 p.1 p.2) := by
    funext p; refine ContinuousLinearMap.ext fun s => ?_; simp [dT]
  rw [h]
  exact (ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1 : ℝ →L[ℝ] ℝ)).continuous.comp (continuous_moment 2).neg

theorem continuous_dZ : Continuous (fun p : ℝ × ℂ => dZ p.1 p.2) := by
  unfold dZ
  exact (continuous_moment 1).smul continuous_const

/-! ### The zero branch through a simple zero -/

/-- **Simple-zero branch.** If `H_{t₁}(ρ) = 0` and `H_{t₁}'(ρ) ≠ 0`, there is a zero branch `γ` through
`ρ`, continuous near `t₁`, with `γ'(t₁) = H_{t₁}''(ρ)/H_{t₁}'(ρ)`. -/
theorem zero_branch {t1 : ℝ} {ρ : ℂ} (h0 : H t1 ρ = 0) (hd : deriv (H t1) ρ ≠ 0) :
    ∃ γ : ℝ → ℂ, γ t1 = ρ ∧ (∀ᶠ s in 𝓝 t1, H s (γ s) = 0 ∧ ContinuousAt γ s) ∧
      HasDerivAt γ (deriv (deriv (H t1)) ρ / deriv (H t1) ρ) t1 := by
  have hm1 : moment 1 t1 ρ ≠ 0 := by rwa [H_eq, deriv_H_z] at hd
  have df₁ : ∀ᶠ v in 𝓝 ((t1, ρ) : ℝ × ℂ), HasFDerivAt (fun t => H t v.2) (dT v.1 v.2) v.1 :=
    Eventually.of_forall fun v => hasFDerivAt_H_t v.1 v.2
  have df₂ : ∀ᶠ v in 𝓝 ((t1, ρ) : ℝ × ℂ), HasFDerivAt (fun z => H v.1 z) (dZ v.1 v.2) v.2 :=
    Eventually.of_forall fun v => hasFDerivAt_H_z v.1 v.2
  have cf₁ : ContinuousAt (↿dT) ((t1, ρ) : ℝ × ℂ) := continuous_dT.continuousAt
  have cf₂ : ContinuousAt (↿dZ) ((t1, ρ) : ℝ × ℂ) := continuous_dZ.continuousAt
  let e : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.equivOfInverse (dZ t1 ρ)
    ((moment 1 t1 ρ)⁻¹ • ContinuousLinearMap.id ℝ ℂ)
    (fun w => by simp [dZ, hm1]) (fun w => by simp [dZ, hm1])
  have if₂u : (dZ t1 ρ).IsInvertible := ⟨e, by ext w; rfl⟩
  refine ⟨implicitFunctionOfBivariate (f := H) (f₁ := dT) (f₂ := dZ) df₁ df₂ cf₁ cf₂ if₂u, ?_, ?_, ?_⟩
  · exact ((eventually_apply_eq_iff_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u).self_of_nhds).mp rfl
  · have hz := eventually_apply_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u
    have hc := eventually_continuousAt_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u
    filter_upwards [hz, hc] with x hx hcx
    exact ⟨by rw [hx, h0], hcx⟩
  · have hs := hasStrictFDerivAt_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u
    refine hs.hasFDerivAt.hasDerivAt.congr_deriv ?_
    rw [H_eq, deriv2_H_z, deriv_H_z]
    have hinv : (dZ t1 ρ).inverse (-moment 2 t1 ρ) = -(moment 2 t1 ρ / moment 1 t1 ρ) := by
      rw [if₂u.inverse_apply_eq, dZ_apply]
      field_simp
    simp only [neg_apply, ContinuousLinearMap.comp_apply, dT_apply, one_smul]
    rw [hinv, neg_neg]

/-! ### The decomposition of the zero dynamics -/

/-- Backward Hermite splitting at a *multiple* highest zero: for all small `ε` there is a zero of
`H_{t₁−ε}` at height `≥ Im ρ + c√ε − Cε`. -/
def HermiteSplit (t0 T : ℝ) : Prop :=
  ∀ t1 ∈ Ioc t0 T, ∀ ρ : ℂ, H t1 ρ = 0 → (Const.X : ℝ) < ρ.re → 0 < ρ.im →
    (∀ z : ℂ, H t1 z = 0 → z.im ≤ ρ.im) → deriv (H t1) ρ = 0 →
    ∃ c > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∃ ε0 > (0 : ℝ), ∀ ε ∈ Ioo (0 : ℝ) ε0,
      ∃ z : ℂ, H (t1 - ε) z = 0 ∧ ρ.im + c * Real.sqrt ε - C * ε ≤ z.im

/-- The exact velocity of `Im(ρ)²` along the simple-zero branch through `ρ`:
`2 Im ρ · Im(H_t''/H_t')(ρ)`. -/
def zeroVel (t : ℝ) (ρ : ℂ) : ℝ := 2 * ρ.im * (deriv (deriv (H t)) ρ / deriv (H t) ρ).im

/-- P6: the source law and both field laws hold for the exact velocity `zeroVel` at a *simple* highest
zero with `Re ρ > X`. -/
def PairSumForce (t0 T : ℝ) : Prop :=
  ∀ t1 ∈ Ioc t0 T, ∀ ρ : ℂ, H t1 ρ = 0 → (Const.X : ℝ) < ρ.re → 0 < ρ.im →
    (∀ z : ℂ, H t1 z = 0 → z.im ≤ ρ.im) → deriv (H t1) ρ ≠ 0 →
    SourceForce ρ.re ρ.im t1 (zeroVel t1 ρ) ∧ UnsignedForce ρ.re ρ.im t1 (zeroVel t1 ρ) ∧
      SignedForce ρ.re ρ.im t1 (zeroVel t1 ρ)

/-- The squared height along the branch has derivative `zeroVel t1 ρ` at `t1`. -/
theorem hasDerivAt_im_sq_branch {t1 : ℝ} {ρ : ℂ} {γ : ℝ → ℂ} (hγ0 : γ t1 = ρ)
    (hγd : HasDerivAt γ (deriv (deriv (H t1)) ρ / deriv (H t1) ρ) t1) :
    HasDerivAt (fun s => (γ s).im ^ 2) (zeroVel t1 ρ) t1 := by
  have h1 : HasDerivAt (fun s => (γ s).im) (deriv (deriv (H t1)) ρ / deriv (H t1) ρ).im t1 := by
    have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (x := t1) hγd
    simpa [Function.comp_def] using this
  have h2 := h1.pow 2
  have h3 : ((fun s => (γ s).im) ^ 2 : ℝ → ℝ) = fun s => (γ s).im ^ 2 := by funext s; simp
  rw [h3] at h2
  refine h2.congr_deriv ?_
  simp [zeroVel, hγ0]

/-- **Zero dynamics from its two analytic parts.** -/
theorem zeroDynamics_of {t0 T : ℝ} (hH : HermiteSplit t0 T) (hP : PairSumForce t0 T) :
    ZeroDynamics t0 T := by
  intro t1 ht1 ρ h0 hre him hhigh
  by_cases hd : deriv (H t1) ρ = 0
  · exact Or.inl (hH t1 ht1 ρ h0 hre him hhigh hd)
  · right
    obtain ⟨γ, hγ0, hev, hγd⟩ := zero_branch h0 hd
    obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp hev
    have hnear : ∀ s ∈ Icc (t1 - ε / 2) t1, dist s t1 < ε := by
      intro s hs
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [hs.1, hs.2]
    refine ⟨ε / 2, by positivity, γ, hγ0, fun s hs => (hεP (hnear s hs)).1,
      fun s hs => (hεP (hnear s hs)).2.continuousWithinAt, zeroVel t1 ρ,
      (hasDerivAt_im_sq_branch hγ0 hγd).hasDerivWithinAt, hP t1 ht1 ρ h0 hre him hhigh hd⟩

end DBN
