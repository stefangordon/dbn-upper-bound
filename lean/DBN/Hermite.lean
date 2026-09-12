import Mathlib
import LeanCert.Analysis.DBN.ZeroTransfer
import DBN.ZeroBranch

/-!
# Backward Hermite splitting at a multiple zero

If `ρ` is a zero of `H_t` of order `m ≥ 2`, then for small `ε > 0` the function `H_{t−ε}` has a zero
at height `≥ Im ρ + c √ε`. The proof is the scaled limit

`ε^{−m/2} H_{t−ε}(ρ + √ε w) → a_m P_m(w)`, `a_m = H_t^{(m)}(ρ)`, `P_m(w) = Σ_{2j+k=m} w^k/(j! k!)`,

locally uniformly in `w`, obtained from the exact double expansion

`H_{t−s²}(ρ + s w) = Σ_{j,k} s^{2j+k} w^k/(j! k!) · moment (2j+k) t ρ`

(product of the exponential series of `e^{−s²u²}` and the Taylor series of `cos` under the heat
integral), followed by leancert's Hurwitz-type lemma `eventually_exists_zero_of_locally_uniform` at a
root `w*` of `P_m` with `Im w* > 0`.
-/

noncomputable section

namespace DBN

open Set Filter Topology MeasureTheory
open LeanCert.Analysis (norm_cos_le_exp_abs_im integrableOn_gaussian_moment)
open LeanCert.Analysis.DBN

namespace Hermite

/-! ### The cosine Taylor series and shift identities -/

theorem iteratedDeriv_cos (n : ℕ) :
    iteratedDeriv n Complex.cos = fun x => Complex.cos (x + (n : ℂ) * (Real.pi : ℂ) / 2) := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h : deriv (fun y : ℂ => Complex.cos (y + (n : ℂ) * (Real.pi : ℂ) / 2)) x =
        -Complex.sin (x + (n : ℂ) * (Real.pi : ℂ) / 2) := by
      have := (Complex.hasDerivAt_cos (x + (n : ℂ) * (Real.pi : ℂ) / 2)).comp x
        ((hasDerivAt_id x).add_const ((n : ℂ) * (Real.pi : ℂ) / 2))
      simp [Function.comp_def] at this; exact this.deriv
    rw [h, ← Complex.cos_add_pi_div_two]
    congr 1; push_cast; ring

theorem cos_add_nat_mul_pi (x : ℂ) (j : ℕ) :
    Complex.cos (x + (j : ℂ) * (Real.pi : ℂ)) = (-1) ^ j * Complex.cos x := by
  induction j with
  | zero => simp
  | succ j ih =>
    have : x + ((j + 1 : ℕ) : ℂ) * (Real.pi : ℂ) = (x + (j : ℂ) * (Real.pi : ℂ)) + Real.pi := by
      push_cast; ring
    rw [this, Complex.cos_add_pi, ih]; ring

/-- Taylor series of `cos` at `θ`. -/
theorem hasSum_cos_taylor (θ b : ℂ) :
    HasSum (fun k : ℕ => b ^ k / (k.factorial : ℂ) * Complex.cos (θ + (k : ℂ) * (Real.pi : ℂ) / 2))
      (Complex.cos (θ + b)) := by
  have h := Complex.hasSum_taylorSeries_of_entire Complex.differentiable_cos θ (θ + b)
  refine h.congr_fun fun k => ?_
  rw [iteratedDeriv_cos]
  simp only [smul_eq_mul, add_sub_cancel_left]
  ring

/-! ### The double expansion under the heat integral -/

/-- Coefficient of the `(j,k)` term: `s^{2j+k} w^k/(j! k!)`. -/
def coef (s : ℝ) (w : ℂ) (p : ℕ × ℕ) : ℂ :=
  (s : ℂ) ^ (2 * p.1 + p.2) * w ^ p.2 / ((p.1.factorial : ℂ) * (p.2.factorial : ℂ))

/-- The `(j,k)` integrand. -/
def term (t : ℝ) (ρ : ℂ) (s : ℝ) (w : ℂ) (p : ℕ × ℕ) (u : ℝ) : ℂ :=
  coef s w p * momentIntegrand (2 * p.1 + p.2) t ρ u

theorem im_aux (ρ : ℂ) (u : ℝ) (k : ℕ) :
    (ρ * (u : ℂ) + (k : ℂ) * (Real.pi : ℂ) / 2).im = ρ.im * u := by
  simp [Complex.mul_im]

/-- Pointwise: the heat integrand of `H_{t−s²}` at `ρ + s w` is the double series of the moment
integrands at `(t, ρ)`. -/
theorem hasSum_term (t : ℝ) (ρ : ℂ) (s : ℝ) (w : ℂ) (u : ℝ) :
    HasSum (fun p : ℕ × ℕ => term t ρ s w p u) (heatIntegrand (t - s ^ 2) (ρ + s * w) u) := by
  set f : ℕ → ℂ := fun j => (-((s : ℂ) ^ 2 * (u : ℂ) ^ 2)) ^ j / (j.factorial : ℂ) with hf
  set g : ℕ → ℂ := fun k => ((s : ℂ) * w * (u : ℂ)) ^ k / (k.factorial : ℂ) *
      Complex.cos (ρ * (u : ℂ) + (k : ℂ) * (Real.pi : ℂ) / 2) with hg
  have hfs : Summable fun j => ‖f j‖ := by
    have := Real.summable_pow_div_factorial (s ^ 2 * u ^ 2)
    refine this.congr fun j => ?_
    simp [hf, norm_div, norm_pow, norm_neg, Complex.norm_natCast, Complex.norm_real]
  have hgs : Summable fun k => ‖g k‖ := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      ((Real.summable_pow_div_factorial (‖(s : ℂ) * w * (u : ℂ)‖)).mul_right (Real.exp |ρ.im * u|))
    simp only [hg, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    gcongr
    have := norm_cos_le_exp_abs_im (ρ * (u : ℂ) + (k : ℂ) * (Real.pi : ℂ) / 2)
    rwa [im_aux] at this
  have hfsum : HasSum f (Complex.exp (-((s : ℂ) ^ 2 * (u : ℂ) ^ 2))) := by
    have := NormedSpace.expSeries_div_hasSum_exp (-((s : ℂ) ^ 2 * (u : ℂ) ^ 2))
    rwa [← Complex.exp_eq_exp_ℂ] at this
  have hgsum : HasSum g (Complex.cos (ρ * (u : ℂ) + (s : ℂ) * w * (u : ℂ))) := hasSum_cos_taylor _ _
  have hprod : HasSum (fun z : ℕ × ℕ => f z.1 * g z.2)
      (Complex.exp (-((s : ℂ) ^ 2 * (u : ℂ) ^ 2)) *
        Complex.cos (ρ * (u : ℂ) + (s : ℂ) * w * (u : ℂ))) := by
    have hsum := summable_mul_of_summable_norm hfs hgs
    have := hsum.hasSum
    rwa [← tsum_mul_tsum_of_summable_norm hfs hgs, hfsum.tsum_eq, hgsum.tsum_eq] at this
  have hprod' := hprod.mul_left (((Real.exp (t * u ^ 2) * LeanCert.Analysis.DBN.Phi u : ℝ) : ℂ))
  have e2 : heatIntegrand (t - s ^ 2) (ρ + s * w) u = ((Real.exp (t * u ^ 2) * LeanCert.Analysis.DBN.Phi u : ℝ) : ℂ) *
      (Complex.exp (-((s : ℂ) ^ 2 * (u : ℂ) ^ 2)) *
        Complex.cos (ρ * (u : ℂ) + (s : ℂ) * w * (u : ℂ))) := by
    simp only [heatIntegrand]
    have e1 : Real.exp ((t - s ^ 2) * u ^ 2) = Real.exp (t * u ^ 2) * Real.exp (-(s ^ 2 * u ^ 2)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1, show (ρ + (s : ℂ) * w) * (u : ℂ) = ρ * (u : ℂ) + (s : ℂ) * w * (u : ℂ) by ring]
    push_cast
    ring
  rw [e2]
  refine hprod'.congr_fun fun p => ?_
  simp only [term, coef, momentIntegrand, hf, hg]
  rw [show ρ * (u : ℂ) + ((2 * p.1 + p.2 : ℕ) : ℂ) * (Real.pi : ℂ) / 2 =
      (ρ * (u : ℂ) + (p.2 : ℂ) * (Real.pi : ℂ) / 2) + (p.1 : ℂ) * (Real.pi : ℂ) by push_cast; ring,
    cos_add_nat_mul_pi]
  push_cast
  ring

/-! ### Uniform bounds and the integral exchange -/

/-- The `s`-free coefficient `ĉ p = (1/4)^j (M/2)^k/(j! k!)`. -/
def chat (M : ℝ) (p : ℕ × ℕ) : ℝ :=
  M ^ p.2 / ((2 : ℝ) ^ (2 * p.1 + p.2) * ((p.1.factorial : ℝ) * (p.2.factorial : ℝ)))

/-- The dominating family: `Bnd p u = heatMajorant t ρ · e^{−u²} · ĉ p · u^{2j+k}`. -/
def Bnd (t : ℝ) (ρ : ℂ) (M : ℝ) (p : ℕ × ℕ) (u : ℝ) : ℝ :=
  heatMajorant t ρ * Real.exp (-u ^ 2) * (chat M p * u ^ (2 * p.1 + p.2))

/-- The integrable envelope `heatMajorant · e^{M²/4} · e^{−u²/2}`. -/
def env (t : ℝ) (ρ : ℂ) (M : ℝ) (u : ℝ) : ℝ :=
  heatMajorant t ρ * Real.exp (M ^ 2 / 4) * Real.exp (-(1 / 2) * u ^ 2)

/-- The tail constant `C₀ = ∫₀^∞ env`. -/
def C0 (t : ℝ) (ρ : ℂ) (M : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), env t ρ M u

theorem factorial_ne (p : ℕ × ℕ) : ((p.1.factorial : ℝ) * (p.2.factorial : ℝ)) ≠ 0 := by
  positivity

theorem chat_nonneg {M : ℝ} (hM : 0 ≤ M) (p : ℕ × ℕ) : 0 ≤ chat M p := by
  unfold chat; positivity

theorem two_s_pow_mul_chat (s M : ℝ) (p : ℕ × ℕ) :
    (2 * s) ^ (2 * p.1 + p.2) * chat M p =
      s ^ (2 * p.1 + p.2) * M ^ p.2 / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ)) := by
  unfold chat
  rw [mul_pow]
  have := factorial_ne p
  have h2 : (2 : ℝ) ^ (2 * p.1 + p.2) ≠ 0 := by positivity
  field_simp

theorem norm_coef (s : ℝ) (hs : 0 ≤ s) (w : ℂ) (p : ℕ × ℕ) :
    ‖coef s w p‖ = s ^ (2 * p.1 + p.2) * ‖w‖ ^ p.2 / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ)) := by
  simp only [coef, norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_natCast,
    Real.norm_eq_abs, abs_of_nonneg hs]

/-- `‖coef s w p‖ ≤ (2s)^{2j+k} ĉ p` for `‖w‖ ≤ M`. -/
theorem norm_coef_le {s M : ℝ} (hs : 0 ≤ s) {w : ℂ} (hw : ‖w‖ ≤ M) (p : ℕ × ℕ) :
    ‖coef s w p‖ ≤ (2 * s) ^ (2 * p.1 + p.2) * chat M p := by
  rw [norm_coef s hs, two_s_pow_mul_chat]
  have h1 : ‖w‖ ^ p.2 ≤ M ^ p.2 := pow_le_pow_left₀ (norm_nonneg _) hw _
  have := factorial_ne p
  gcongr

/-- The exponential series identity `Σ_p ĉ p u^{2j+k} = e^{u²/4} e^{Mu/2}`. -/
theorem hasSum_chat (M u : ℝ) :
    HasSum (fun p : ℕ × ℕ => chat M p * u ^ (2 * p.1 + p.2))
      (Real.exp (u ^ 2 / 4) * Real.exp (M * u / 2)) := by
  have hf := NormedSpace.expSeries_div_hasSum_exp (u ^ 2 / 4)
  have hg := NormedSpace.expSeries_div_hasSum_exp (M * u / 2)
  rw [← Real.exp_eq_exp_ℝ] at hf hg
  have hfs : Summable fun j : ℕ => ‖(u ^ 2 / 4) ^ j / (j.factorial : ℝ)‖ :=
    (Real.summable_pow_div_factorial _).norm
  have hgs : Summable fun k : ℕ => ‖(M * u / 2) ^ k / (k.factorial : ℝ)‖ :=
    (Real.summable_pow_div_factorial _).norm
  have hprod := (summable_mul_of_summable_norm hfs hgs).hasSum
  rw [← tsum_mul_tsum_of_summable_norm hfs hgs, hf.tsum_eq, hg.tsum_eq] at hprod
  refine hprod.congr_fun fun p => ?_
  simp only [chat]
  have h4 : (2 : ℝ) ^ (2 * p.1 + p.2) = 4 ^ p.1 * 2 ^ p.2 := by
    rw [pow_add, pow_mul]; norm_num
  rw [h4, div_pow, div_pow, mul_pow, pow_add, pow_mul]
  have := factorial_ne p
  have h4' : (4 : ℝ) ^ p.1 ≠ 0 := by positivity
  have h2' : (2 : ℝ) ^ p.2 ≠ 0 := by positivity
  field_simp

theorem Bnd_nonneg {t : ℝ} {ρ : ℂ} {M : ℝ} (hM : 0 ≤ M) (p : ℕ × ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ Bnd t ρ M p u := by
  unfold Bnd
  have := heatMajorant_pos t ρ
  have := chat_nonneg hM p
  positivity

theorem Bnd_eq (t : ℝ) (ρ : ℂ) (M : ℝ) (p : ℕ × ℕ) :
    Bnd t ρ M p = fun u => (heatMajorant t ρ * chat M p) * (u ^ (2 * p.1 + p.2) * Real.exp (-u ^ 2)) := by
  funext u; unfold Bnd; ring

theorem integrableOn_Bnd (t : ℝ) (ρ : ℂ) (M : ℝ) (p : ℕ × ℕ) :
    IntegrableOn (Bnd t ρ M p) (Ioi 0) := by
  rw [Bnd_eq]
  exact (integrableOn_gaussian_moment _).const_mul _

theorem integrableOn_env (t : ℝ) (ρ : ℂ) (M : ℝ) : IntegrableOn (env t ρ M) (Ioi 0) := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).integrableOn (s := Ioi (0 : ℝ))
  have := h.const_mul (heatMajorant t ρ * Real.exp (M ^ 2 / 4))
  refine IntegrableOn.congr_fun this (fun u _ => ?_) measurableSet_Ioi
  unfold env; ring

/-- Finite partial sums of the dominating family are below the envelope. -/
theorem sum_Bnd_le {t : ℝ} {ρ : ℂ} {M : ℝ} (hM : 0 ≤ M) (S : Finset (ℕ × ℕ)) {u : ℝ} (hu : 0 ≤ u) :
    ∑ p ∈ S, Bnd t ρ M p u ≤ env t ρ M u := by
  have hsum := hasSum_chat M u
  have hle : ∑ p ∈ S, chat M p * u ^ (2 * p.1 + p.2) ≤ Real.exp (u ^ 2 / 4) * Real.exp (M * u / 2) := by
    rw [← hsum.tsum_eq]
    exact hsum.summable.sum_le_tsum S (fun p _ => by have := chat_nonneg hM p; positivity)
  have hexp : Real.exp (-u ^ 2) * (Real.exp (u ^ 2 / 4) * Real.exp (M * u / 2)) ≤
      Real.exp (M ^ 2 / 4) * Real.exp (-(1 / 2) * u ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (u - M)]
  have hpos := heatMajorant_pos t ρ
  calc ∑ p ∈ S, Bnd t ρ M p u
      = heatMajorant t ρ * Real.exp (-u ^ 2) * ∑ p ∈ S, chat M p * u ^ (2 * p.1 + p.2) := by
        unfold Bnd; rw [Finset.mul_sum]
    _ ≤ heatMajorant t ρ * Real.exp (-u ^ 2) * (Real.exp (u ^ 2 / 4) * Real.exp (M * u / 2)) := by
        gcongr
    _ = heatMajorant t ρ * (Real.exp (-u ^ 2) * (Real.exp (u ^ 2 / 4) * Real.exp (M * u / 2))) := by ring
    _ ≤ heatMajorant t ρ * (Real.exp (M ^ 2 / 4) * Real.exp (-(1 / 2) * u ^ 2)) := by gcongr
    _ = env t ρ M u := by unfold env; ring

/-- The integrated bounds `b p = ∫₀^∞ Bnd p`. -/
def bInt (t : ℝ) (ρ : ℂ) (M : ℝ) (p : ℕ × ℕ) : ℝ := ∫ u in Ioi (0 : ℝ), Bnd t ρ M p u

theorem bInt_nonneg {t : ℝ} {ρ : ℂ} {M : ℝ} (hM : 0 ≤ M) (p : ℕ × ℕ) : 0 ≤ bInt t ρ M p :=
  setIntegral_nonneg measurableSet_Ioi fun u hu => Bnd_nonneg hM p (le_of_lt hu)

theorem summable_bInt {t : ℝ} {ρ : ℂ} {M : ℝ} (hM : 0 ≤ M) : Summable (bInt t ρ M) := by
  refine summable_of_sum_le (c := C0 t ρ M) (fun p => bInt_nonneg hM p) fun S => ?_
  unfold bInt
  rw [← integral_finsetSum S (fun p _ => integrableOn_Bnd t ρ M p)]
  refine integral_mono_of_nonneg ?_ (integrableOn_env t ρ M) ?_
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu =>
      Finset.sum_nonneg fun p _ => Bnd_nonneg hM p (le_of_lt hu))
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu =>
      sum_Bnd_le hM S (le_of_lt hu))

theorem tsum_bInt_le {t : ℝ} {ρ : ℂ} {M : ℝ} (hM : 0 ≤ M) : ∑' p, bInt t ρ M p ≤ C0 t ρ M := by
  refine (summable_bInt hM).tsum_le_of_sum_le fun S => ?_
  unfold bInt
  rw [← integral_finsetSum S (fun p _ => integrableOn_Bnd t ρ M p)]
  refine integral_mono_of_nonneg ?_ (integrableOn_env t ρ M) ?_
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu =>
      Finset.sum_nonneg fun p _ => Bnd_nonneg hM p (le_of_lt hu))
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu =>
      sum_Bnd_le hM S (le_of_lt hu))

/-- `ĉ p ‖moment (2j+k) t ρ‖ ≤ b p`. -/
theorem chat_mul_norm_moment_le {t : ℝ} {ρ : ℂ} {M : ℝ} (hM : 0 ≤ M) (p : ℕ × ℕ) :
    chat M p * ‖moment (2 * p.1 + p.2) t ρ‖ ≤ bInt t ρ M p := by
  have hc := chat_nonneg hM p
  have h1 : chat M p * ‖moment (2 * p.1 + p.2) t ρ‖ =
      ‖∫ u in Ioi (0 : ℝ), (chat M p : ℂ) * momentIntegrand (2 * p.1 + p.2) t ρ u‖ := by
    rw [integral_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    rfl
  rw [h1]
  refine (norm_integral_le_integral_norm _).trans ?_
  unfold bInt
  refine integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _) (integrableOn_Bnd t ρ M p) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
  dsimp only
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  have hb := momentIntegrand_bound (2 * p.1 + p.2) t ρ (le_of_lt hu)
  unfold Bnd
  calc chat M p * ‖momentIntegrand (2 * p.1 + p.2) t ρ u‖
      ≤ chat M p * (heatMajorant t ρ * (u ^ (2 * p.1 + p.2) * Real.exp (-u ^ 2))) := by gcongr
    _ = heatMajorant t ρ * Real.exp (-u ^ 2) * (chat M p * u ^ (2 * p.1 + p.2)) := by ring

/-- The `(s,w)` coefficient times the moment is dominated by `(2s)^{2j+k} b p`. -/
theorem norm_coef_mul_moment_le {t : ℝ} {ρ : ℂ} {s M : ℝ} (hs : 0 ≤ s) (hM : 0 ≤ M) {w : ℂ}
    (hw : ‖w‖ ≤ M) (p : ℕ × ℕ) :
    ‖coef s w p * moment (2 * p.1 + p.2) t ρ‖ ≤ (2 * s) ^ (2 * p.1 + p.2) * bInt t ρ M p := by
  rw [norm_mul]
  calc ‖coef s w p‖ * ‖moment (2 * p.1 + p.2) t ρ‖
      ≤ ((2 * s) ^ (2 * p.1 + p.2) * chat M p) * ‖moment (2 * p.1 + p.2) t ρ‖ := by
        gcongr; exact norm_coef_le hs hw p
    _ = (2 * s) ^ (2 * p.1 + p.2) * (chat M p * ‖moment (2 * p.1 + p.2) t ρ‖) := by ring
    _ ≤ (2 * s) ^ (2 * p.1 + p.2) * bInt t ρ M p := by
        gcongr; exact chat_mul_norm_moment_le hM p

theorem two_s_pow_le_one {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ 1 / 2) (n : ℕ) : (2 * s) ^ n ≤ 1 :=
  pow_le_one₀ (by positivity) (by linarith)

theorem summable_norm_coef_mul_moment {t : ℝ} {ρ : ℂ} {s M : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ 1 / 2)
    (hM : 0 ≤ M) {w : ℂ} (hw : ‖w‖ ≤ M) :
    Summable fun p : ℕ × ℕ => ‖coef s w p * moment (2 * p.1 + p.2) t ρ‖ := by
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
    (summable_bInt (t := t) (ρ := ρ) hM)
  refine (norm_coef_mul_moment_le hs hM hw p).trans ?_
  have h1 := bInt_nonneg (t := t) (ρ := ρ) hM p
  have h2 := two_s_pow_le_one hs hs2 (2 * p.1 + p.2)
  nlinarith

theorem term_integrable (t : ℝ) (ρ : ℂ) (s : ℝ) (w : ℂ) (p : ℕ × ℕ) :
    Integrable (term t ρ s w p) (volume.restrict (Ioi 0)) :=
  (momentIntegrand_integrable _ t ρ).const_mul _

/-- **The double expansion.** For `0 ≤ s ≤ 1/2` and `‖w‖ ≤ M`,
`H_{t−s²}(ρ + s w) = Σ_{(j,k)} s^{2j+k} w^k/(j!k!) · moment (2j+k) t ρ`. -/
theorem hasSum_expansion {t : ℝ} {ρ : ℂ} {s M : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ 1 / 2) (hM : 0 ≤ M)
    {w : ℂ} (hw : ‖w‖ ≤ M) :
    HasSum (fun p : ℕ × ℕ => coef s w p * moment (2 * p.1 + p.2) t ρ) (H (t - s ^ 2) (ρ + s * w)) := by
  have hsum : Summable fun p : ℕ × ℕ => ∫ u in Ioi (0 : ℝ), ‖term t ρ s w p u‖ := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun u => norm_nonneg _)
      (fun p => ?_) (summable_bInt (t := t) (ρ := ρ) hM)
    unfold bInt
    refine integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _)
      (integrableOn_Bnd t ρ M p) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    dsimp only
    unfold term
    rw [norm_mul]
    have hb := momentIntegrand_bound (2 * p.1 + p.2) t ρ (le_of_lt hu)
    have hc := norm_coef_le hs hw p
    have h2 := two_s_pow_le_one hs hs2 (2 * p.1 + p.2)
    have hcn := chat_nonneg hM p
    have hpos : 0 ≤ heatMajorant t ρ * (u ^ (2 * p.1 + p.2) * Real.exp (-u ^ 2)) := by
      have := heatMajorant_pos t ρ; have : (0 : ℝ) ≤ u := le_of_lt hu; positivity
    calc ‖coef s w p‖ * ‖momentIntegrand (2 * p.1 + p.2) t ρ u‖
        ≤ ((2 * s) ^ (2 * p.1 + p.2) * chat M p) *
            (heatMajorant t ρ * (u ^ (2 * p.1 + p.2) * Real.exp (-u ^ 2))) := by gcongr
      _ ≤ (1 * chat M p) * (heatMajorant t ρ * (u ^ (2 * p.1 + p.2) * Real.exp (-u ^ 2))) := by
          gcongr
      _ = Bnd t ρ M p u := by unfold Bnd; ring
  have h := hasSum_integral_of_summable_integral_norm (term_integrable t ρ s w) hsum
  have e1 : ∀ p : ℕ × ℕ, (∫ u in Ioi (0 : ℝ), term t ρ s w p u) = coef s w p * moment (2 * p.1 + p.2) t ρ := by
    intro p; unfold term; rw [integral_const_mul]; rfl
  have e2 : (∫ u in Ioi (0 : ℝ), ∑' p : ℕ × ℕ, term t ρ s w p u) = H (t - s ^ 2) (ρ + s * w) := by
    rw [H_eq]
    unfold LeanCert.Analysis.DBN.H
    congr 1
    funext u
    exact (hasSum_term t ρ s w u).tsum_eq
  rw [e2] at h
  exact h.congr_fun fun p => (e1 p).symm

/-! ### The limit polynomial and the tail estimate -/

/-- Index set of the weight-`m` terms. -/
def E (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter (fun p => 2 * p.1 + p.2 = m)

/-- Index set of the terms of weight `≤ m`. -/
def Fle (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter (fun p => 2 * p.1 + p.2 ≤ m)

theorem mem_E {m : ℕ} {p : ℕ × ℕ} : p ∈ E m ↔ 2 * p.1 + p.2 = m := by
  simp only [E, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega

theorem mem_Fle {m : ℕ} {p : ℕ × ℕ} : p ∈ Fle m ↔ 2 * p.1 + p.2 ≤ m := by
  simp only [Fle, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega

/-- The limit polynomial `P_m(w) = Σ_{2j+k=m} w^k/(j! k!)`. -/
def P (m : ℕ) (w : ℂ) : ℂ := ∑ p ∈ E m, w ^ p.2 / ((p.1.factorial : ℂ) * (p.2.factorial : ℂ))

theorem sum_Fle_eq {t : ℝ} {ρ : ℂ} {m : ℕ} (hlow : ∀ n < m, moment n t ρ = 0) (s : ℝ) (w : ℂ) :
    ∑ p ∈ Fle m, coef s w p * moment (2 * p.1 + p.2) t ρ = (s : ℂ) ^ m * (moment m t ρ * P m w) := by
  rw [← Finset.sum_filter_add_sum_filter_not (Fle m) (fun p => 2 * p.1 + p.2 = m)]
  have h0 : ∑ p ∈ (Fle m).filter (fun p => ¬ 2 * p.1 + p.2 = m), coef s w p * moment (2 * p.1 + p.2) t ρ = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_filter, mem_Fle] at hp
    rw [hlow _ (lt_of_le_of_ne hp.1 hp.2), mul_zero]
  have hE : (Fle m).filter (fun p => 2 * p.1 + p.2 = m) = E m := by
    ext p; simp only [Finset.mem_filter, mem_Fle, mem_E]; omega
  rw [h0, add_zero, hE, P, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [mem_E] at hp
  unfold coef
  rw [hp]
  ring

/-- **Tail estimate.** `‖H_{t−s²}(ρ + s w) − s^m a_m P_m(w)‖ ≤ (2s)^{m+1} C₀`. -/
theorem tail_bound {t : ℝ} {ρ : ℂ} {m : ℕ} (hlow : ∀ n < m, moment n t ρ = 0) {s M : ℝ} (hs : 0 ≤ s)
    (hs2 : s ≤ 1 / 2) (hM : 0 ≤ M) {w : ℂ} (hw : ‖w‖ ≤ M) :
    ‖H (t - s ^ 2) (ρ + s * w) - (s : ℂ) ^ m * (moment m t ρ * P m w)‖ ≤ (2 * s) ^ (m + 1) * C0 t ρ M := by
  set a : ℕ × ℕ → ℂ := fun p => coef s w p * moment (2 * p.1 + p.2) t ρ with ha
  have hsum : Summable a := (hasSum_expansion hs hs2 hM hw).summable
  have hnorm : Summable fun p => ‖a p‖ := summable_norm_coef_mul_moment hs hs2 hM hw
  have hb := summable_bInt (t := t) (ρ := ρ) hM
  have hsplit := hsum.sum_add_tsum_compl (s := Fle m)
  rw [(hasSum_expansion hs hs2 hM hw).tsum_eq] at hsplit
  have hF : ∑ x ∈ Fle m, a x = (s : ℂ) ^ m * (moment m t ρ * P m w) := sum_Fle_eq hlow s w
  rw [hF] at hsplit
  have e : H (t - s ^ 2) (ρ + s * w) - (s : ℂ) ^ m * (moment m t ρ * P m w) = ∑' x : ↑((↑(Fle m) : Set (ℕ × ℕ))ᶜ), a x := by
    linear_combination -hsplit
  rw [e]
  -- each term outside `Fle m` has weight `≥ m+1`
  have hterm : ∀ x : ↑((↑(Fle m) : Set (ℕ × ℕ))ᶜ), ‖a x‖ ≤ (2 * s) ^ (m + 1) * bInt t ρ M x := by
    intro x
    have hx : m + 1 ≤ 2 * x.1.1 + x.1.2 := by
      have := x.2
      simp only [Set.mem_compl_iff, Finset.mem_coe, mem_Fle] at this
      omega
    refine (norm_coef_mul_moment_le hs hM hw x.1).trans ?_
    have := bInt_nonneg (t := t) (ρ := ρ) hM x.1
    have hp : (2 * s) ^ (2 * x.1.1 + x.1.2) ≤ (2 * s) ^ (m + 1) :=
      pow_le_pow_of_le_one (by positivity) (by linarith) hx
    exact mul_le_mul_of_nonneg_right hp this
  have hsub : Summable fun x : ↑((↑(Fle m) : Set (ℕ × ℕ))ᶜ) => ‖a x‖ := hnorm.subtype _
  have hbsub : Summable fun x : ↑((↑(Fle m) : Set (ℕ × ℕ))ᶜ) => bInt t ρ M x := hb.subtype _
  calc ‖∑' x : ↑((↑(Fle m) : Set (ℕ × ℕ))ᶜ), a x‖
      ≤ ∑' x : ↑((↑(Fle m) : Set (ℕ × ℕ))ᶜ), ‖a x‖ := norm_tsum_le_tsum_norm hsub
    _ ≤ ∑' x : ↑((↑(Fle m) : Set (ℕ × ℕ))ᶜ), (2 * s) ^ (m + 1) * bInt t ρ M x :=
        hsub.tsum_le_tsum hterm (hbsub.mul_left _)
    _ = (2 * s) ^ (m + 1) * ∑' x : ↑((↑(Fle m) : Set (ℕ × ℕ))ᶜ), bInt t ρ M x := tsum_mul_left
    _ ≤ (2 * s) ^ (m + 1) * ∑' p, bInt t ρ M p := by
        gcongr
        have h2 := hb.sum_add_tsum_compl (s := Fle m)
        have h3 : 0 ≤ ∑ x ∈ Fle m, bInt t ρ M x := Finset.sum_nonneg fun p _ => bInt_nonneg hM p
        linarith
    _ ≤ (2 * s) ^ (m + 1) * C0 t ρ M := by gcongr; exact tsum_bInt_le hM

/-! ### Uniform convergence of the scaled functions -/

/-- The scaled function `G s w = H_{t−s²}(ρ + s w)/s^m`. -/
def G (t : ℝ) (ρ : ℂ) (m : ℕ) (s : ℝ) (w : ℂ) : ℂ := H (t - s ^ 2) (ρ + s * w) / (s : ℂ) ^ m

theorem C0_nonneg (t : ℝ) (ρ : ℂ) (M : ℝ) : 0 ≤ C0 t ρ M :=
  setIntegral_nonneg measurableSet_Ioi fun u _ => by
    unfold env; have := heatMajorant_pos t ρ; positivity

theorem tendstoUniformlyOn_G {t : ℝ} {ρ : ℂ} {m : ℕ} (hlow : ∀ n < m, moment n t ρ = 0) {M : ℝ}
    (hM : 0 ≤ M) :
    TendstoUniformlyOn (G t ρ m) (fun w => moment m t ρ * P m w) (𝓝[>] 0) (Metric.closedBall 0 M) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hC := C0_nonneg t ρ M
  set A : ℝ := 2 ^ (m + 1) * C0 t ρ M with hA
  have hA0 : 0 ≤ A := by positivity
  set δ : ℝ := min (1 / 2) (ε / (A + 1)) with hδ
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hδpos] with s hs
  intro w hw
  have hs0 : 0 < s := hs.1
  have hs2 : s ≤ 1 / 2 := le_trans hs.2.le (min_le_left _ _)
  have hsε : s ≤ ε / (A + 1) := le_trans hs.2.le (min_le_right _ _)
  rw [Metric.mem_closedBall, dist_zero_right] at hw
  have hb := tail_bound hlow hs0.le hs2 hM hw
  have hsm : ((s : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hs0.ne')
  have e : moment m t ρ * P m w - G t ρ m s w =
      ((s : ℂ) ^ m * (moment m t ρ * P m w) - H (t - s ^ 2) (ρ + s * w)) / (s : ℂ) ^ m := by
    unfold G; rw [sub_div, mul_div_cancel_left₀ _ hsm]
  have hlt : A * s < ε := by
    have h1 : A * s ≤ A * (ε / (A + 1)) := mul_le_mul_of_nonneg_left hsε hA0
    have h2 : A * (ε / (A + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    exact lt_of_le_of_lt h1 h2
  rw [dist_eq_norm, e, norm_div, norm_sub_rev, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs0, div_lt_iff₀ (pow_pos hs0 m)]
  calc ‖H (t - s ^ 2) (ρ + s * w) - (s : ℂ) ^ m * (moment m t ρ * P m w)‖
      ≤ (2 * s) ^ (m + 1) * C0 t ρ M := hb
    _ = (A * s) * s ^ m := by rw [hA]; ring
    _ < ε * s ^ m := mul_lt_mul_of_pos_right hlt (pow_pos hs0 m)

theorem tendstoLocallyUniformly_G {t : ℝ} {ρ : ℂ} {m : ℕ} (hlow : ∀ n < m, moment n t ρ = 0) :
    TendstoLocallyUniformly (G t ρ m) (fun w => moment m t ρ * P m w) (𝓝[>] 0) := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  have hsub : K ⊆ Metric.closedBall 0 (max r 0) :=
    hr.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  exact (tendstoUniformlyOn_G hlow (le_max_right r 0)).mono hsub

theorem differentiable_P (m : ℕ) : Differentiable ℂ (P m) := by
  unfold P
  have h := Differentiable.sum (𝕜 := ℂ) (u := E m)
    (A := fun p w => w ^ p.2 / ((p.1.factorial : ℂ) * (p.2.factorial : ℂ)))
    fun p _ => (differentiable_id.pow _).div_const _
  have e : (∑ i ∈ E m, fun w : ℂ => w ^ i.2 / ((i.1.factorial : ℂ) * (i.2.factorial : ℂ))) =
      fun w => ∑ p ∈ E m, w ^ p.2 / ((p.1.factorial : ℂ) * (p.2.factorial : ℂ)) := by
    funext w; simp [Finset.sum_apply]
  rw [e] at h; exact h

theorem differentiable_G (t : ℝ) (ρ : ℂ) (m : ℕ) (s : ℝ) : Differentiable ℂ (G t ρ m s) := by
  unfold G
  rw [H_eq]
  have hH := H_entire (t - s ^ 2)
  exact (hH.comp ((differentiable_const _).add ((differentiable_const _).mul differentiable_id))).div_const _

/-! ### A root of `P_m` in the upper half-plane -/

/-- `Rf m y = Σ_{j ≤ m/2} y^{m/2−j}/(j!(m−2j)!)`, so that `P m w = w^{m%2} Rf m (w²)`. -/
def Rf (m : ℕ) (y : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (m / 2 + 1), y ^ (m / 2 - j) / ((j.factorial : ℂ) * ((m - 2 * j).factorial : ℂ))

theorem P_eq_Rf (m : ℕ) (w : ℂ) : P m w = w ^ (m % 2) * Rf m (w ^ 2) := by
  unfold P Rf
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_nbij (fun j => (j, m - 2 * j)) ?_ ?_ ?_ ?_
  · intro j hj; rw [Finset.mem_range] at hj; rw [mem_E]; omega
  · intro j _ j' _ h; simp only [Prod.mk.injEq] at h; exact h.1
  · intro p hp
    rw [Finset.mem_coe, mem_E] at hp
    refine ⟨p.1, ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_range]; omega
    · ext
      · rfl
      · simp only; omega
  · intro j hj
    rw [Finset.mem_range] at hj
    simp only
    have : m - 2 * j = 2 * (m / 2 - j) + m % 2 := by omega
    rw [this, pow_add, pow_mul]
    ring

/-- The polynomial with `eval = Rf m`. -/
def Rp (m : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (m / 2 + 1),
    Polynomial.C (1 / ((j.factorial : ℂ) * ((m - 2 * j).factorial : ℂ))) * Polynomial.X ^ (m / 2 - j)

theorem Rp_eval (m : ℕ) (y : ℂ) : (Rp m).eval y = Rf m y := by
  unfold Rp Rf
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem Rp_coeff (m : ℕ) : (Rp m).coeff (m / 2) = 1 / (m.factorial : ℂ) := by
  unfold Rp
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single 0]
  · simp [Polynomial.coeff_C_mul_X_pow]
  · intro j hj hj0
    rw [Finset.mem_range] at hj
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]; omega
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

theorem Rp_degree_pos {m : ℕ} (hm : 2 ≤ m) : 0 < (Rp m).degree := by
  rw [← Polynomial.natDegree_pos_iff_degree_pos]
  have h := Polynomial.le_natDegree_of_ne_zero (p := Rp m) (n := m / 2)
    (by rw [Rp_coeff]; exact one_div_ne_zero (by exact_mod_cast Nat.factorial_ne_zero m))
  omega

theorem Rf_real_ne_zero (m : ℕ) {r : ℝ} (hr : 0 ≤ r) : Rf m (r : ℂ) ≠ 0 := by
  have hreal : Rf m (r : ℂ) = ((∑ j ∈ Finset.range (m / 2 + 1),
      r ^ (m / 2 - j) / ((j.factorial : ℝ) * ((m - 2 * j).factorial : ℝ)) : ℝ) : ℂ) := by
    unfold Rf; push_cast; rfl
  rw [hreal, Complex.ofReal_ne_zero]
  apply ne_of_gt
  have hmem : m / 2 ∈ Finset.range (m / 2 + 1) := Finset.mem_range.mpr (Nat.lt_succ_self _)
  have hterm : 0 < r ^ (m / 2 - m / 2) / (((m / 2).factorial : ℝ) * ((m - 2 * (m / 2)).factorial : ℝ)) := by
    rw [Nat.sub_self, pow_zero]; positivity
  have hle := Finset.single_le_sum
    (f := fun j => r ^ (m / 2 - j) / ((j.factorial : ℝ) * ((m - 2 * j).factorial : ℝ)))
    (fun j _ => by positivity) hmem
  exact lt_of_lt_of_le hterm hle

theorem P_one_ne_zero (m : ℕ) : P m 1 ≠ 0 := by
  rw [P_eq_Rf, one_pow, one_mul]
  have := Rf_real_ne_zero m (r := 1) zero_le_one
  simpa using this

theorem exists_root_P {m : ℕ} (hm : 2 ≤ m) : ∃ w : ℂ, P m w = 0 ∧ 0 < w.im := by
  obtain ⟨y0, hy0⟩ := Complex.exists_root (Rp_degree_pos hm)
  have hR : Rf m y0 = 0 := by rw [← Rp_eval]; exact hy0
  obtain ⟨w0, hw0⟩ := IsAlgClosed.exists_pow_nat_eq y0 (two_pos : 0 < 2)
  have him : w0.im ≠ 0 := by
    intro h
    have hw0r : w0 = (w0.re : ℂ) := Complex.ext rfl (by simp [h])
    have : Rf m ((w0.re ^ 2 : ℝ) : ℂ) = 0 := by rw [Complex.ofReal_pow, ← hw0r, hw0]; exact hR
    exact Rf_real_ne_zero m (sq_nonneg _) this
  by_cases hpos : 0 < w0.im
  · exact ⟨w0, by rw [P_eq_Rf, hw0, hR, mul_zero], hpos⟩
  · refine ⟨-w0, by rw [P_eq_Rf, neg_sq, hw0, hR, mul_zero], ?_⟩
    push_neg at hpos
    simp only [Complex.neg_im]
    exact neg_pos.mpr (lt_of_le_of_ne hpos him)

/-! ### The splitting theorem -/

theorem exists_moment_ne (t : ℝ) (ρ : ℂ) : ∃ n, moment n t ρ ≠ 0 := by
  by_contra hall
  push_neg at hall
  have h := hasSum_expansion (t := t) (ρ := ρ) (s := 1 / 2) (M := 2 * ‖ρ‖) (w := -2 * ρ)
    (by norm_num) le_rfl (by positivity) (by simp)
  simp only [hall, mul_zero] at h
  have h0 : (0 : ℂ) = H (t - (1 / 2 : ℝ) ^ 2) (ρ + ((1 / 2 : ℝ) : ℂ) * (-2 * ρ)) := hasSum_zero.unique h
  have e : ρ + ((1 / 2 : ℝ) : ℂ) * (-2 * ρ) = 0 := by push_cast; ring
  rw [e, H_eq] at h0
  exact H_zero_ne_zero _ h0.symm

/-- **Backward Hermite splitting.** At a zero `ρ` of `H_t` with `H_t'(ρ) = 0`, for all small `ε > 0`
there is a zero of `H_{t−ε}` at height `≥ Im ρ + c √ε`. -/
theorem hermite_split {t : ℝ} {ρ : ℂ} (h0 : H t ρ = 0) (hd : deriv (H t) ρ = 0) :
    ∃ c > (0 : ℝ), ∃ ε0 > (0 : ℝ), ∀ ε ∈ Ioo (0 : ℝ) ε0,
      ∃ z : ℂ, H (t - ε) z = 0 ∧ ρ.im + c * Real.sqrt ε ≤ z.im := by
  classical
  have hex : ∃ n, moment n t ρ ≠ 0 := exists_moment_ne t ρ
  set m := Nat.find hex with hm_def
  have hm : moment m t ρ ≠ 0 := Nat.find_spec hex
  have hlow : ∀ n < m, moment n t ρ = 0 := fun n hn => by
    have := Nat.find_min hex hn; push_neg at this; exact this
  have hm2 : 2 ≤ m := by
    by_contra hlt
    push_neg at hlt
    have h01 : m = 0 ∨ m = 1 := by omega
    rcases h01 with h | h
    · rw [h] at hm; apply hm; rw [moment_zero, ← H_eq_apply]; exact h0
    · rw [h] at hm; apply hm; rw [← deriv_H_z, ← H_eq]; exact hd
  obtain ⟨wst, hP, him⟩ := exists_root_P hm2
  set r := wst.im / 2 with hr
  have hr0 : 0 < r := half_pos him
  have hev := eventually_exists_zero_of_locally_uniform (l := 𝓝[>] (0 : ℝ)) (F := G t ρ m)
    (f := fun w => moment m t ρ * P m w)
    (fun K _ => Eventually.of_forall fun s => (differentiable_G t ρ m s).differentiableOn)
    ((differentiable_P m).const_mul _) ⟨1, mul_ne_zero hm (P_one_ne_zero m)⟩
    (tendstoLocallyUniformly_G hlow) (U := Metric.ball wst r) (z := wst) Metric.isOpen_ball
    (Metric.mem_ball_self hr0) (by simp [hP])
  obtain ⟨s0, hs0, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hs0' : (0 : ℝ) < s0 := hs0
  refine ⟨r, hr0, s0 ^ 2, by positivity, fun ε hε => ?_⟩
  set s := Real.sqrt ε with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hε.1
  have hss0 : s < s0 := by
    rw [hs, show s0 = Real.sqrt (s0 ^ 2) from (Real.sqrt_sq hs0'.le).symm]
    exact Real.sqrt_lt_sqrt hε.1.le hε.2
  obtain ⟨w, hwball, hGw⟩ := hsub ⟨hspos, hss0⟩
  have hsm : ((s : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hspos.ne')
  have hHz : H (t - s ^ 2) (ρ + s * w) = 0 := by
    unfold G at hGw; exact (div_eq_zero_iff.mp hGw).resolve_right hsm
  refine ⟨ρ + s * w, ?_, ?_⟩
  · rwa [hs, Real.sq_sqrt hε.1.le] at hHz
  · have hwim : r ≤ w.im := by
      have h1 : |w.im - wst.im| ≤ ‖w - wst‖ := by
        have := Complex.abs_im_le_norm (w - wst); simpa using this
      have h2 : ‖w - wst‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hwball
      have := abs_sub_lt_iff.mp (lt_of_le_of_lt h1 h2)
      linarith [this.2]
    have him' : (ρ + (s : ℂ) * w).im = ρ.im + s * w.im := by simp [Complex.add_im, Complex.mul_im]
    rw [him']
    have := mul_le_mul_of_nonneg_left hwim hspos.le
    linarith

end Hermite

/-- **`HermiteSplit` is a theorem**, with `C = 0`. -/
theorem hermiteSplit_proved (t0 T : ℝ) : HermiteSplit t0 T := by
  intro t1 _ ρ h0 _ _ _ hd
  obtain ⟨c, hc, ε0, hε0, h⟩ := Hermite.hermite_split h0 hd
  refine ⟨c, hc, 0, le_refl _, ε0, hε0, fun ε hε => ?_⟩
  obtain ⟨z, hz, hzim⟩ := h ε hε
  exact ⟨z, hz, by simpa using hzim⟩

end DBN
