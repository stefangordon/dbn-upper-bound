import Mathlib
import LeanCert.Analysis.DBN.CanonicalProduct
import LeanCert.Analysis.DBN.TimePolynomialApproximation
import DBN.ZeroBranch
import DBN.Kernels
import DBN.Algebra

/-!
# The pair-sum force laws at a simple highest zero

leancert gives the Hadamard product of `H_t` and the sum formula
`H_t'/H_t (z) = Σ_p (1/(z − ζ_p) + 1/ζ_p)` over the zero index type `divisorZeroIndex₀` (zeros with
multiplicity). Pairing each index with its conjugate index turns imaginary parts into the kernels
`K_Y(d, b)` of `DBN.Kernels`:

`S(x, Y, t) = ½ Σ_p K_Y(x − Re ζ_p, Im ζ_p)`, `S_Y(x, Y, t) = ½ Σ_p ∂_Y K_Y(x − Re ζ_p, Im ζ_p)`,

and at a simple zero `ρ = x + ih` the branch velocity `zeroVel = 2h·Im(H''/H')(ρ)` equals
`−2 − 2h Σ_{p ∉ {ρ, ρ̄}} K_h(x − Re ζ_p, Im ζ_p)`. The kernel minorants of `DBN.Kernels` then give the
source law and the two field laws termwise: `PairSumForce` is a theorem.
-/

noncomputable section

namespace DBN

open Set Filter Topology Complex Complex.Hadamard
open scoped ComplexConjugate
open LeanCert.Analysis.DBN LeanCert.Analysis.DBN.TimeApproximation
open DBN.Kernels DBN.Algebra

namespace PairSum

variable (t : ℝ)

/-- The zero-index type of `H_t` (zeros with multiplicity; `0` is never a zero). -/
abbrev Idx := divisorZeroIndex₀ (LeanCert.Analysis.DBN.H t) univ

/-- The zero attached to an index. -/
abbrev ζ (p : Idx t) : ℂ := divisorZeroIndex₀_val p

theorem summable_inv_sq : Summable fun p : Idx t => ‖ζ t p‖⁻¹ ^ 2 := H_inverse_square_summable t

theorem H_ζ (p : Idx t) : LeanCert.Analysis.DBN.H t (ζ t p) = 0 := by
  have h := divisorZeroIndex₀_val_mem_divisor_support p
  rw [divisor_univ_eq_analyticOrderNatAt_int (H_entire t)] at h
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (by exact_mod_cast h)

theorem ne_ζ {z : ℂ} (hz : LeanCert.Analysis.DBN.H t z ≠ 0) (p : Idx t) : z ≠ ζ t p := by
  intro h; exact hz (h ▸ H_ζ t p)

/-- The zero-sum term `T_p(z) = 1/(z − ζ_p) + 1/ζ_p`. -/
def T (p : Idx t) (z : ℂ) : ℂ := 1 / (z - ζ t p) + 1 / ζ t p

theorem summable_T {z : ℂ} (hz : LeanCert.Analysis.DBN.H t z ≠ 0) : Summable fun p => T t p z :=
  summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq (summable_inv_sq t) (ne_ζ t hz)

/-- The logarithmic derivative of `H_t` away from its zeros is the zero sum. -/
theorem logDeriv_eq_tsum {z : ℂ} (hz : LeanCert.Analysis.DBN.H t z ≠ 0) :
    logDeriv (LeanCert.Analysis.DBN.H t) z = ∑' p, T t p z := by
  have h1 : logDeriv (fun w => LeanCert.Analysis.DBN.H t 0 *
      divisorCanonicalProduct 1 (LeanCert.Analysis.DBN.H t) univ w) z =
      logDeriv (LeanCert.Analysis.DBN.H t) z := by
    congr 1
    funext w
    exact (H_eq_normalized_canonicalProduct t w).symm
  rw [← h1, logDeriv_const_mul _ _ (H_zero_ne_zero t)]
  exact logDeriv_divisorCanonicalProduct_one_eq_tsum_of_forall_ne (summable_inv_sq t) (ne_ζ t hz)

/-! ### The conjugation involution on indices -/

theorem divisor_conj (z : ℂ) :
    MeromorphicOn.divisor (LeanCert.Analysis.DBN.H t) univ (conj z) =
      MeromorphicOn.divisor (LeanCert.Analysis.DBN.H t) univ z := by
  simp only [divisor_univ_eq_analyticOrderNatAt_int (H_entire t), analyticOrderNatAt,
    H_analyticOrder_conj t]

/-- Conjugation of an index. -/
def cj (p : Idx t) : Idx t :=
  ⟨⟨conj p.val.1, ⟨p.val.2.val, by simpa only [divisor_conj t] using p.val.2.isLt⟩⟩,
    (map_ne_zero (starRingEnd ℂ)).mpr p.property⟩

theorem cj_involutive : Function.Involutive (cj t) := by
  rintro ⟨⟨z, k⟩, hz⟩
  apply Subtype.ext
  apply Sigma.ext (Complex.conj_conj z)
  exact (Fin.heq_ext_iff (by simp [cj])).mpr rfl

/-- Conjugation as a permutation of the index type. -/
def cjEquiv : Idx t ≃ Idx t := (cj_involutive t).toPerm

theorem cjEquiv_apply (p : Idx t) : cjEquiv t p = cj t p := rfl

theorem ζ_cj (p : Idx t) : ζ t (cj t p) = conj (ζ t p) := rfl

theorem cj_cj (p : Idx t) : cj t (cj t p) = p := cj_involutive t p

/-- Summing a summable family over conjugate indices gives the same sum. -/
theorem tsum_cj {α : Type*} [AddCommMonoid α] [TopologicalSpace α] (f : Idx t → α) :
    ∑' p, f (cj t p) = ∑' p, f p :=
  (cjEquiv t).tsum_eq f

theorem summable_cj {f : Idx t → ℝ} (hf : Summable f) : Summable fun p => f (cj t p) :=
  ((cjEquiv t).summable_iff).mpr hf

/-! ### Pairing the imaginary parts into kernels -/

/-- Real coordinates of a zero relative to the abscissa `x`: `d_p = x − Re ζ_p`, `b_p = Im ζ_p`. -/
def dd (x : ℝ) (p : Idx t) : ℝ := x - (ζ t p).re
def bb (p : Idx t) : ℝ := (ζ t p).im

theorem dd_cj (x : ℝ) (p : Idx t) : dd t x (cj t p) = dd t x p := by simp [dd, ζ_cj]
theorem bb_cj (p : Idx t) : bb t (cj t p) = -bb t p := by simp [bb, ζ_cj]

theorem K_neg_b (y d b : ℝ) : K y d (-b) = K y d b := by unfold K; ring
theorem dK_neg_b (y d b : ℝ) : dK y d (-b) = dK y d b := by unfold dK; ring
theorem K_neg_y (y d b : ℝ) : K (-y) d b = -K y d b := by unfold K; ring
theorem dK_neg_y (y d b : ℝ) : dK (-y) d b = dK y d b := by unfold dK; ring

/-- `Im T_p(z) + Im T_{p̄}(z) = −K_{Im z}(Re z − Re ζ_p, Im ζ_p)`. -/
theorem im_T_add_cj' (z : ℂ) (p : Idx t) :
    (T t p z).im + (T t (cj t p) z).im = -K z.im (dd t z.re p) (bb t p) := by
  unfold T K dd bb
  rw [ζ_cj]
  simp only [one_div, Complex.add_im, Complex.inv_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

/-- `Im T_p(x+iY) + Im T_{p̄}(x+iY) = −K_Y(d_p, b_p)`. -/
theorem im_T_add_cj (x Y : ℝ) (p : Idx t) :
    (T t p (x + Y * I)).im + (T t (cj t p) (x + Y * I)).im = -K Y (dd t x p) (bb t p) := by
  have := im_T_add_cj' t (x + Y * I) p
  simpa using this

/-- `Re(1/(x+iY−ζ_p)²) + Re(1/(x+iY−ζ_{p̄})²) = ∂_Y K_Y(d_p, b_p)`. -/
theorem re_inv_sq_add_cj (x Y : ℝ) (p : Idx t) :
    (1 / ((x + Y * I) - ζ t p) ^ 2).re + (1 / ((x + Y * I) - ζ t (cj t p)) ^ 2).re =
      dK Y (dd t x p) (bb t p) := by
  unfold dK dd bb
  rw [ζ_cj]
  simp only [one_div, Complex.inv_re, pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

/-! ### `S` as a kernel sum -/

theorem u_eq_logDeriv (x Y : ℝ) : u x Y t = logDeriv (LeanCert.Analysis.DBN.H t) (x + Y * I) := by
  unfold u; rw [logDeriv_apply, H_eq]

theorem summable_im_T {z : ℂ} (hz : LeanCert.Analysis.DBN.H t z ≠ 0) :
    Summable fun p => (T t p z).im := by
  have := Complex.imCLM.summable (summable_T t hz)
  simpa using this

theorem summable_K {x Y : ℝ} (hz : LeanCert.Analysis.DBN.H t (x + Y * I) ≠ 0) :
    Summable fun p => K Y (dd t x p) (bb t p) := by
  have h1 := summable_im_T t hz
  have h2 := summable_cj t h1
  have h3 := (h1.add h2).neg
  refine h3.congr fun p => ?_
  rw [im_T_add_cj, neg_neg]

/-- `Σ_p K_Y(d_p, b_p) = 2 S(x, Y, t)` off the zero set. -/
theorem tsum_K {x Y : ℝ} (hz : LeanCert.Analysis.DBN.H t (x + Y * I) ≠ 0) :
    ∑' p, K Y (dd t x p) (bb t p) = 2 * S x Y t := by
  have h1 := summable_im_T t hz
  have h2 := summable_cj t h1
  have hS : S x Y t = -∑' p, (T t p (x + Y * I)).im := by
    unfold S
    rw [u_eq_logDeriv, logDeriv_eq_tsum t hz, Complex.im_tsum (summable_T t hz)]
  have hpair : ∑' p, K Y (dd t x p) (bb t p) = -∑' p, ((T t p (x + Y * I)).im + (T t (cj t p) (x + Y * I)).im) := by
    rw [← tsum_neg]
    exact tsum_congr fun p => by rw [im_T_add_cj]; ring
  have hc : ∑' p, (T t (cj t p) (x + Y * I)).im = ∑' p, (T t p (x + Y * I)).im :=
    tsum_cj t (fun q => (T t q (x + Y * I)).im)
  rw [hpair, h1.tsum_add h2, hc, hS]
  ring

/-! ### Differentiating the zero sum with finitely many indices removed -/

open scoped Classical

/-- The zero sum with the indices in `F` removed. -/
def RF (F : Finset (Idx t)) (w : ℂ) : ℂ := ∑' p, if p ∈ F then 0 else T t p w

/-- Its termwise derivative. -/
def RF' (F : Finset (Idx t)) (w : ℂ) : ℂ := ∑' p, if p ∈ F then 0 else -1 / (w - ζ t p) ^ 2

theorem norm_T_le {z : ℂ} (p : Idx t) (hp : 2 * ‖z‖ ≤ ‖ζ t p‖) :
    ‖T t p z‖ ≤ 2 * ‖z‖ * ‖ζ t p‖⁻¹ ^ 2 := by
  have hζ : ζ t p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
  have hζpos : 0 < ‖ζ t p‖ := norm_pos_iff.mpr hζ
  have hdist : ‖ζ t p‖ / 2 ≤ ‖z - ζ t p‖ := by
    have := norm_sub_norm_le (ζ t p) z
    rw [norm_sub_rev] at this
    linarith
  have hne : z - ζ t p ≠ 0 := by
    intro h; rw [h, norm_zero] at hdist; linarith
  have e : T t p z = z / ((z - ζ t p) * ζ t p) := by
    unfold T; field_simp; ring
  rw [e, norm_div, norm_mul, div_le_iff₀ (by positivity)]
  have h1 : ‖z‖ * (‖ζ t p‖ / 2 * ‖ζ t p‖) ≤ ‖z‖ * (‖z - ζ t p‖ * ‖ζ t p‖) := by
    gcongr
  calc ‖z‖ = 2 * ‖z‖ * ‖ζ t p‖⁻¹ ^ 2 * (‖ζ t p‖ / 2 * ‖ζ t p‖) := by
        field_simp
    _ ≤ 2 * ‖z‖ * ‖ζ t p‖⁻¹ ^ 2 * (‖z - ζ t p‖ * ‖ζ t p‖) := by gcongr

/-- The finite set of indices with `‖ζ_p‖ ≤ R`. -/
def small (R : ℝ) : Finset (Idx t) :=
  (divisorZeroIndex₀_norm_le_finite (f := LeanCert.Analysis.DBN.H t) (U := univ) R (subset_univ _)).toFinset

theorem mem_small {R : ℝ} {p : Idx t} : p ∈ small t R ↔ ‖ζ t p‖ ≤ R := by
  simp [small]

theorem summable_ite_T (F : Finset (Idx t)) {z : ℂ} (hF : ∀ p ∉ F, ζ t p ≠ z) :
    Summable fun p => if p ∈ F then (0 : ℂ) else T t p z := by
  refine Summable.of_norm_bounded_eventually (g := fun p => 2 * ‖z‖ * ‖ζ t p‖⁻¹ ^ 2)
    ((summable_inv_sq t).mul_left _) ?_
  have hfin : ∀ᶠ p in Filter.cofinite, p ∉ small t (2 * ‖z‖) := by
    rw [Filter.eventually_cofinite]
    exact (small t (2 * ‖z‖)).finite_toSet.subset fun p hp => by simpa using hp
  filter_upwards [hfin] with p hp
  rw [mem_small, not_le] at hp
  split_ifs
  · simp only [norm_zero]; positivity
  · exact norm_T_le t p hp.le

theorem hasDerivAt_T {w : ℂ} (p : Idx t) (hw : w ≠ ζ t p) :
    HasDerivAt (T t p) (-1 / (w - ζ t p) ^ 2) w := by
  have h := ((hasDerivAt_id w).sub_const (ζ t p)).inv (sub_ne_zero.mpr hw)
  have h2 := h.add_const (1 / ζ t p)
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
  simp [T, Pi.inv_apply]

theorem norm_inv_sq_le {w a : ℂ} {r : ℝ} (hr : 0 < r) (h : r ≤ ‖w - a‖) :
    ‖-1 / (w - a) ^ 2‖ ≤ 1 / r ^ 2 := by
  rw [norm_div, norm_neg, norm_one, norm_pow]
  have : 0 < ‖w - a‖ := lt_of_lt_of_le hr h
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := pow_le_pow_left₀ hr.le h 2
  nlinarith

/-- **Derivative of the punctured zero sum.** If no index outside `F` has zero `z₀`, the sum
`RF F` is differentiable at `z₀` with derivative `RF' F z₀`. -/
theorem hasDerivAt_RF (F : Finset (Idx t)) {z₀ : ℂ} (hF : ∀ p ∉ F, ζ t p ≠ z₀) :
    HasDerivAt (RF t F) (RF' t F z₀) z₀ ∧
      Summable fun p => if p ∈ F then (0 : ℂ) else -1 / (z₀ - ζ t p) ^ 2 := by
  set R : ℝ := 2 * ‖z₀‖ + 1 with hR
  set B : Finset (Idx t) := F ∪ small t R with hB
  set D : Finset (Idx t) := B.filter (fun p => p ∉ F) with hD
  -- a positive margin to the finitely many zeros outside `F` with `‖ζ_p‖ ≤ R`
  obtain ⟨δ, hδ, hδD⟩ : ∃ δ > (0 : ℝ), ∀ p ∈ D, 2 * δ ≤ ‖z₀ - ζ t p‖ := by
    by_cases hne : D.Nonempty
    · obtain ⟨q, hq, hmin⟩ := D.exists_min_image (fun p => ‖z₀ - ζ t p‖) hne
      have hq' : q ∉ F := (Finset.mem_filter.mp hq).2
      have hpos : 0 < ‖z₀ - ζ t q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hF q hq').symm)
      exact ⟨‖z₀ - ζ t q‖ / 2, by positivity, fun p hp => by have := hmin p hp; linarith⟩
    · exact ⟨1, one_pos, fun p hp => absurd ⟨p, hp⟩ hne⟩
  set r : ℝ := min δ (1 / 4) with hr
  have hr0 : 0 < r := lt_min hδ (by norm_num)
  have hrδ : r ≤ δ := min_le_left _ _
  have hr4 : r ≤ 1 / 4 := min_le_right _ _
  -- distances from points of the ball to the zeros
  have hfar : ∀ p ∉ B, ∀ w ∈ Metric.ball z₀ r, ‖ζ t p‖ / 4 ≤ ‖w - ζ t p‖ ∧ 1 ≤ ‖ζ t p‖ := by
    intro p hp w hw
    have hpB : ¬ ‖ζ t p‖ ≤ R := fun h => hp (Finset.mem_union_right _ ((mem_small t).mpr h))
    push_neg at hpB
    have h1 : ‖ζ t p‖ - ‖z₀‖ ≤ ‖z₀ - ζ t p‖ := by
      have := norm_sub_norm_le (ζ t p) z₀; rwa [norm_sub_rev] at this
    have h2 : ‖z₀ - ζ t p‖ - ‖w - z₀‖ ≤ ‖w - ζ t p‖ := by
      have := norm_sub_norm_le (z₀ - ζ t p) (z₀ - w)
      rw [show z₀ - ζ t p - (z₀ - w) = w - ζ t p by ring, norm_sub_rev z₀ w] at this
      exact this
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have := norm_nonneg (ζ t p)
    have := norm_nonneg z₀
    constructor
    · linarith
    · linarith
  have hnear : ∀ p ∈ D, ∀ w ∈ Metric.ball z₀ r, δ ≤ ‖w - ζ t p‖ := by
    intro p hp w hw
    have h := hδD p hp
    have h2 : ‖z₀ - ζ t p‖ - ‖w - z₀‖ ≤ ‖w - ζ t p‖ := by
      have := norm_sub_norm_le (z₀ - ζ t p) (z₀ - w)
      rw [show z₀ - ζ t p - (z₀ - w) = w - ζ t p by ring, norm_sub_rev z₀ w] at this
      exact this
    rw [Metric.mem_ball, dist_eq_norm] at hw
    linarith
  -- the summable bound
  set C : ℝ := 1 / δ ^ 2 with hC
  set ub : Idx t → ℝ := fun p => if p ∈ B then C else 16 * ‖ζ t p‖⁻¹ ^ 2 with hub
  have hub_sum : Summable ub := by
    have h1 : Summable fun p : Idx t => 16 * ‖ζ t p‖⁻¹ ^ 2 := (summable_inv_sq t).mul_left 16
    have h2 : Summable fun p : Idx t => if p ∈ B then C - 16 * ‖ζ t p‖⁻¹ ^ 2 else 0 :=
      summable_of_ne_finset_zero (s := B) fun p hp => by simp [hp]
    refine (h1.add h2).congr fun p => ?_
    simp only [hub]; split_ifs <;> ring
  set g : Idx t → ℂ → ℂ := fun p w => if p ∈ F then 0 else T t p w with hg
  set g' : Idx t → ℂ → ℂ := fun p w => if p ∈ F then 0 else -1 / (w - ζ t p) ^ 2 with hg'
  have hderiv : ∀ p, ∀ w ∈ Metric.ball z₀ r, HasDerivAt (g p) (g' p w) w := by
    intro p w hw
    simp only [hg, hg']
    split_ifs with hpF
    · exact hasDerivAt_const _ _
    · apply hasDerivAt_T
      by_cases hpB : p ∈ B
      · have hpD : p ∈ D := Finset.mem_filter.mpr ⟨hpB, hpF⟩
        have := hnear p hpD w hw
        intro h; rw [h, sub_self, norm_zero] at this; linarith
      · have := (hfar p hpB w hw).1
        have hpos : 0 < ‖ζ t p‖ := norm_pos_iff.mpr (divisorZeroIndex₀_val_ne_zero p)
        intro h; rw [h, sub_self, norm_zero] at this; linarith
  have hbound : ∀ p, ∀ w ∈ Metric.ball z₀ r, ‖g' p w‖ ≤ ub p := by
    intro p w hw
    simp only [hg', hub]
    by_cases hpF : p ∈ F
    · have hpB : p ∈ B := Finset.mem_union_left _ hpF
      simp only [hpF, hpB, if_true, norm_zero]; positivity
    · simp only [hpF, if_false]
      by_cases hpB : p ∈ B
      · have hpD : p ∈ D := Finset.mem_filter.mpr ⟨hpB, hpF⟩
        simp only [hpB, if_true]
        exact norm_inv_sq_le hδ (hnear p hpD w hw)
      · simp only [hpB, if_false]
        obtain ⟨h1, h2⟩ := hfar p hpB w hw
        have hpos : 0 < ‖ζ t p‖ := by linarith
        have := norm_inv_sq_le (by positivity : 0 < ‖ζ t p‖ / 4) h1
        calc ‖-1 / (w - ζ t p) ^ 2‖ ≤ 1 / (‖ζ t p‖ / 4) ^ 2 := this
          _ = 16 * ‖ζ t p‖⁻¹ ^ 2 := by field_simp; norm_num
  have hz₀ : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr0
  have hsum0 : Summable fun p => g p z₀ := summable_ite_T t F hF
  have hmain := hasDerivAt_tsum_of_isPreconnected hub_sum Metric.isOpen_ball
    (convex_ball z₀ r).isPreconnected hderiv hbound hz₀ hsum0 hz₀
  refine ⟨hmain, ?_⟩
  exact Summable.of_norm_bounded hub_sum fun p => hbound p z₀ hz₀

/-! ### `S_Y` as a kernel sum -/

theorem RF_empty (w : ℂ) : RF t ∅ w = ∑' p, T t p w := by
  unfold RF; simp

theorem RF'_empty (w : ℂ) : RF' t ∅ w = ∑' p, -1 / (w - ζ t p) ^ 2 := by
  unfold RF'; simp

/-- `u_z = (H'/H)' = Σ_p −1/(z − ζ_p)²` off the zero set. -/
theorem uz_eq_tsum {x Y : ℝ} (hz : LeanCert.Analysis.DBN.H t (x + Y * I) ≠ 0) :
    uz x Y t = ∑' p, -1 / ((x + Y * I) - ζ t p) ^ 2 ∧
      Summable fun p => -1 / ((x + Y * I) - ζ t p) ^ 2 := by
  set z : ℂ := x + Y * I with hzdef
  have hcont : ContinuousAt (LeanCert.Analysis.DBN.H t) z := (H_entire t).continuous.continuousAt
  have hev : ∀ᶠ w in 𝓝 z, LeanCert.Analysis.DBN.H t w ≠ 0 := hcont.eventually_ne hz
  have heq : logDeriv (LeanCert.Analysis.DBN.H t) =ᶠ[𝓝 z] RF t ∅ := by
    filter_upwards [hev] with w hw
    rw [RF_empty, logDeriv_eq_tsum t hw]
  obtain ⟨hd, hs⟩ := hasDerivAt_RF t ∅ (z₀ := z) (fun p _ => (ne_ζ t hz p).symm)
  have hd' : HasDerivAt (logDeriv (LeanCert.Analysis.DBN.H t)) (RF' t ∅ z) z :=
    hd.congr_of_eventuallyEq heq
  have hH : HasDerivAt (LeanCert.Analysis.DBN.H t) (deriv (LeanCert.Analysis.DBN.H t) z) z :=
    (H_entire t z).hasDerivAt
  have hH' : HasDerivAt (deriv (LeanCert.Analysis.DBN.H t))
      (deriv (deriv (LeanCert.Analysis.DBN.H t)) z) z := by
    rw [deriv2_H_z, deriv_H_z]; exact hasDerivAt_moment_z 1 t z
  have hq := hH'.div hH hz
  have hlog : logDeriv (LeanCert.Analysis.DBN.H t) =
      deriv (LeanCert.Analysis.DBN.H t) / LeanCert.Analysis.DBN.H t := funext fun w => logDeriv_apply _ _
  rw [hlog] at hd'
  have huz : uz x Y t = (deriv (deriv (LeanCert.Analysis.DBN.H t)) z * LeanCert.Analysis.DBN.H t z -
      deriv (LeanCert.Analysis.DBN.H t) z * deriv (LeanCert.Analysis.DBN.H t) z) /
        LeanCert.Analysis.DBN.H t z ^ 2 := by
    unfold uz u
    rw [H_eq, ← hzdef]
    field_simp <;> ring
  refine ⟨?_, by simpa using hs⟩
  rw [huz, hq.unique hd', RF'_empty]

theorem summable_re_inv_sq {x Y : ℝ} (hz : LeanCert.Analysis.DBN.H t (x + Y * I) ≠ 0) :
    Summable fun p => (1 / ((x + Y * I) - ζ t p) ^ 2).re := by
  obtain ⟨_, hs⟩ := uz_eq_tsum t hz
  have := Complex.reCLM.summable hs.neg
  refine this.congr fun p => ?_
  simp only [Complex.reCLM_apply, neg_div, neg_neg]

theorem summable_dK {x Y : ℝ} (hz : LeanCert.Analysis.DBN.H t (x + Y * I) ≠ 0) :
    Summable fun p => dK Y (dd t x p) (bb t p) := by
  have h1 := summable_re_inv_sq t hz
  have h2 := summable_cj t h1
  refine (h1.add h2).congr fun p => ?_
  exact re_inv_sq_add_cj t x Y p

/-- `Σ_p ∂_Y K_Y(d_p, b_p) = 2 S_Y(x, Y, t)` off the zero set. -/
theorem tsum_dK {x Y : ℝ} (hz : LeanCert.Analysis.DBN.H t (x + Y * I) ≠ 0) :
    ∑' p, dK Y (dd t x p) (bb t p) = 2 * SY x Y t := by
  obtain ⟨huz, hs⟩ := uz_eq_tsum t hz
  have h1 := summable_re_inv_sq t hz
  have h2 := summable_cj t h1
  have hSY : SY x Y t = ∑' p, (1 / ((x + Y * I) - ζ t p) ^ 2).re := by
    unfold SY
    rw [huz, Complex.re_tsum hs, ← tsum_neg]
    exact tsum_congr fun p => by rw [neg_div, Complex.neg_re, neg_neg]
  have hc : ∑' p, (1 / ((x + Y * I) - ζ t (cj t p)) ^ 2).re =
      ∑' p, (1 / ((x + Y * I) - ζ t p) ^ 2).re :=
    tsum_cj t (fun q => (1 / ((x + Y * I) - ζ t q) ^ 2).re)
  have hpair : ∑' p, dK Y (dd t x p) (bb t p) =
      ∑' p, ((1 / ((x + Y * I) - ζ t p) ^ 2).re + (1 / ((x + Y * I) - ζ t (cj t p)) ^ 2).re) :=
    tsum_congr fun p => (re_inv_sq_add_cj t x Y p).symm
  rw [hpair, h1.tsum_add h2, hc, hSY]; ring

/-! ### The velocity at a simple zero -/

theorem order_one {ρ : ℂ} (h0 : LeanCert.Analysis.DBN.H t ρ = 0)
    (hd : deriv (LeanCert.Analysis.DBN.H t) ρ ≠ 0) :
    analyticOrderNatAt (LeanCert.Analysis.DBN.H t) ρ = 1 := by
  have h := ((H_entire t).analyticAt ρ).analyticOrderAt_eq_one_of_zero_deriv_ne_zero h0 hd
  unfold analyticOrderNatAt; rw [h]; rfl

theorem ρ_ne_zero {ρ : ℂ} (h0 : LeanCert.Analysis.DBN.H t ρ = 0) : ρ ≠ 0 := by
  intro h; rw [h] at h0; exact H_zero_ne_zero t h0

/-- The fiber of a simple zero is a single index. -/
theorem exists_fiber_singleton {ρ : ℂ} (h0 : LeanCert.Analysis.DBN.H t ρ = 0)
    (hd : deriv (LeanCert.Analysis.DBN.H t) ρ ≠ 0) :
    ∃ p₀ : Idx t, ∀ p, ζ t p = ρ ↔ p = p₀ := by
  have hcard : (divisorZeroIndex₀_fiberFinset (LeanCert.Analysis.DBN.H t) ρ).card = 1 := by
    rw [divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt (H_entire t) (ρ_ne_zero t h0)]
    exact order_one t h0 hd
  obtain ⟨p₀, hp₀⟩ := Finset.card_eq_one.mp hcard
  refine ⟨p₀, fun p => ?_⟩
  rw [← mem_divisorZeroIndex₀_fiberFinset, hp₀, Finset.mem_singleton]

/-- Splitting one index off the zero sum. -/
theorem logDeriv_eq_T_add_RF (p₀ : Idx t) {w : ℂ} (hw : LeanCert.Analysis.DBN.H t w ≠ 0) :
    logDeriv (LeanCert.Analysis.DBN.H t) w = T t p₀ w + RF t {p₀} w := by
  rw [logDeriv_eq_tsum t hw, (summable_T t hw).tsum_eq_add_tsum_ite p₀]
  unfold RF
  congr 1
  exact tsum_congr fun p => by simp [Finset.mem_singleton]

theorem iteratedDeriv_two' (f : ℂ → ℂ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- **Velocity formula.** At a simple zero `ρ`, `H''(ρ)/H'(ρ) = 2 (1/ρ + Σ_{p ≠ p₀} T_p(ρ))`. -/
theorem velocity_formula {ρ : ℂ} (h0 : LeanCert.Analysis.DBN.H t ρ = 0)
    (hd : deriv (LeanCert.Analysis.DBN.H t) ρ ≠ 0) (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) :
    deriv (deriv (LeanCert.Analysis.DBN.H t)) ρ / deriv (LeanCert.Analysis.DBN.H t) ρ =
      2 * (1 / ρ + RF t {p₀} ρ) := by
  have hp₀ : ζ t p₀ = ρ := (hfib p₀).mpr rfl
  have hF : ∀ p ∉ ({p₀} : Finset (Idx t)), ζ t p ≠ ρ := fun p hp h =>
    hp (Finset.mem_singleton.mpr ((hfib p).mp h))
  have hRF : ContinuousAt (RF t {p₀}) ρ := (hasDerivAt_RF t {p₀} hF).1.continuousAt
  have hp := ((H_entire t).analyticAt ρ).hasFPowerSeriesAt
  set g := dslope (LeanCert.Analysis.DBN.H t) ρ with hg
  have hq := hp.has_fpower_series_dslope_fslope
  have hgρ : g ρ = deriv (LeanCert.Analysis.DBN.H t) ρ := dslope_same _ _
  have hg' : deriv g ρ = deriv (deriv (LeanCert.Analysis.DBN.H t)) ρ / 2 := by
    rw [hq.deriv, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      FormalMultilinearSeries.coeff_fslope, FormalMultilinearSeries.coeff_ofScalars]
    simp only [Finset.prod_const_one, one_smul]
    norm_num [Nat.factorial, iteratedDeriv_two']
  have hgd : DifferentiableAt ℂ g ρ := hq.analyticAt.differentiableAt
  have hg_cont : ContinuousAt g ρ := hgd.continuousAt
  have hdg_cont : ContinuousAt (deriv g) ρ := (hq.analyticAt.deriv).continuousAt
  have hgne : g ρ ≠ 0 := by rw [hgρ]; exact hd
  have hlogg : ContinuousAt (logDeriv g) ρ := by
    have : logDeriv g = deriv g / g := funext fun w => logDeriv_apply _ _
    rw [this]; exact hdg_cont.div hg_cont hgne
  have hne_ev : ∀ᶠ w in 𝓝[≠] ρ, LeanCert.Analysis.DBN.H t w ≠ 0 := by
    have hfin := analyticOrderAt_ne_top_of_exists_ne_zero (H_entire t) ⟨0, H_zero_ne_zero t⟩ ρ
    exact ((H_entire t).analyticAt ρ).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun h => hfin (analyticOrderAt_eq_top.mpr h))
  have hident : (fun w => logDeriv g w) =ᶠ[𝓝[≠] ρ] (fun w => 1 / ρ + RF t {p₀} w) := by
    filter_upwards [hne_ev, eventually_mem_nhdsWithin] with w hw hwρ
    have hwρ' : w ≠ ρ := hwρ
    have hsub : w - ρ ≠ 0 := sub_ne_zero.mpr hwρ'
    have hgw : g w = LeanCert.Analysis.DBN.H t w / (w - ρ) := by
      rw [hg, dslope_of_ne _ hwρ', slope_def_field, h0, sub_zero]
    have hgd_w : HasDerivAt g ((deriv (LeanCert.Analysis.DBN.H t) w * (w - ρ) -
        LeanCert.Analysis.DBN.H t w * 1) / (w - ρ) ^ 2) w := by
      have h1 := ((H_entire t w).hasDerivAt).div ((hasDerivAt_id w).sub_const ρ) hsub
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [eventually_ne_nhds hwρ'] with v hv
      simp only [Pi.div_apply, id]
      rw [hg, dslope_of_ne _ hv, slope_def_field, h0, sub_zero]
    have hlogH := logDeriv_eq_T_add_RF t p₀ hw
    rw [logDeriv_apply] at hlogH
    unfold T at hlogH
    rw [hp₀] at hlogH
    rw [logDeriv_apply, hgd_w.deriv, hgw]
    have e : ((deriv (LeanCert.Analysis.DBN.H t) w * (w - ρ) - LeanCert.Analysis.DBN.H t w * 1) /
        (w - ρ) ^ 2) / (LeanCert.Analysis.DBN.H t w / (w - ρ)) =
        deriv (LeanCert.Analysis.DBN.H t) w / LeanCert.Analysis.DBN.H t w - 1 / (w - ρ) := by
      field_simp <;> ring
    rw [e, hlogH]; ring
  have hlim1 : Tendsto (fun w => logDeriv g w) (𝓝[≠] ρ) (𝓝 (logDeriv g ρ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds hlogg.tendsto
  have hlim2 : Tendsto (fun w => 1 / ρ + RF t {p₀} w) (𝓝[≠] ρ) (𝓝 (1 / ρ + RF t {p₀} ρ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds (tendsto_const_nhds.add hRF.tendsto)
  have heq := tendsto_nhds_unique (hlim1.congr' hident) hlim2
  rw [logDeriv_apply, hg', hgρ] at heq
  rw [← heq]
  field_simp

/-! ### The force laws at a simple highest zero -/

/-- Data of a simple highest zero `ρ` of `H_t` with `Im ρ > 0`. -/
structure HighestSimple (t : ℝ) (ρ : ℂ) : Prop where
  h0 : LeanCert.Analysis.DBN.H t ρ = 0
  hd : deriv (LeanCert.Analysis.DBN.H t) ρ ≠ 0
  hpos : 0 < ρ.im
  hhigh : ∀ z : ℂ, LeanCert.Analysis.DBN.H t z = 0 → z.im ≤ ρ.im

variable {ρ : ℂ}

theorem HighestSimple.abs_bb_le (hρ : HighestSimple t ρ) (p : Idx t) : |bb t p| ≤ ρ.im := by
  rw [abs_le]
  constructor
  · have := hρ.hhigh _ (H_ζ t (cj t p))
    rw [ζ_cj, Complex.conj_im] at this
    unfold bb; linarith
  · exact hρ.hhigh _ (H_ζ t p)

theorem HighestSimple.ne_zero_of_gt (hρ : HighestSimple t ρ) {Y : ℝ} (hY : ρ.im < Y) :
    LeanCert.Analysis.DBN.H t (ρ.re + Y * I) ≠ 0 := by
  intro h
  have := hρ.hhigh _ h
  simp at this
  linarith

theorem ne_zero_neg {x Y : ℝ} (hY : LeanCert.Analysis.DBN.H t (x + Y * I) ≠ 0) :
    LeanCert.Analysis.DBN.H t (x + (-Y : ℝ) * I) ≠ 0 := by
  have e : (x : ℂ) + ((-Y : ℝ) : ℂ) * I = conj ((x : ℂ) + Y * I) := by
    apply Complex.ext <;> simp
  rw [e, H_conj]
  exact (map_ne_zero _).mpr hY

theorem HighestSimple.conj_ne (hρ : HighestSimple t ρ) : conj ρ ≠ ρ := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith [hρ.hpos]

/-- The excluded pair of indices `{p₀, p̄₀}`. -/
def pair (p₀ : Idx t) : Finset (Idx t) := {p₀, cj t p₀}

/-- The fiber of `ρ̄` is the conjugate index. -/
theorem fiber_conj (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) (p : Idx t) :
    ζ t p = conj ρ ↔ p = cj t p₀ := by
  constructor
  · intro h
    have h1 : ζ t (cj t p) = ρ := by rw [ζ_cj, h, Complex.conj_conj]
    have h2 := (hfib _).mp h1
    rw [← h2, cj_cj]
  · intro h; rw [h, ζ_cj, (hfib p₀).mpr rfl]

theorem p₀_ne_cj (hρ : HighestSimple t ρ) (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) :
    p₀ ≠ cj t p₀ := by
  intro h
  have : ζ t p₀ = conj ρ := (fiber_conj t p₀ hfib p₀).mpr h
  rw [(hfib p₀).mpr rfl] at this
  exact HighestSimple.conj_ne t hρ this.symm

theorem mem_pair_iff (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) (p : Idx t) :
    p ∈ pair t p₀ ↔ ζ t p = ρ ∨ ζ t p = conj ρ := by
  unfold pair
  rw [Finset.mem_insert, Finset.mem_singleton, ← hfib p, ← fiber_conj t p₀ hfib p]

theorem cj_mem_pair_iff (p₀ p : Idx t) : cj t p ∈ pair t p₀ ↔ p ∈ pair t p₀ := by
  unfold pair
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · right; rw [← h, cj_cj]
    · left; exact (cj_involutive t).injective h
  · rintro (h | h)
    · right; rw [h]
    · left; rw [h, cj_cj]

theorem not_mem_pair_ne (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) {p : Idx t}
    (hp : p ∉ pair t p₀) : ζ t p ≠ ρ := fun h =>
  hp ((mem_pair_iff t p₀ hfib p).mpr (Or.inl h))

theorem dd_p₀ (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) : dd t ρ.re p₀ = 0 := by
  unfold dd; rw [(hfib p₀).mpr rfl]; ring

theorem bb_p₀ (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) : bb t p₀ = ρ.im := by
  unfold bb; rw [(hfib p₀).mpr rfl]

/-- `d_p² + (h − |b_p|)² > 0` for indices outside the pair. -/
theorem dist_pos_of_not_mem (hρ : HighestSimple t ρ) (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀)
    {p : Idx t} (hp : p ∉ pair t p₀) :
    0 < dd t ρ.re p ^ 2 + (ρ.im - |bb t p|) ^ 2 := by
  rw [mem_pair_iff t p₀ hfib] at hp
  by_contra hle
  push_neg at hle
  have hsq1 : dd t ρ.re p ^ 2 = 0 := by
    nlinarith [sq_nonneg (dd t ρ.re p), sq_nonneg (ρ.im - |bb t p|)]
  have hsq2 : (ρ.im - |bb t p|) ^ 2 = 0 := by
    nlinarith [sq_nonneg (dd t ρ.re p), sq_nonneg (ρ.im - |bb t p|)]
  have h1 : dd t ρ.re p = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hsq1
  have h2 : ρ.im - |bb t p| = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hsq2
  have h2' : |bb t p| = ρ.im := by linarith
  unfold dd at h1
  unfold bb at h2'
  rcases (abs_eq hρ.hpos.le).mp h2' with h3 | h3
  · exact hp (Or.inl (Complex.ext (by linarith) h3))
  · exact hp (Or.inr (Complex.ext (by simp; linarith) (by simp; linarith)))

theorem K_abs_b (y d b : ℝ) : K y d b = K y d |b| := by
  rcases le_or_gt 0 b with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, K_neg_b]

theorem dK_abs_b (y d b : ℝ) : dK y d b = dK y d |b| := by
  rcases le_or_gt 0 b with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, dK_neg_b]

/-! #### Splitting sums along the pair -/

theorem tsum_split {f : Idx t → ℝ} (hf : Summable f) (F : Finset (Idx t)) :
    ∑' p, f p = ∑ p ∈ F, f p + ∑' p, (if p ∈ F then 0 else f p) := by
  rw [← hf.sum_add_tsum_compl (s := F), tsum_subtype]
  congr 1
  exact tsum_congr fun p => by simp [Set.indicator_apply]

theorem summable_ite {f : Idx t → ℝ} (hf : Summable f) (F : Finset (Idx t)) :
    Summable fun p => if p ∈ F then 0 else f p :=
  (hf.indicator ((↑F : Set (Idx t))ᶜ)).congr fun p => by simp [Set.indicator_apply]

theorem sum_pair_K (hρ : HighestSimple t ρ) (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) (Y : ℝ) :
    ∑ p ∈ pair t p₀, K Y (dd t ρ.re p) (bb t p) = 2 * K Y 0 ρ.im := by
  unfold pair
  rw [Finset.sum_pair (p₀_ne_cj t hρ p₀ hfib), dd_cj, bb_cj, dd_p₀ t p₀ hfib, bb_p₀ t p₀ hfib, K_neg_b]
  ring

theorem sum_pair_dK (hρ : HighestSimple t ρ) (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) (Y : ℝ) :
    ∑ p ∈ pair t p₀, dK Y (dd t ρ.re p) (bb t p) = 2 * dK Y 0 ρ.im := by
  unfold pair
  rw [Finset.sum_pair (p₀_ne_cj t hρ p₀ hfib), dd_cj, bb_cj, dd_p₀ t p₀ hfib, bb_p₀ t p₀ hfib, dK_neg_b]
  ring

/-- `2 S(x,Y) = 2 K_Y(0,h) + Σ_{p ∉ pair} K_Y(d_p,b_p)`. -/
theorem two_S_eq (hρ : HighestSimple t ρ) (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) {Y : ℝ}
    (hY : LeanCert.Analysis.DBN.H t (ρ.re + Y * I) ≠ 0) :
    2 * S ρ.re Y t = 2 * K Y 0 ρ.im +
      ∑' p, (if p ∈ pair t p₀ then 0 else K Y (dd t ρ.re p) (bb t p)) := by
  rw [← tsum_K t hY, tsum_split t (summable_K t hY), sum_pair_K t hρ p₀ hfib]

/-- `2 S_Y(x,Y) = 2 ∂_Y K_Y(0,h) + Σ_{p ∉ pair} ∂_Y K_Y(d_p,b_p)`. -/
theorem two_SY_eq (hρ : HighestSimple t ρ) (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) {Y : ℝ}
    (hY : LeanCert.Analysis.DBN.H t (ρ.re + Y * I) ≠ 0) :
    2 * SY ρ.re Y t = 2 * dK Y 0 ρ.im +
      ∑' p, (if p ∈ pair t p₀ then 0 else dK Y (dd t ρ.re p) (bb t p)) := by
  rw [← tsum_dK t hY, tsum_split t (summable_dK t hY), sum_pair_dK t hρ p₀ hfib]

/-! #### The velocity as a kernel sum -/

theorem im_T_cj_p₀ (hρ : HighestSimple t ρ) (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) :
    (T t (cj t p₀) ρ).im = -1 / (2 * ρ.im) - (1 / ρ).im := by
  have hp₀ : ζ t p₀ = ρ := (hfib p₀).mpr rfl
  have hh := hρ.hpos
  unfold T
  rw [ζ_cj, hp₀]
  have e1 : (1 / conj ρ).im = -(1 / ρ).im := by
    rw [show (1 / conj ρ) = conj (1 / ρ) by rw [map_div₀, map_one], Complex.conj_im]
  have e : ρ - conj ρ = ((2 * ρ.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  have e2 : (1 / (ρ - conj ρ)).im = -1 / (2 * ρ.im) := by
    rw [e, one_div, Complex.inv_im, Complex.normSq_apply]
    simp
    field_simp
  rw [Complex.add_im, e1, e2]
  ring

theorem him2 (w : ℂ) : (2 * w).im = 2 * w.im := by simp [Complex.mul_im]

/-- Summability of the excluded kernel sum at the critical height, and its relation to the
imaginary parts of the excluded zero sum. -/
theorem ite_K_h (hρ : HighestSimple t ρ) (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) :
    Summable (fun p => if p ∈ pair t p₀ then (0 : ℝ) else K ρ.im (dd t ρ.re p) (bb t p)) ∧
    2 * ∑' p, (if p ∈ pair t p₀ then (0 : ℂ) else T t p ρ).im =
      -∑' p, (if p ∈ pair t p₀ then (0 : ℝ) else K ρ.im (dd t ρ.re p) (bb t p)) := by
  have hF' : ∀ p ∉ pair t p₀, ζ t p ≠ ρ := fun p hp => not_mem_pair_ne t p₀ hfib hp
  have hsumb := summable_ite_T t (pair t p₀) hF'
  set b : Idx t → ℝ := fun p => (if p ∈ pair t p₀ then (0 : ℂ) else T t p ρ).im with hb
  have hsb : Summable b := by
    have := Complex.imCLM.summable hsumb
    simpa [hb] using this
  have hsb' := summable_cj t hsb
  have hpair : ∀ p, b p + b (cj t p) =
      if p ∈ pair t p₀ then 0 else -K ρ.im (dd t ρ.re p) (bb t p) := by
    intro p
    by_cases hp : p ∈ pair t p₀
    · have hcp : cj t p ∈ pair t p₀ := (cj_mem_pair_iff t p₀ p).mpr hp
      simp [hb, hp, hcp]
    · have hcp : cj t p ∉ pair t p₀ := fun h => hp ((cj_mem_pair_iff t p₀ p).mp h)
      simp only [hb, hp, hcp, if_false]
      exact im_T_add_cj' t ρ p
  have hsumneg : Summable fun p => if p ∈ pair t p₀ then (0 : ℝ) else -K ρ.im (dd t ρ.re p) (bb t p) :=
    (hsb.add hsb').congr hpair
  have hneg : ∀ p, (if p ∈ pair t p₀ then (0 : ℝ) else -K ρ.im (dd t ρ.re p) (bb t p)) =
      -(if p ∈ pair t p₀ then (0 : ℝ) else K ρ.im (dd t ρ.re p) (bb t p)) := by
    intro p; split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · have := hsumneg.neg
    refine this.congr fun p => ?_
    rw [hneg, neg_neg]
  · have hc : ∑' p, b (cj t p) = ∑' p, b p := tsum_cj t b
    calc 2 * ∑' p, b p = ∑' p, b p + ∑' p, b (cj t p) := by rw [hc]; ring
      _ = ∑' p, (b p + b (cj t p)) := (hsb.tsum_add hsb').symm
      _ = ∑' p, (if p ∈ pair t p₀ then (0 : ℝ) else -K ρ.im (dd t ρ.re p) (bb t p)) :=
          tsum_congr hpair
      _ = -∑' p, (if p ∈ pair t p₀ then (0 : ℝ) else K ρ.im (dd t ρ.re p) (bb t p)) := by
          rw [← tsum_neg]; exact tsum_congr hneg

/-- **The velocity identity.** `zeroVel = −2 − 2h Σ_{p ∉ pair} K_h(d_p, b_p)`. -/
theorem zeroVel_eq (hρ : HighestSimple t ρ) (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) :
    zeroVel t ρ = -2 - 2 * ρ.im *
      ∑' p, (if p ∈ pair t p₀ then (0 : ℝ) else K ρ.im (dd t ρ.re p) (bb t p)) := by
  have hh := hρ.hpos
  have hF : ∀ p ∉ ({p₀} : Finset (Idx t)), ζ t p ≠ ρ := fun p hp h =>
    hp (Finset.mem_singleton.mpr ((hfib p).mp h))
  have hsum1 := summable_ite_T t {p₀} hF
  have hcj : cj t p₀ ∉ ({p₀} : Finset (Idx t)) := fun h =>
    p₀_ne_cj t hρ p₀ hfib (Finset.mem_singleton.mp h).symm
  set a : Idx t → ℝ := fun p => (if p ∈ ({p₀} : Finset (Idx t)) then (0 : ℂ) else T t p ρ).im with ha
  have hsa : Summable a := by
    have := Complex.imCLM.summable hsum1
    simpa [ha] using this
  have h1 : (RF t {p₀} ρ).im = ∑' p, a p := by unfold RF; rw [Complex.im_tsum hsum1]
  have h2 : ∑' p, a p = a (cj t p₀) + ∑' p, (if p = cj t p₀ then 0 else a p) :=
    hsa.tsum_eq_add_tsum_ite _
  have h3 : ∀ p, (if p = cj t p₀ then (0 : ℝ) else a p) =
      (if p ∈ pair t p₀ then (0 : ℂ) else T t p ρ).im := by
    intro p
    unfold pair
    by_cases hp1 : p = cj t p₀ <;> by_cases hp2 : p = p₀ <;> simp [ha, hp1, hp2]
  have hcj' : cj t p₀ ≠ p₀ := fun h => hcj (Finset.mem_singleton.mpr h)
  have h4 : a (cj t p₀) = (T t (cj t p₀) ρ).im := by simp [ha, hcj']
  obtain ⟨_, h5⟩ := ite_K_h t hρ p₀ hfib
  unfold zeroVel
  rw [H_eq, velocity_formula t hρ.h0 hρ.hd p₀ hfib, him2, Complex.add_im, h1, h2, h4,
    im_T_cj_p₀ t hρ p₀ hfib, tsum_congr h3]
  have h6 : ∑' p, (if p ∈ pair t p₀ then (0 : ℂ) else T t p ρ).im =
      -(1 / 2) * ∑' p, (if p ∈ pair t p₀ then (0 : ℝ) else K ρ.im (dd t ρ.re p) (bb t p)) := by
    linarith
  rw [h6]
  field_simp
  ring

/-! #### The three laws -/

theorem source_law (hρ : HighestSimple t ρ) (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) :
    SourceForce ρ.re ρ.im t (zeroVel t ρ) := by
  unfold SourceForce V
  have hh := hρ.hpos
  have hne3 := HighestSimple.ne_zero_of_gt t hρ (by linarith : ρ.im < 3 * ρ.im)
  have hne4 := HighestSimple.ne_zero_of_gt t hρ (by linarith : ρ.im < 4 * ρ.im)
  have hne5 := HighestSimple.ne_zero_of_gt t hρ (by linarith : ρ.im < 5 * ρ.im)
  have hS3 := two_S_eq t hρ p₀ hfib hne3
  have hS4 := two_S_eq t hρ p₀ hfib hne4
  have hS5 := two_S_eq t hρ p₀ hfib hne5
  have hK3 := summable_ite t (summable_K t hne3) (pair t p₀)
  have hK4 := summable_ite t (summable_K t hne4) (pair t p₀)
  have hK5 := summable_ite t (summable_K t hne5) (pair t p₀)
  obtain ⟨hKh, _⟩ := ite_K_h t hρ p₀ hfib
  set c : Idx t → ℝ := fun p => (15 / 14) * K (3 * ρ.im) (dd t ρ.re p) (bb t p) -
      (16 / 21) * K (4 * ρ.im) (dd t ρ.re p) (bb t p) + (1 / 6) * K (5 * ρ.im) (dd t ρ.re p) (bb t p)
    with hc
  have hsc : Summable fun p => if p ∈ pair t p₀ then (0 : ℝ) else c p := by
    refine (((hK3.mul_left (15 / 14)).sub (hK4.mul_left (16 / 21))).add (hK5.mul_left (1 / 6))).congr
      fun p => ?_
    simp only [hc]; split_ifs <;> simp
  have hlin : ∑' p, (if p ∈ pair t p₀ then (0 : ℝ) else c p) =
      (15 / 14) * ∑' p, (if p ∈ pair t p₀ then (0 : ℝ) else K (3 * ρ.im) (dd t ρ.re p) (bb t p)) -
      (16 / 21) * ∑' p, (if p ∈ pair t p₀ then (0 : ℝ) else K (4 * ρ.im) (dd t ρ.re p) (bb t p)) +
      (1 / 6) * ∑' p, (if p ∈ pair t p₀ then (0 : ℝ) else K (5 * ρ.im) (dd t ρ.re p) (bb t p)) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
      ← (hK3.mul_left (15 / 14)).tsum_sub (hK4.mul_left (16 / 21)),
      ← ((hK3.mul_left (15 / 14)).sub (hK4.mul_left (16 / 21))).tsum_add (hK5.mul_left (1 / 6))]
    exact tsum_congr fun p => by simp only [hc]; split_ifs <;> simp
  have hterm : ∀ p, (if p ∈ pair t p₀ then (0 : ℝ) else c p) ≤
      (if p ∈ pair t p₀ then (0 : ℝ) else K ρ.im (dd t ρ.re p) (bb t p)) := by
    intro p
    split_ifs with hp
    · exact le_refl _
    · simp only [hc]
      rw [K_abs_b (3 * ρ.im), K_abs_b (4 * ρ.im), K_abs_b (5 * ρ.im), K_abs_b ρ.im]
      exact threeProbe (abs_nonneg _) (HighestSimple.abs_bb_le t hρ p) hh (dist_pos_of_not_mem t hρ p₀ hfib hp)
  have key := hsc.tsum_le_tsum hterm hKh
  have hself := threeProbe_self ρ.im hh
  have h7 : 4 * ρ.im * (7 / (15 * ρ.im)) = 28 / 15 := by field_simp; ring
  rw [zeroVel_eq t hρ p₀ hfib]
  have e : 4 * ρ.im * (15 / 14 * S ρ.re (3 * ρ.im) t - 16 / 21 * S ρ.re (4 * ρ.im) t +
      1 / 6 * S ρ.re (5 * ρ.im) t) = 28 / 15 + 2 * ρ.im * ∑' p, (if p ∈ pair t p₀ then (0 : ℝ) else c p) := by
    rw [hlin]
    linear_combination (15 / 14 * 2 * ρ.im) * hS3 - (16 / 21 * 2 * ρ.im) * hS4 +
      (1 / 6 * 2 * ρ.im) * hS5 + (4 * ρ.im) * hself + h7
  have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * ρ.im)
  linarith

theorem unsigned_pos (hρ : HighestSimple t ρ) (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) {p : ℝ}
    (hp : 0 < p) (h5 : 5 * ρ.im ^ 2 ≤ p ^ 2) (hne : LeanCert.Analysis.DBN.H t (ρ.re + p * I) ≠ 0) :
    zeroVel t ρ ≤ -2 - 4 * ρ.im ^ 2 * S ρ.re p t / p + 8 * ρ.im ^ 2 / (p ^ 2 - ρ.im ^ 2) := by
  have hh := hρ.hpos
  have hhp : ρ.im < p := lt_of_pow_lt_pow_left₀ 2 hp.le (by nlinarith)
  have hS := two_S_eq t hρ p₀ hfib hne
  rw [K_self p ρ.im hhp hh] at hS
  have hK1 := summable_ite t (summable_K t hne) (pair t p₀)
  obtain ⟨hKh, _⟩ := ite_K_h t hρ p₀ hfib
  have hterm : ∀ q, (ρ.im / p) * (if q ∈ pair t p₀ then (0 : ℝ) else K p (dd t ρ.re q) (bb t q)) ≤
      (if q ∈ pair t p₀ then (0 : ℝ) else K ρ.im (dd t ρ.re q) (bb t q)) := by
    intro q
    split_ifs with hq
    · simp
    · rw [K_abs_b p, K_abs_b ρ.im]
      exact unsigned (abs_nonneg _) (HighestSimple.abs_bb_le t hρ q) hh hhp h5 (dist_pos_of_not_mem t hρ p₀ hfib hq)
  have key : (ρ.im / p) * ∑' q, (if q ∈ pair t p₀ then (0 : ℝ) else K p (dd t ρ.re q) (bb t q)) ≤
      ∑' q, (if q ∈ pair t p₀ then (0 : ℝ) else K ρ.im (dd t ρ.re q) (bb t q)) := by
    rw [← tsum_mul_left]; exact (hK1.mul_left _).tsum_le_tsum hterm hKh
  rw [zeroVel_eq t hρ p₀ hfib]
  have hden : p ^ 2 - ρ.im ^ 2 ≠ 0 := by nlinarith
  have e : -2 - 4 * ρ.im ^ 2 * S ρ.re p t / p + 8 * ρ.im ^ 2 / (p ^ 2 - ρ.im ^ 2) =
      -2 - 2 * ρ.im * ((ρ.im / p) *
        ∑' q, (if q ∈ pair t p₀ then (0 : ℝ) else K p (dd t ρ.re q) (bb t q))) := by
    have hS' : S ρ.re p t = (2 * (2 * p / (p ^ 2 - ρ.im ^ 2)) +
        ∑' q, (if q ∈ pair t p₀ then (0 : ℝ) else K p (dd t ρ.re q) (bb t q))) / 2 := by linarith
    rw [hS']
    field_simp
    ring
  rw [e]
  have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * ρ.im)
  linarith

theorem signed_pos (hρ : HighestSimple t ρ) (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) {p : ℝ}
    (hp : 0 < p) (h9 : 9 * ρ.im ^ 2 ≤ p ^ 2) (hne : LeanCert.Analysis.DBN.H t (ρ.re + p * I) ≠ 0) :
    zeroVel t ρ ≤ -2 - 4 * ρ.im * (ρ.im * (3 * p ^ 2 - ρ.im ^ 2) / (2 * p ^ 3)) *
        (S ρ.re p t - (p * (p ^ 2 - ρ.im ^ 2) / (3 * p ^ 2 - ρ.im ^ 2)) * SY ρ.re p t) +
      16 * ρ.im ^ 2 / (p ^ 2 - ρ.im ^ 2) := by
  have hh := hρ.hpos
  have hhp : ρ.im < p := lt_of_pow_lt_pow_left₀ 2 hp.le (by nlinarith)
  have hS := two_S_eq t hρ p₀ hfib hne
  have hSY := two_SY_eq t hρ p₀ hfib hne
  rw [K_self p ρ.im hhp hh] at hS
  rw [dK_self p ρ.im hhp hh] at hSY
  have hK1 := summable_ite t (summable_K t hne) (pair t p₀)
  have hK2 := summable_ite t (summable_dK t hne) (pair t p₀)
  obtain ⟨hKh, _⟩ := ite_K_h t hρ p₀ hfib
  set α : ℝ := ρ.im * (3 * p ^ 2 - ρ.im ^ 2) / (2 * p ^ 3) with hα
  set a : ℝ := p * (p ^ 2 - ρ.im ^ 2) / (3 * p ^ 2 - ρ.im ^ 2) with ha
  have hterm : ∀ q, α * ((if q ∈ pair t p₀ then (0 : ℝ) else K p (dd t ρ.re q) (bb t q)) -
      a * (if q ∈ pair t p₀ then (0 : ℝ) else dK p (dd t ρ.re q) (bb t q))) ≤
      (if q ∈ pair t p₀ then (0 : ℝ) else K ρ.im (dd t ρ.re q) (bb t q)) := by
    intro q
    split_ifs with hq
    · simp
    · rw [K_abs_b p, K_abs_b ρ.im, dK_abs_b p]
      exact signed (abs_nonneg _) (HighestSimple.abs_bb_le t hρ q) hh hhp h9 (dist_pos_of_not_mem t hρ p₀ hfib hq)
  have hsum := (hK1.sub (hK2.mul_left a)).mul_left α
  have key : α * ((∑' q, (if q ∈ pair t p₀ then (0 : ℝ) else K p (dd t ρ.re q) (bb t q))) -
      a * ∑' q, (if q ∈ pair t p₀ then (0 : ℝ) else dK p (dd t ρ.re q) (bb t q))) ≤
      ∑' q, (if q ∈ pair t p₀ then (0 : ℝ) else K ρ.im (dd t ρ.re q) (bb t q)) := by
    rw [← tsum_mul_left, ← hK1.tsum_sub (hK2.mul_left a), ← tsum_mul_left]
    exact hsum.tsum_le_tsum hterm hKh
  rw [zeroVel_eq t hρ p₀ hfib]
  have hden : p ^ 2 - ρ.im ^ 2 ≠ 0 := by nlinarith
  have hden3 : 3 * p ^ 2 - ρ.im ^ 2 ≠ 0 := by nlinarith
  have hp0 : p ≠ 0 := hp.ne'
  set sum1 := ∑' q, (if q ∈ pair t p₀ then (0 : ℝ) else K p (dd t ρ.re q) (bb t q)) with hsum1
  set sum2 := ∑' q, (if q ∈ pair t p₀ then (0 : ℝ) else dK p (dd t ρ.re q) (bb t q)) with hsum2
  have hS' : S ρ.re p t = (2 * (2 * p / (p ^ 2 - ρ.im ^ 2)) + sum1) / 2 := by linarith
  have hSY' : SY ρ.re p t = (2 * (-2 * (p ^ 2 + ρ.im ^ 2) / (p ^ 2 - ρ.im ^ 2) ^ 2) + sum2) / 2 := by
    linarith
  have e : -2 - 4 * ρ.im * α * (S ρ.re p t - a * SY ρ.re p t) + 16 * ρ.im ^ 2 / (p ^ 2 - ρ.im ^ 2) =
      -2 - 2 * ρ.im * (α * (sum1 - a * sum2)) := by
    rw [hS', hSY', hα, ha]
    field_simp
    ring
  rw [e]
  have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * ρ.im)
  linarith

/-- Sign symmetry of `S` and `S_Y` in the probe height. -/
theorem S_SY_neg {x Y : ℝ} (hY : LeanCert.Analysis.DBN.H t (x + Y * I) ≠ 0) :
    S x (-Y) t = -S x Y t ∧ SY x (-Y) t = SY x Y t := by
  have hY' := ne_zero_neg t hY
  constructor
  · have h1 := tsum_K t hY
    have h2 := tsum_K t hY'
    have h3 : ∑' p, K (-Y) (dd t x p) (bb t p) = -∑' p, K Y (dd t x p) (bb t p) := by
      rw [← tsum_neg]; exact tsum_congr fun p => K_neg_y _ _ _
    linarith
  · have h1 := tsum_dK t hY
    have h2 := tsum_dK t hY'
    have h3 : ∑' p, dK (-Y) (dd t x p) (bb t p) = ∑' p, dK Y (dd t x p) (bb t p) :=
      tsum_congr fun p => dK_neg_y _ _ _
    linarith

theorem unsigned_law (hρ : HighestSimple t ρ) (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) {p : ℝ}
    (h5 : 5 * ρ.im ^ 2 ≤ p ^ 2) (hne : LeanCert.Analysis.DBN.H t (ρ.re + p * I) ≠ 0) :
    zeroVel t ρ ≤ -2 - 4 * ρ.im ^ 2 * S ρ.re p t / p + 8 * ρ.im ^ 2 / (p ^ 2 - ρ.im ^ 2) := by
  have hh := hρ.hpos
  have hp0 : p ≠ 0 := by intro h; rw [h] at h5; nlinarith
  rcases lt_or_gt_of_ne hp0 with hneg | hpos
  · have hne' := ne_zero_neg t hne
    have hq := unsigned_pos t hρ p₀ hfib (p := -p) (by linarith) (by rw [neg_sq]; exact h5) hne'
    obtain ⟨hS, _⟩ := S_SY_neg t hne'
    rw [neg_neg] at hS
    have e : -2 - 4 * ρ.im ^ 2 * S ρ.re p t / p + 8 * ρ.im ^ 2 / (p ^ 2 - ρ.im ^ 2) =
        -2 - 4 * ρ.im ^ 2 * S ρ.re (-p) t / (-p) + 8 * ρ.im ^ 2 / ((-p) ^ 2 - ρ.im ^ 2) := by
      rw [hS]; ring
    rw [e]; exact hq
  · exact unsigned_pos t hρ p₀ hfib hpos h5 hne

theorem signed_law (hρ : HighestSimple t ρ) (p₀ : Idx t) (hfib : ∀ p, ζ t p = ρ ↔ p = p₀) {p : ℝ}
    (h9 : 9 * ρ.im ^ 2 ≤ p ^ 2) (hne : LeanCert.Analysis.DBN.H t (ρ.re + p * I) ≠ 0) :
    zeroVel t ρ ≤ -2 - 4 * ρ.im * (ρ.im * (3 * p ^ 2 - ρ.im ^ 2) / (2 * p ^ 3)) *
        (S ρ.re p t - (p * (p ^ 2 - ρ.im ^ 2) / (3 * p ^ 2 - ρ.im ^ 2)) * SY ρ.re p t) +
      16 * ρ.im ^ 2 / (p ^ 2 - ρ.im ^ 2) := by
  have hh := hρ.hpos
  have hp0 : p ≠ 0 := by intro h; rw [h] at h9; nlinarith
  rcases lt_or_gt_of_ne hp0 with hneg | hpos
  · have hne' := ne_zero_neg t hne
    have hq := signed_pos t hρ p₀ hfib (p := -p) (by linarith) (by rw [neg_sq]; exact h9) hne'
    obtain ⟨hS, hSY⟩ := S_SY_neg t hne'
    rw [neg_neg] at hS hSY
    have e : -2 - 4 * ρ.im * (ρ.im * (3 * p ^ 2 - ρ.im ^ 2) / (2 * p ^ 3)) *
        (S ρ.re p t - (p * (p ^ 2 - ρ.im ^ 2) / (3 * p ^ 2 - ρ.im ^ 2)) * SY ρ.re p t) +
        16 * ρ.im ^ 2 / (p ^ 2 - ρ.im ^ 2) =
        -2 - 4 * ρ.im * (ρ.im * (3 * (-p) ^ 2 - ρ.im ^ 2) / (2 * (-p) ^ 3)) *
        (S ρ.re (-p) t - ((-p) * ((-p) ^ 2 - ρ.im ^ 2) / (3 * (-p) ^ 2 - ρ.im ^ 2)) * SY ρ.re (-p) t) +
        16 * ρ.im ^ 2 / ((-p) ^ 2 - ρ.im ^ 2) := by
      rw [hS, hSY]; ring
    rw [e]; exact hq
  · exact signed_pos t hρ p₀ hfib hpos h9 hne

end PairSum

/-- **`PairSumForce` is a theorem.** -/
theorem pairSumForce_proved (t0 T : ℝ) : PairSumForce t0 T := by
  intro t1 _ ρ h0 _ hpos hhigh hd
  have hρ : PairSum.HighestSimple t1 ρ :=
    ⟨by rwa [H_eq] at h0, by rwa [H_eq] at hd, hpos, fun z hz => hhigh z (by rwa [H_eq])⟩
  obtain ⟨p₀, hfib⟩ := PairSum.exists_fiber_singleton t1 hρ.h0 hρ.hd
  refine ⟨PairSum.source_law t1 hρ p₀ hfib, ?_, ?_⟩
  · intro p h5 hne
    exact PairSum.unsigned_law t1 hρ p₀ hfib h5 (by rwa [H_eq] at hne)
  · intro p h9 hne
    exact PairSum.signed_law t1 hρ p₀ hfib h9 (by rwa [H_eq] at hne)

end DBN
