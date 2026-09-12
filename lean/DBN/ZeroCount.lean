import Mathlib
import DBN.PairSum

/-!
# Counting the zeros of `H_t` in a disc

For a disc `ball c R` whose boundary circle carries no zero of `H_t`, the number of zeros of `H_t`
inside it (with multiplicity) is the circle integral `(2πi)⁻¹ ∮ H_t'/H_t`. This is the argument
principle for `H_t`, derived from the existing Hadamard logarithmic-derivative formula:
`H_t'/H_t = Σ_p (1/(z − ζ_p) + 1/ζ_p)` is split into the finitely many terms with `‖ζ_p‖` small and a
tail that is holomorphic on a larger disc; each finite term integrates by Cauchy's formula to `2πi`
or `0`, and the tail integrates to `0` by Cauchy–Goursat.

Because the integral depends continuously on `t` and is `2πi` times an integer, the count is locally
constant in time (`count_locally_constant`).
-/

noncomputable section

namespace DBN

open Set Filter Topology Complex Complex.Hadamard Metric Real
open scoped ComplexConjugate Classical
open LeanCert.Analysis.DBN
open PairSum

namespace ZeroCount

variable (t : ℝ)

/-- The finite set of zero indices (with multiplicity) inside the open ball `ball c R`. -/
def inBall (c : ℂ) (R : ℝ) : Finset (Idx t) :=
  (small t (4 * (‖c‖ + R))).filter (fun p => ζ t p ∈ ball c R)

theorem mem_inBall {c : ℂ} {R : ℝ} {p : Idx t} : p ∈ inBall t c R ↔ ζ t p ∈ ball c R := by
  simp only [inBall, Finset.mem_filter, mem_small]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have h1 := mem_ball_iff_norm.mp h
    have h2 := norm_sub_norm_le (ζ t p) c
    have h3 := norm_nonneg c
    have h4 : (0 : ℝ) ≤ R := le_of_lt (lt_of_le_of_lt (norm_nonneg _) h1)
    linarith

/-- The number of zeros of `H_t` in `ball c R`, with multiplicity. -/
def count (c : ℂ) (R : ℝ) : ℕ := (inBall t c R).card

/-! ### Elementary circle integrals -/

theorem circleIntegral_const (a c : ℂ) (R : ℝ) : (∮ z in C(c, R), a) = 0 := by
  have h := circleIntegral.integral_sub_zpow_of_ne (n := 0) (by decide) c c R
  simp only [zpow_zero] at h
  have h2 := circleIntegral.integral_const_mul a (fun _ => (1 : ℂ)) c R
  simp only [mul_one] at h2
  rw [h2, h, mul_zero]

theorem tsum_split_c {f : Idx t → ℂ} (hf : Summable f) (F : Finset (Idx t)) :
    ∑' p, f p = ∑ p ∈ F, f p + ∑' p, (if p ∈ F then 0 else f p) := by
  rw [← hf.sum_add_tsum_compl (s := F), tsum_subtype]
  congr 1
  exact tsum_congr fun p => by simp [Set.indicator_apply]

/-- `T_p` is continuous on a set avoiding `ζ_p`. -/
theorem continuousOn_T (p : Idx t) {s : Set ℂ} (hs : ∀ z ∈ s, z ≠ ζ t p) :
    ContinuousOn (T t p) s := fun z hz => (hasDerivAt_T t p (hs z hz)).continuousAt.continuousWithinAt

/-- Cauchy's formula for one zero term: `2πi` inside, `0` outside. -/
theorem circleIntegral_T (p : Idx t) {c : ℂ} {R : ℝ} (hR : 0 < R) (hz : ζ t p ∉ sphere c R) :
    (∮ z in C(c, R), T t p z) = if ζ t p ∈ ball c R then 2 * π * I else 0 := by
  have hT : T t p = fun z => (z - ζ t p)⁻¹ + 1 / ζ t p := by
    funext z; unfold T; rw [one_div]
  by_cases hin : ζ t p ∈ ball c R
  · rw [if_pos hin, hT]
    have hcont : CircleIntegrable (fun z => (z - ζ t p)⁻¹) c R := by
      apply ContinuousOn.circleIntegrable hR.le
      refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun z hzs => ?_
      intro h
      exact hz (by rw [sub_eq_zero] at h; rw [← h]; exact hzs)
    rw [circleIntegral.integral_add hcont (continuousOn_const.circleIntegrable hR.le),
      circleIntegral.integral_sub_inv_of_mem_ball hin, circleIntegral_const, add_zero]
  · rw [if_neg hin]
    have hout : ζ t p ∉ closedBall c R := by
      intro h
      rcases (mem_closedBall.mp h).lt_or_eq with h1 | h1
      · exact hin (mem_ball.mpr h1)
      · exact hz (mem_sphere.mpr h1)
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le countable_empty
    · exact continuousOn_T t p fun z hzb h => hout (h ▸ hzb)
    · intro z hzb
      exact (hasDerivAt_T t p fun h => hout (h ▸ ball_subset_closedBall hzb.1)).differentiableAt

/-! ### The count formula -/

/-- **Argument principle for `H_t` on a disc.** -/
theorem circleIntegral_logDeriv (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hsph : ∀ z ∈ sphere c R, LeanCert.Analysis.DBN.H t z ≠ 0) :
    (∮ z in C(c, R), logDeriv (LeanCert.Analysis.DBN.H t) z) = 2 * π * I * (count t c R : ℂ) := by
  set ρ₀ : ℝ := ‖c‖ + R with hρ₀
  set B : Finset (Idx t) := small t (4 * ρ₀) with hB
  have hρ₀pos : 0 < ρ₀ := by have := norm_nonneg c; linarith
  have hζ : ∀ p : Idx t, ζ t p ∉ sphere c R := fun p hp => hsph _ hp (H_ζ t p)
  -- indices outside `B` are far from the ball of radius `2R`
  have hfar : ∀ p ∉ B, ∀ z ∈ ball c (2 * R), z ≠ ζ t p ∧ 2 * ‖z‖ ≤ ‖ζ t p‖ ∧
      ‖ζ t p‖ / 2 ≤ ‖z - ζ t p‖ := by
    intro p hp z hzb
    have h1 : ¬ ‖ζ t p‖ ≤ 4 * ρ₀ := fun h => hp ((mem_small t).mpr h)
    push_neg at h1
    have hz : ‖z‖ ≤ 2 * ρ₀ := by
      have := mem_ball_iff_norm.mp hzb
      have := norm_le_norm_add_norm_sub' z c
      have := norm_nonneg c
      linarith
    have hd : ‖ζ t p‖ / 2 ≤ ‖z - ζ t p‖ := by
      have := norm_sub_norm_le (ζ t p) z
      rw [norm_sub_rev] at this
      linarith
    refine ⟨?_, by linarith, hd⟩
    intro h; rw [h] at hz; linarith
  have hfarC : ∀ p ∉ B, ∀ z ∈ closedBall c R, z ≠ ζ t p := fun p hp z hz =>
    (hfar p hp z (closedBall_subset_ball (by linarith) hz)).1
  -- the tail `Σ_{p ∉ B} T_p` is holomorphic on `ball c (2R)`
  set tail : ℂ → ℂ := fun z => ∑' p, (if p ∈ B then (0 : ℂ) else T t p z) with htail
  set u : Idx t → ℝ := fun p => if p ∈ B then 0 else 4 * ‖ζ t p‖⁻¹ ^ 2 with hu
  have hu_sum : Summable u := summable_ite t ((summable_inv_sq t).mul_left _) B
  have hderiv : ∀ p : Idx t, ∀ z ∈ ball c (2 * R),
      HasDerivAt (fun w => if p ∈ B then (0 : ℂ) else T t p w)
        (if p ∈ B then 0 else -1 / (z - ζ t p) ^ 2) z := by
    intro p z hz
    by_cases hp : p ∈ B
    · simp only [hp, if_true]; exact hasDerivAt_const _ _
    · simp only [hp, if_false]; exact hasDerivAt_T t p (hfar p hp z hz).1
  have hbound : ∀ p : Idx t, ∀ z ∈ ball c (2 * R),
      ‖(if p ∈ B then (0 : ℂ) else -1 / (z - ζ t p) ^ 2)‖ ≤ u p := by
    intro p z hz
    simp only [hu]
    by_cases hp : p ∈ B
    · simp [hp]
    · simp only [hp, if_false]
      obtain ⟨_, _, hd⟩ := hfar p hp z hz
      have hζpos : 0 < ‖ζ t p‖ := norm_pos_iff.mpr (divisorZeroIndex₀_val_ne_zero p)
      have := norm_inv_sq_le (by positivity : 0 < ‖ζ t p‖ / 2) hd
      calc ‖-1 / (z - ζ t p) ^ 2‖ ≤ 1 / (‖ζ t p‖ / 2) ^ 2 := this
        _ = 4 * ‖ζ t p‖⁻¹ ^ 2 := by field_simp <;> norm_num
  have hsum0 : Summable fun p => if p ∈ B then (0 : ℂ) else T t p c :=
    summable_ite_T t B fun p hp => (hfar p hp c (mem_ball_self (by linarith))).1.symm
  have htail_diff : ∀ z ∈ ball c (2 * R), DifferentiableAt ℂ tail z := fun z hz =>
    (hasDerivAt_tsum_of_isPreconnected hu_sum isOpen_ball (convex_ball c (2 * R)).isPreconnected
      hderiv hbound (mem_ball_self (by linarith)) hsum0 hz).differentiableAt
  have htail_zero : (∮ z in C(c, R), tail z) = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le countable_empty
    · exact fun z hz => (htail_diff z (closedBall_subset_ball (by linarith) hz)).continuousAt.continuousWithinAt
    · exact fun z hz => htail_diff z (ball_subset_ball (by linarith) hz.1)
  have hcont_tail : ContinuousOn tail (sphere c R) := fun z hz =>
    (htail_diff z (closedBall_subset_ball (by linarith) (sphere_subset_closedBall hz))).continuousAt.continuousWithinAt
  have hcontT : ∀ p : Idx t, ContinuousOn (T t p) (sphere c R) :=
    fun p => continuousOn_T t p fun z hz h => hζ p (h ▸ hz)
  -- the log-derivative equals finite part + tail on the sphere
  have hsplit : EqOn (logDeriv (LeanCert.Analysis.DBN.H t))
      (fun z => ∑ p ∈ B, T t p z + tail z) (sphere c R) := by
    intro z hz
    rw [logDeriv_eq_tsum t (hsph z hz), tsum_split_c t (summable_T t (hsph z hz)) B]
  rw [circleIntegral.integral_congr hR.le hsplit,
    circleIntegral.integral_add ((continuousOn_finset_sum B fun p _ => hcontT p).circleIntegrable hR.le)
      (hcont_tail.circleIntegrable hR.le),
    htail_zero, add_zero,
    circleIntegral.integral_fun_sum fun p _ => (hcontT p).circleIntegrable hR.le]
  have hterms : ∀ p ∈ B, (∮ z in C(c, R), T t p z) =
      2 * π * I * (if ζ t p ∈ ball c R then 1 else 0) := by
    intro p _
    rw [circleIntegral_T t p hR (hζ p)]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterms, ← Finset.mul_sum, Finset.sum_boole]
  simp only [count, inBall, hB, hρ₀]

/-! ### Local constancy in time -/

theorem logDeriv_jointly_continuous {t₀ : ℝ} {z₀ : ℂ} (h : LeanCert.Analysis.DBN.H t₀ z₀ ≠ 0) :
    ContinuousAt (fun q : ℝ × ℂ => logDeriv (LeanCert.Analysis.DBN.H q.1) q.2) (t₀, z₀) := by
  have e : (fun q : ℝ × ℂ => logDeriv (LeanCert.Analysis.DBN.H q.1) q.2) =
      fun q : ℝ × ℂ => moment 1 q.1 q.2 / LeanCert.Analysis.DBN.H q.1 q.2 := by
    funext q; rw [logDeriv_apply, deriv_H_z]
  rw [e]
  exact ((continuous_moment 1).continuousAt).div (continuous_H.continuousAt) h

theorem continuousOn_logDeriv_sphere {t : ℝ} {c : ℂ} {R : ℝ}
    (hsph : ∀ z ∈ sphere c R, LeanCert.Analysis.DBN.H t z ≠ 0) :
    ContinuousOn (logDeriv (LeanCert.Analysis.DBN.H t)) (sphere c R) := by
  intro z hz
  have := (logDeriv_jointly_continuous (hsph z hz)).comp
    (continuous_const.prodMk continuous_id).continuousAt
  exact this.continuousWithinAt

/-- The count is constant for `t` near `t₀` when the circle is zero-free at `t₀`. -/
theorem count_locally_constant (c : ℂ) {R : ℝ} (hR : 0 < R) {t₀ : ℝ}
    (hsph : ∀ z ∈ sphere c R, LeanCert.Analysis.DBN.H t₀ z ≠ 0) :
    ∀ᶠ t in 𝓝 t₀, (∀ z ∈ sphere c R, LeanCert.Analysis.DBN.H t z ≠ 0) ∧ count t c R = count t₀ c R := by
  obtain ⟨M, hM⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn
    (continuousOn_logDeriv_sphere hsph)
  -- the tube lemma: nonvanishing and the bound persist for `t` near `t₀`
  have htube : ∀ᶠ t in 𝓝 t₀, ∀ z ∈ sphere c R,
      LeanCert.Analysis.DBN.H t z ≠ 0 ∧ ‖logDeriv (LeanCert.Analysis.DBN.H t) z‖ ≤ M + 1 := by
    apply (isCompact_sphere c R).eventually_forall_of_forall_eventually
    intro z hz
    have h1 : ∀ᶠ q : ℝ × ℂ in 𝓝 (t₀, z), LeanCert.Analysis.DBN.H q.1 q.2 ≠ 0 :=
      continuous_H.continuousAt.eventually_ne (hsph z hz)
    have h2 : ∀ᶠ q : ℝ × ℂ in 𝓝 (t₀, z), ‖logDeriv (LeanCert.Analysis.DBN.H q.1) q.2‖ < M + 1 := by
      have hc := logDeriv_jointly_continuous (hsph z hz)
      have hlt : ‖logDeriv (LeanCert.Analysis.DBN.H t₀) z‖ < M + 1 := by linarith [hM z hz]
      exact hc.eventually (isOpen_lt continuous_norm continuous_const |>.mem_nhds hlt)
    filter_upwards [h1, h2] with q hq1 hq2
    exact ⟨hq1, hq2.le⟩
  -- the circle integral is continuous in `t`
  set I' : ℝ → ℂ := fun t => ∮ z in C(c, R), logDeriv (LeanCert.Analysis.DBN.H t) z with hI'
  have hIcont : ContinuousAt I' t₀ := by
    have e : I' = fun t => ∫ θ in (0 : ℝ)..(2 * π),
        deriv (circleMap c R) θ • logDeriv (LeanCert.Analysis.DBN.H t) (circleMap c R θ) := by
      funext t; rfl
    rw [e]
    refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => R * (M + 1))
      ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [htube] with t ht
      apply Continuous.aestronglyMeasurable
      have hc1 : Continuous fun θ => deriv (circleMap c R) θ := by
        simp only [deriv_circleMap]; exact (continuous_circleMap 0 R).mul continuous_const
      have hc2 : Continuous fun θ => logDeriv (LeanCert.Analysis.DBN.H t) (circleMap c R θ) :=
        (continuousOn_logDeriv_sphere fun z hz => (ht z hz).1).comp_continuous
          (continuous_circleMap c R) (fun θ => circleMap_mem_sphere c hR.le θ)
      exact hc1.smul hc2
    · filter_upwards [htube] with t ht
      refine Eventually.of_forall fun θ _ => ?_
      rw [norm_smul, deriv_circleMap, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero,
        abs_of_pos hR]
      exact mul_le_mul_of_nonneg_left (ht _ (circleMap_mem_sphere c hR.le θ)).2 hR.le
    · refine Eventually.of_forall fun θ _ => ?_
      have hz := circleMap_mem_sphere c hR.le θ
      have := ContinuousAt.comp (f := fun s : ℝ => (s, circleMap c R θ)) (x := t₀)
        (logDeriv_jointly_continuous (hsph _ hz)) (continuous_id.prodMk continuous_const).continuousAt
      show ContinuousAt (fun s : ℝ => deriv (circleMap c R) θ *
        logDeriv (LeanCert.Analysis.DBN.H s) (circleMap c R θ)) t₀
      exact continuousAt_const.mul this
  -- the integral is `2πi · count`, so the count cannot jump
  have hform : ∀ᶠ t in 𝓝 t₀, I' t = 2 * π * I * (count t c R : ℂ) := by
    filter_upwards [htube] with t ht
    exact circleIntegral_logDeriv t c hR fun z hz => (ht z hz).1
  have hI₀ : I' t₀ = 2 * π * I * (count t₀ c R : ℂ) := circleIntegral_logDeriv t₀ c hR hsph
  have hev : ∀ᶠ t in 𝓝 t₀, dist (I' t) (I' t₀) < π :=
    Metric.tendsto_nhds.mp hIcont.tendsto π Real.pi_pos
  filter_upwards [htube, hform, hev] with t ht hf he
  refine ⟨fun z hz => (ht z hz).1, ?_⟩
  rw [dist_eq_norm, hf, hI₀, ← mul_sub] at he
  have hcast : ((count t c R : ℂ) - (count t₀ c R : ℂ)) =
      (((count t c R : ℤ) - (count t₀ c R : ℤ) : ℤ) : ℂ) := by push_cast; ring
  rw [hcast, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_intCast,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos] at he
  norm_num at he
  have hπ := Real.pi_pos
  have hlt' : |(count t c R : ℝ) - (count t₀ c R : ℝ)| < 1 := by nlinarith
  have hlt : |((count t c R : ℤ) - (count t₀ c R : ℤ) : ℤ)| < 1 := by
    have h' : ((|((count t c R : ℤ) - (count t₀ c R : ℤ) : ℤ)| : ℤ) : ℝ) < 1 := by
      push_cast; exact hlt'
    exact_mod_cast h'
  have := Int.abs_lt_one_iff.mp hlt
  omega

/-! ### Counting lemmas used by the head argument -/

/-- A zero of `H_t` carries at least one index. -/
theorem exists_index_of_zero {z : ℂ} (hz : LeanCert.Analysis.DBN.H t z = 0) : ∃ p : Idx t, ζ t p = z := by
  have hz0 : z ≠ 0 := fun h => H_zero_ne_zero t (h ▸ hz)
  have hcard := divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt (H_entire t) hz0
  have hord : analyticOrderNatAt (LeanCert.Analysis.DBN.H t) z ≠ 0 := by
    intro h0
    have hfin := analyticOrderAt_ne_top_of_exists_ne_zero (H_entire t) ⟨0, H_zero_ne_zero t⟩ z
    have h1 : analyticOrderAt (LeanCert.Analysis.DBN.H t) z = 0 := by
      rw [← Nat.cast_analyticOrderNatAt hfin, h0]; rfl
    rw [analyticOrderAt_eq_zero] at h1
    rcases h1 with h | h
    · exact h ((H_entire t).analyticAt z)
    · exact h hz
  have hne : (divisorZeroIndex₀_fiberFinset (LeanCert.Analysis.DBN.H t) z).Nonempty := by
    rw [← Finset.card_pos, hcard]; exact Nat.pos_of_ne_zero hord
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, (mem_divisorZeroIndex₀_fiberFinset _ _ _).mp hp⟩

theorem one_le_count_of_zero {c : ℂ} {R : ℝ} {z : ℂ} (hz : LeanCert.Analysis.DBN.H t z = 0)
    (hzb : z ∈ ball c R) : 1 ≤ count t c R := by
  obtain ⟨p, hp⟩ := exists_index_of_zero t hz
  exact Finset.card_pos.mpr ⟨p, (mem_inBall t).mpr (hp ▸ hzb)⟩

/-- Counts over pairwise disjoint sub-balls add up to at most the count of the enclosing ball. -/
theorem sum_count_le {ι : Type*} (s : Finset ι) (c : ι → ℂ) (r : ι → ℝ) {C : ℂ} {R : ℝ}
    (hsub : ∀ i ∈ s, ball (c i) (r i) ⊆ ball C R)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (ball (c i) (r i)) (ball (c j) (r j))) :
    ∑ i ∈ s, count t (c i) (r i) ≤ count t C R := by
  unfold count
  rw [← Finset.card_biUnion]
  · apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨i, hi, hpi⟩ := hp
    rw [mem_inBall] at hpi ⊢
    exact hsub i hi hpi
  · intro i hi j hj hij
    show Disjoint (inBall t (c i) (r i)) (inBall t (c j) (r j))
    rw [Finset.disjoint_left]
    intro p hpi hpj
    rw [mem_inBall] at hpi hpj
    exact Set.disjoint_left.mp (hdisj i hi j hj hij) hpi hpj

/-- If a ball around a real center contains exactly one zero index, that zero is real. -/
theorem real_of_count_one {x R : ℝ} (h1 : count t (x : ℂ) R = 1) {z : ℂ}
    (hz : LeanCert.Analysis.DBN.H t z = 0) (hzb : z ∈ ball (x : ℂ) R) : z.im = 0 := by
  obtain ⟨p, hp⟩ := exists_index_of_zero t hz
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp h1
  have hp_mem : p ∈ inBall t (x : ℂ) R := (mem_inBall t).mpr (hp ▸ hzb)
  have hcj_mem : cj t p ∈ inBall t (x : ℂ) R := by
    rw [mem_inBall, ζ_cj, hp]
    rw [mem_ball_iff_norm] at hzb ⊢
    have e : conj z - (x : ℂ) = conj (z - x) := by simp
    rw [e, Complex.norm_conj]; exact hzb
  rw [hq, Finset.mem_singleton] at hp_mem hcj_mem
  have hfix : cj t p = p := by rw [hcj_mem, hp_mem]
  have hζ : ζ t (cj t p) = ζ t p := by rw [hfix]
  rw [ζ_cj, hp] at hζ
  have := congrArg Complex.im hζ
  simp at this
  linarith

end ZeroCount

end DBN
