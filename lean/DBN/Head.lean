import Mathlib
import DBN.Premises
import DBN.External
import DBN.ZeroCount
import DBN.HermiteRoots
import DBN.HermiteForward

/-!
# The finite head: forward propagation of real zeros

The finite-head premise (`P2`) says that every zero of `H_t` with `|Re z| ≤ X` is real for
`t ∈ [0, 1/5]`. This file proves it from two concrete inputs at the ends of the argument:

* `FiniteRH`: zeros of `H_0` with `|Re z| ≤ X` are real. The normalization is
  `H_0(z) = ξ((1+iz)/2)/8`, so the corresponding zeta ordinate cutoff is `X/2 = 2999673670750`;
* `BoundaryNonvanishing`: `H_t(X + iy) ≠ 0` for `t ∈ [0, 1/5]` and `y ∈ [0, 1]` (the boundary
  certificate). Evenness and conjugation cover both vertical sides. The strip bound restricts
  zeros to `|Im| ≤ 1`; it does not by itself exclude zeros on the horizontal sides.

The propagation in `t` is continuous induction on `[0, 1/5]`
(`IsClosed.Icc_subset_of_forall_mem_nhdsWithin`):

* **closed**: a non-real zero at time `t₀` with `|Re| < X` would, by Hurwitz, force non-real zeros
  at nearby good times inside the window; `|Re| = X` is excluded by the boundary hypothesis;
* **right-open**: at a good time `t₀` the zeros in the window are finitely many real points `ρ`
  of orders `m_ρ`. For small `s > 0`, (i) `H_{t₀+s²}` has no zeros on the compact set obtained by
  removing small discs around the `ρ` (locally uniform convergence), (ii) each disc still carries
  exactly `m_ρ` zeros (`DBN.ZeroCount.count_locally_constant`), (iii) the forward Hermite splitting
  (`DBN.HermiteForward.forward_zero_near`) places a zero in each of the `m_ρ` disjoint sub-discs
  around `ρ + s λ`, `λ` ranging over the `m_ρ` distinct real roots of the model polynomial
  (`DBN.HermiteRoots.exists_roots`), so each sub-disc carries exactly one zero, which is real by
  conjugation symmetry (`DBN.ZeroCount.real_of_count_one`).
-/

noncomputable section

namespace DBN

open Set Filter Topology Metric Complex.Hadamard
open LeanCert.Analysis.DBN
open PairSum ZeroCount

local notation "ℋ" => LeanCert.Analysis.DBN.H

/-- Every zero of `H_0(z) = ξ((1+iz)/2)/8` with `|Re z| ≤ X` is real.
The corresponding zeta ordinate cutoff is `X/2`, not `X`. -/
def FiniteRH : Prop := ∀ z : ℂ, DBN.H 0 z = 0 → |z.re| ≤ Const.X → z.im = 0

/-- **Boundary nonvanishing**: `H_t(X + iy) ≠ 0` for `t ∈ [0, 1/5]` and `y ∈ [0, 1]`. -/
def BoundaryNonvanishing : Prop :=
  ∀ t ∈ Icc (0 : ℝ) (1 / 5), ∀ y ∈ Icc (0 : ℝ) 1, DBN.H t ((Const.X : ℝ) + y * Complex.I) ≠ 0

namespace Head

/-- Zeros of `H_t` with `|Re z| ≤ X` are real. -/
def Good (t : ℝ) : Prop := ∀ z : ℂ, ℋ t z = 0 → |z.re| ≤ Const.X → z.im = 0

/-! ### Consequences of the boundary hypothesis -/

theorem no_zero_on_boundary (hb : BoundaryNonvanishing) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 5))
    {z : ℂ} (hz : ℋ t z = 0) : |z.re| ≠ Const.X := by
  have key : ∀ w : ℂ, DBN.H t w = 0 → w.re = Const.X → False := by
    intro w hw hre
    have him := strip_all t ht.1 w hw
    rcases le_or_gt 0 w.im with h | h
    · apply hb t ht w.im ⟨h, (abs_le.mp him).2⟩
      have e : w = (Const.X : ℝ) + w.im * Complex.I := by
        apply Complex.ext <;> simp [hre]
      rw [← e]; exact hw
    · apply hb t ht (-w.im) ⟨by linarith, by linarith [(abs_le.mp him).1]⟩
      have e : starRingEnd ℂ w = (Const.X : ℝ) + ((-w.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hre]
      rw [← e]; exact (symm_all t w hw).2
  intro habs
  rw [← H_eq_apply] at hz
  rcases (abs_eq (Nat.cast_nonneg _)).mp habs with h | h
  · exact key z hz h
  · exact key (-z) (symm_all t z hz).1 (by simp [h])

/-! ### Finite separation -/

theorem exists_sep {α : Type*} [MetricSpace α] (Z : Finset α) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → 2 * δ ≤ dist x y := by
  classical
  set S : Finset ℝ := ((Z ×ˢ Z).filter (fun p : α × α => p.1 ≠ p.2)).image
    (fun p => dist p.1 p.2) with hS
  have hmemS : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → dist x y ∈ S := fun x hx y hy hxy =>
    Finset.mem_image.mpr ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩, rfl⟩
  by_cases hne : S.Nonempty
  · have hmin : 0 < S.min' hne := by
      obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp (Finset.min'_mem S hne)
      rw [← hpe]
      exact dist_pos.mpr (Finset.mem_filter.mp hp).2
    refine ⟨min (S.min' hne / 2) 1, lt_min (by linarith) one_pos, min_le_right _ _, ?_⟩
    intro x hx y hy hxy
    have := Finset.min'_le S _ (hmemS x hx y hy hxy)
    have := min_le_left (S.min' hne / 2) 1
    linarith
  · refine ⟨1, one_pos, le_rfl, fun x hx y hy hxy => absurd ⟨_, hmemS x hx y hy hxy⟩ hne⟩

/-! ### Exactly one zero per sub-disc -/

theorem counts_eq_one {ι : Type*} (s : Finset ι) (c : ι → ℂ) (r : ι → ℝ) {C : ℂ} {R : ℝ} (t : ℝ)
    (hsub : ∀ i ∈ s, ball (c i) (r i) ⊆ ball C R)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (ball (c i) (r i)) (ball (c j) (r j)))
    (hone : ∀ i ∈ s, 1 ≤ count t (c i) (r i)) (hcard : count t C R = s.card) :
    (∀ i ∈ s, count t (c i) (r i) = 1) ∧
      ∀ p ∈ inBall t C R, ∃ i ∈ s, p ∈ inBall t (c i) (r i) := by
  classical
  have hsum := sum_count_le t s c r hsub hdisj
  rw [hcard] at hsum
  have hdisj' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (inBall t (c i) (r i)) (inBall t (c j) (r j)) := by
    intro i hi j hj hij
    rw [Finset.disjoint_left]
    intro p hpi hpj
    rw [mem_inBall] at hpi hpj
    exact Set.disjoint_left.mp (hdisj i hi j hj hij) hpi hpj
  have hall : ∀ i ∈ s, count t (c i) (r i) = 1 := by
    intro i hi
    have h1 := Finset.add_sum_erase s (fun j => count t (c j) (r j)) hi
    have h2 := Finset.card_nsmul_le_sum (s.erase i) (fun j => count t (c j) (r j)) 1
      (fun j hj => hone j (Finset.mem_of_mem_erase hj))
    rw [Finset.card_erase_of_mem hi, smul_eq_mul, mul_one] at h2
    have h3 := hone i hi
    have h4 : 1 ≤ s.card := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  refine ⟨hall, ?_⟩
  have hU : s.biUnion (fun i => inBall t (c i) (r i)) = inBall t C R := by
    apply Finset.eq_of_subset_of_card_le
    · intro p hp
      rw [Finset.mem_biUnion] at hp
      obtain ⟨i, hi, hpi⟩ := hp
      rw [mem_inBall] at hpi ⊢
      exact hsub i hi hpi
    · rw [Finset.card_biUnion hdisj']
      show count t C R ≤ ∑ i ∈ s, count t (c i) (r i)
      rw [hcard, Finset.sum_congr rfl hall]
      simp
  intro p hp
  rw [← hU, Finset.mem_biUnion] at hp
  exact hp

/-! ### The order of a zero and the moments -/

theorem iteratedDeriv_H_eq (t : ℝ) : ∀ n : ℕ, iteratedDeriv n (ℋ t) = moment n t
  | 0 => by ext z; simp
  | n + 1 => by
    rw [iteratedDeriv_succ, iteratedDeriv_H_eq t n]
    ext z
    exact (hasDerivAt_moment_z n t z).deriv

theorem order_moment {t : ℝ} {ρ : ℂ} (hρ : ℋ t ρ = 0) :
    moment (analyticOrderNatAt (ℋ t) ρ) t ρ ≠ 0 ∧
      ∀ n < analyticOrderNatAt (ℋ t) ρ, moment n t ρ = 0 := by
  have hfin := analyticOrderAt_ne_top_of_exists_ne_zero (H_entire t) ⟨0, H_zero_ne_zero t⟩ ρ
  have h := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero ((H_entire t).analyticAt ρ)).mp
    (Nat.cast_analyticOrderNatAt hfin).symm
  simp only [iteratedDeriv_H_eq] at h
  exact ⟨h.2, h.1⟩

theorem count_eq_order {t : ℝ} {ρ : ℂ} {δ : ℝ} (hρ0 : ρ ≠ 0) (hδ : 0 < δ)
    (huniq : ∀ z : ℂ, ℋ t z = 0 → z ∈ ball ρ δ → z = ρ) :
    count t ρ δ = analyticOrderNatAt (ℋ t) ρ := by
  rw [← divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt (H_entire t) hρ0]
  unfold count
  congr 1
  ext p
  rw [mem_inBall, mem_divisorZeroIndex₀_fiberFinset]
  constructor
  · intro h; exact huniq _ (H_ζ t p) h
  · intro h
    show ζ t p ∈ ball ρ δ
    rw [show ζ t p = ρ from h]
    exact mem_ball_self hδ

theorem P_ofReal (m : ℕ) (x : ℝ) :
    HermiteForward.P m (x : ℂ) = ((HermiteRoots.Pf m x : ℝ) : ℂ) := by
  unfold HermiteForward.P HermiteRoots.Pf
  push_cast
  rfl

/-! ### The window -/

/-- The window `|Re z| ≤ X`, `|Im z| ≤ 1`. -/
def K₀ : Set ℂ := {z | |z.re| ≤ Const.X ∧ |z.im| ≤ 1}

theorem norm_le_of_mem_K₀ {z : ℂ} (hz : z ∈ K₀) : ‖z‖ ≤ Const.X + 1 :=
  (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add hz.1 hz.2)

theorem isCompact_K₀ : IsCompact K₀ := by
  have hclosed : IsClosed K₀ :=
    (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
  refine (isCompact_closedBall (0 : ℂ) (Const.X + 1)).of_isClosed_subset hclosed ?_
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  exact norm_le_of_mem_K₀ hz

/-! ### The right-open step -/

theorem forward_step {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (hg : Good t₀) : ∀ᶠ t in 𝓝[>] t₀, Good t := by
  classical
  set R : ℝ := Const.X + 2 with hR
  -- all zeros of `H_{t₀}` in the closed ball of radius `R`
  set Z : Finset ℂ := (small t₀ R).image (ζ t₀) with hZ
  have mem_Z : ∀ z, z ∈ Z ↔ ℋ t₀ z = 0 ∧ ‖z‖ ≤ R := by
    intro z; constructor
    · intro h
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
      exact ⟨H_ζ t₀ p, (mem_small t₀).mp hp⟩
    · rintro ⟨hz, hn⟩
      obtain ⟨p, hp⟩ := exists_index_of_zero t₀ hz
      exact Finset.mem_image.mpr ⟨p, (mem_small t₀).mpr (hp ▸ hn), hp⟩
  set Z₀ : Finset ℂ := Z.filter (fun z => z ∈ K₀) with hZ₀
  have mem_Z₀ : ∀ z, z ∈ Z₀ ↔ ℋ t₀ z = 0 ∧ z ∈ K₀ := by
    intro z
    rw [hZ₀, Finset.mem_filter, mem_Z]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, (norm_le_of_mem_K₀ h2).trans (by rw [hR]; linarith)⟩, h2⟩
  have hZ₀zero : ∀ ρ ∈ Z₀, ℋ t₀ ρ = 0 := fun ρ hρ => ((mem_Z₀ ρ).mp hρ).1
  -- separation radius
  obtain ⟨δ, hδ, hδ1, hsep⟩ := exists_sep Z
  have huniq : ∀ ρ ∈ Z₀, ∀ z : ℂ, ℋ t₀ z = 0 → z ∈ closedBall ρ δ → z = ρ := by
    intro ρ hρ z hz hzb
    rw [mem_Z₀] at hρ
    have h1 := norm_le_of_mem_K₀ hρ.2
    have hzZ : z ∈ Z := by
      rw [mem_Z]
      refine ⟨hz, ?_⟩
      have h2 : ‖z - ρ‖ ≤ δ := by rwa [mem_closedBall, dist_eq_norm] at hzb
      have h3 := norm_sub_norm_le z ρ
      rw [hR]; linarith
    have hρZ : ρ ∈ Z := (mem_Z ρ).mpr ⟨hρ.1, h1.trans (by rw [hR]; linarith)⟩
    by_contra hne
    have := hsep z hzZ ρ hρZ hne
    rw [mem_closedBall] at hzb
    linarith
  -- roots of the model polynomials and their separation
  have hL : ∀ ρ : ℂ, ∃ L : Finset ℝ, L.card = analyticOrderNatAt (ℋ t₀) ρ ∧
      ∀ x ∈ L, HermiteRoots.Pf (analyticOrderNatAt (ℋ t₀) ρ) x = 0 :=
    fun ρ => HermiteRoots.exists_roots _
  choose L hLcard hLroot using hL
  have hg' : ∀ ρ : ℂ, ∃ g : ℝ, 0 < g ∧ g ≤ 1 ∧ ∀ x ∈ L ρ, ∀ y ∈ L ρ, x ≠ y → 2 * g ≤ dist x y :=
    fun ρ => exists_sep (L ρ)
  choose g hgpos _hg1 hgsep using hg'
  -- the compact set where `H_{t₀}` has no zeros
  set U : Set ℂ := ⋃ ρ ∈ Z₀, ball ρ δ with hU
  have hUopen : IsOpen U := isOpen_iUnion fun ρ => isOpen_iUnion fun _ => isOpen_ball
  set K : Set ℂ := K₀ \ U with hK
  have hKc : IsCompact K := isCompact_K₀.diff hUopen
  have hKne : ∀ z ∈ K, ℋ t₀ z ≠ 0 := by
    intro z hz h0
    have hzZ₀ : z ∈ Z₀ := (mem_Z₀ z).mpr ⟨h0, hz.1⟩
    exact hz.2 (Set.mem_iUnion₂.mpr ⟨z, hzZ₀, mem_ball_self hδ⟩)
  -- the time map `s ↦ t₀ + s²`
  have htend : Tendsto (fun s : ℝ => t₀ + s ^ 2) (𝓝[>] 0) (𝓝 t₀) := by
    have hc : Continuous (fun s : ℝ => t₀ + s ^ 2) := by fun_prop
    have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hconv : TendstoLocallyUniformly (fun s : ℝ => ℋ (t₀ + s ^ 2)) (ℋ t₀) (𝓝[>] 0) :=
    H_time_tendstoLocallyUniformly htend
  -- (E1) no zeros on `K` for small `s`
  have hE1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ z ∈ K, ℋ (t₀ + s ^ 2) z ≠ 0 := by
    by_cases hKe : K.Nonempty
    · obtain ⟨z₀, hz₀, hmin⟩ := hKc.exists_isMinOn hKe
        (continuous_norm.comp (H_entire t₀).continuous).continuousOn
      have hε : 0 < ‖ℋ t₀ z₀‖ := norm_pos_iff.mpr (hKne z₀ hz₀)
      have hunif : TendstoUniformlyOn (fun s : ℝ => ℋ (t₀ + s ^ 2)) (ℋ t₀) (𝓝[>] 0) K :=
        (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp
          hconv.tendstoLocallyUniformlyOn K (subset_univ _) hKc
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif _ hε] with s hs z hz h0
      have h1 := hs z hz
      rw [h0, dist_zero_right] at h1
      have h2 : ‖ℋ t₀ z₀‖ ≤ ‖ℋ t₀ z‖ := hmin hz
      linarith
    · rw [Set.not_nonempty_iff_eq_empty] at hKe
      exact Eventually.of_forall fun s z hz => by rw [hKe] at hz; simp at hz
  -- (E2) counts in the discs around `ρ ∈ Z₀` are locally constant
  have hsph : ∀ ρ ∈ Z₀, ∀ z ∈ sphere ρ δ, ℋ t₀ z ≠ 0 := by
    intro ρ hρ z hz h0
    have := huniq ρ hρ z h0 (sphere_subset_closedBall hz)
    rw [this, mem_sphere, dist_self] at hz
    exact hδ.ne hz
  have hE2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ ρ ∈ Z₀,
      (∀ z ∈ sphere ρ δ, ℋ (t₀ + s ^ 2) z ≠ 0) ∧ count (t₀ + s ^ 2) ρ δ = count t₀ ρ δ := by
    rw [eventually_all_finset]
    intro ρ hρ
    exact htend.eventually (count_locally_constant ρ hδ (hsph ρ hρ))
  -- (E3) forward splitting: a zero near each `ρ + s λ`
  have hE3 : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ ρ ∈ Z₀, ∀ x ∈ L ρ,
      ∃ w ∈ ball (x : ℂ) (g ρ), ℋ (t₀ + s ^ 2) (ρ + s * w) = 0 := by
    rw [eventually_all_finset]
    intro ρ hρ
    rw [eventually_all_finset]
    intro x hx
    obtain ⟨hm1, hm2⟩ := order_moment (hZ₀zero ρ hρ)
    have hP : HermiteForward.P (analyticOrderNatAt (ℋ t₀) ρ) (x : ℂ) = 0 := by
      rw [P_ofReal, hLroot ρ x hx]; simp
    filter_upwards [HermiteForward.forward_zero_near hm1 hm2 hP (hgpos ρ)] with s hs
    obtain ⟨w, hw, hw0⟩ := hs
    exact ⟨w, hw, by rw [← H_eq_apply]; exact hw0⟩
  -- (E4) the sub-discs fit inside the discs
  have hE4 : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ ρ ∈ Z₀, ∀ x ∈ L ρ, s * (|x| + g ρ) < δ := by
    rw [eventually_all_finset]
    intro ρ hρ
    rw [eventually_all_finset]
    intro x hx
    have h : Tendsto (fun s : ℝ => s * (|x| + g ρ)) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun s : ℝ => s * (|x| + g ρ)) := by fun_prop
      have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    exact h.eventually (eventually_lt_nhds hδ)
  -- transfer to `t = t₀ + s²`
  have hE : ∀ᶠ s in 𝓝[>] (0 : ℝ), Good (t₀ + s ^ 2) := by
    filter_upwards [hE1, hE2, hE3, hE4, self_mem_nhdsWithin] with s hs1 hs2 hs3 hs4 hs0
    have hspos : (0 : ℝ) < s := hs0
    set t := t₀ + s ^ 2 with ht
    intro z hz hre
    have him : |z.im| ≤ 1 :=
      strip_all t (add_nonneg ht₀ (sq_nonneg s)) z (by rw [H_eq_apply]; exact hz)
    have hzK₀ : z ∈ K₀ := ⟨hre, him⟩
    have hzU : z ∈ U := by
      by_contra hnot
      exact hs1 z ⟨hzK₀, hnot⟩ hz
    obtain ⟨ρ, hρ, hzρ⟩ := Set.mem_iUnion₂.mp hzU
    have hρ0 : ℋ t₀ ρ = 0 := hZ₀zero ρ hρ
    have hρK : ρ ∈ K₀ := ((mem_Z₀ ρ).mp hρ).2
    have hρim : ρ.im = 0 := hg ρ hρ0 hρK.1
    have hρne : ρ ≠ 0 := fun h => H_zero_ne_zero t₀ (h ▸ hρ0)
    -- the count at time `t` equals the order at time `t₀`
    have hcount : count t ρ δ = (L ρ).card := by
      rw [(hs2 ρ hρ).2, hLcard ρ]
      exact count_eq_order hρne hδ fun w hw hwb => huniq ρ hρ w hw (ball_subset_closedBall hwb)
    -- the sub-discs
    set c : ℝ → ℂ := fun x => ρ + (s : ℂ) * (x : ℂ) with hc
    set r : ℝ → ℝ := fun _ => s * g ρ with hr
    have hsub : ∀ x ∈ L ρ, ball (c x) (r x) ⊆ ball ρ δ := by
      intro x hx w hw
      rw [mem_ball, dist_eq_norm] at hw ⊢
      have h1 : ‖w - ρ‖ ≤ ‖w - c x‖ + ‖c x - ρ‖ := norm_sub_le_norm_sub_add_norm_sub w (c x) ρ
      have h2 : ‖c x - ρ‖ = s * |x| := by
        simp only [hc]
        rw [show ρ + (s : ℂ) * (x : ℂ) - ρ = ((s * x : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hspos]
      have h3 := hs4 ρ hρ x hx
      simp only [hr] at hw
      linarith
    have hdisj : ∀ x ∈ L ρ, ∀ y ∈ L ρ, x ≠ y →
        Disjoint (ball (c x) (r x)) (ball (c y) (r y)) := by
      intro x hx y hy hxy
      apply ball_disjoint_ball
      simp only [hc, hr]
      rw [dist_eq_norm, show ρ + (s : ℂ) * (x : ℂ) - (ρ + (s : ℂ) * (y : ℂ)) =
          ((s * (x - y) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hspos]
      have := hgsep ρ x hx y hy hxy
      rw [Real.dist_eq] at this
      have := mul_le_mul_of_nonneg_left this hspos.le
      linarith
    have hone : ∀ x ∈ L ρ, 1 ≤ count t (c x) (r x) := by
      intro x hx
      obtain ⟨w, hw, hw0⟩ := hs3 ρ hρ x hx
      refine one_le_count_of_zero t hw0 ?_
      simp only [hc, hr]
      rw [mem_ball, dist_eq_norm,
        show ρ + (s : ℂ) * w - (ρ + (s : ℂ) * (x : ℂ)) = (s : ℂ) * (w - x) by ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos]
      rw [mem_ball, dist_eq_norm] at hw
      exact mul_lt_mul_of_pos_left hw hspos
    obtain ⟨hall, hcover⟩ := counts_eq_one (L ρ) c r t hsub hdisj hone hcount
    obtain ⟨p, hp⟩ := exists_index_of_zero t hz
    have hpB : p ∈ inBall t ρ δ := (mem_inBall t).mpr (hp ▸ hzρ)
    obtain ⟨x, hx, hpx⟩ := hcover p hpB
    have hzx : z ∈ ball (c x) (r x) := by rw [← hp]; exact (mem_inBall t).mp hpx
    have e : c x = ((ρ.re + s * x : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc, hρim]
    have h1 := hall x hx
    rw [e] at h1 hzx
    exact real_of_count_one t h1 hz hzx
  -- convert `∀ᶠ s in 𝓝[>] 0` into `∀ᶠ t in 𝓝[>] t₀` via `s = √(t − t₀)`
  have hsq : Tendsto (fun t : ℝ => Real.sqrt (t - t₀)) (𝓝[>] t₀) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have : Tendsto (fun t : ℝ => Real.sqrt (t - t₀)) (𝓝 t₀) (𝓝 (Real.sqrt (t₀ - t₀))) :=
        (Real.continuous_sqrt.comp (continuous_id.sub continuous_const)).tendsto t₀
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Real.sqrt_pos.mpr (sub_pos.mpr ht)
  filter_upwards [hsq.eventually hE, self_mem_nhdsWithin] with t ht ht'
  have hlt : t₀ < t := ht'
  rwa [Real.sq_sqrt (sub_nonneg.mpr hlt.le), add_sub_cancel] at ht

/-! ### Closedness -/

theorem closed_good (hb : BoundaryNonvanishing) :
    IsClosed ({t | Good t} ∩ Icc (0 : ℝ) (1 / 5)) := by
  rw [isClosed_iff_clusterPt]
  intro t₀ hcl
  have hIcc : t₀ ∈ Icc (0 : ℝ) (1 / 5) := by
    have : ClusterPt t₀ (𝓟 (Icc (0 : ℝ) (1 / 5))) :=
      hcl.mono (principal_mono.mpr inter_subset_right)
    have h2 := mem_closure_iff_clusterPt.mpr this
    rwa [isClosed_Icc.closure_eq] at h2
  refine ⟨?_, hIcc⟩
  intro z hz hre
  by_contra him
  have hlt : |z.re| < Const.X := lt_of_le_of_ne hre (no_zero_on_boundary hb hIcc hz)
  set r := min |z.im| (Const.X - |z.re|) with hr
  have hr0 : 0 < r := lt_min (abs_pos.mpr him) (by linarith)
  set l := 𝓝 t₀ ⊓ 𝓟 ({t | Good t} ∩ Icc (0 : ℝ) (1 / 5)) with hl
  haveI : l.NeBot := hcl.neBot
  have hconv : TendstoLocallyUniformly (fun t => ℋ t) (ℋ t₀) l :=
    H_time_tendstoLocallyUniformly (τ := id) (tendsto_id'.mpr inf_le_left)
  have hev := eventually_exists_zero_of_locally_uniform (l := l) (F := fun t => ℋ t) (f := ℋ t₀)
    (fun K _ => Eventually.of_forall fun t => (H_entire t).differentiableOn) (H_entire t₀)
    ⟨0, H_zero_ne_zero t₀⟩ hconv (U := ball z r) isOpen_ball (mem_ball_self hr0) hz
  have hmem : ∀ᶠ t in l, t ∈ {t | Good t} ∩ Icc (0 : ℝ) (1 / 5) :=
    Eventually.filter_mono inf_le_right (eventually_principal.mpr fun _ h => h)
  obtain ⟨t, ⟨w, hw, hw0⟩, hgood, _⟩ := (hev.and hmem).exists
  have hgood' : Good t := hgood
  have hwz : ‖w - z‖ < r := by rwa [mem_ball, dist_eq_norm] at hw
  have hre' : |w.re - z.re| < r :=
    lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (w - z)) hwz
  have him' : |w.im - z.im| < r :=
    lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (w - z)) hwz
  have hwre : |w.re| ≤ Const.X := by
    have := min_le_right |z.im| (Const.X - |z.re|)
    have h1 := abs_sub_abs_le_abs_sub w.re z.re
    linarith
  have hwim : w.im = 0 := hgood' w hw0 hwre
  rw [hwim, zero_sub, abs_neg] at him'
  have := min_le_left |z.im| (Const.X - |z.re|)
  linarith

/-! ### Assembly -/

theorem good_of (h0 : FiniteRH) (hb : BoundaryNonvanishing) :
    ∀ t ∈ Icc (0 : ℝ) (1 / 5), Good t := by
  have hsub := IsClosed.Icc_subset_of_forall_mem_nhdsWithin (closed_good hb) (a := 0) (b := 1 / 5)
    (show (0 : ℝ) ∈ {t | Good t} from fun z hz hre => h0 z (by rw [H_eq_apply]; exact hz) hre)
    (fun t ht => forward_step ht.2.1 ht.1)
  exact fun t ht => hsub ht

end Head

/-- The finite head (P2) follows from `FiniteRH` at `t = 0` and the boundary certificate.
The time-zero zeta ordinate cutoff is `X/2`. -/
theorem head_of_finiteRH (h0 : FiniteRH) (hb : BoundaryNonvanishing) :
    ∀ t ∈ Icc (0 : ℝ) (1 / 5), ∀ z : ℂ, H t z = 0 → |z.re| ≤ Const.X → z.im = 0 :=
  fun t ht z hz hre => Head.good_of h0 hb t ht z (by rw [← H_eq_apply]; exact hz) hre

end DBN
