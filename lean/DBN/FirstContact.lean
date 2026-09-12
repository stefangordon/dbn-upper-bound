import Mathlib
import DBN.Premises
import DBN.Algebra

/-!
# The first-contact argument (manuscript §7), formalized

**Theorem `barrier_comparison`.** Let `l` be a proper chain of rows, each satisfying `RowSpec`,
covering `[t0, T]` with `0 ≤ t0` and `T ≤ 1/5`, and let the analytic premises hold. Then every zero
`ρ` of `H_t`, `t ∈ [t0, T]`, satisfies `Im(ρ)² < Q l t`.

Proof structure (all steps are kernel-checked; only `AnalyticPremises` is assumed):
1. the violation set `F` is the projection of a compact set, hence compact; `t₁ = min F`;
2. `t₁ > t0` (strict entry); before `t₁` there is no violation;
3. at `t₁` a highest zero `ρ` exists, with `Re ρ > X` after the head exclusion and symmetry;
4. a multiple contact produces an earlier violation (backward Hermite vs. the affine barrier);
5. a simple contact has `Im(ρ)² = Q(t₁)`, and the certified row force makes the left derivative of
   `Im(γ)² − Q` negative, contradicting first contact from below.
-/

noncomputable section

namespace DBN

open Set Filter Topology

/-- Violation set: times in `[t0,T]` with a zero at or above the barrier. -/
def Viol (t0 T : ℝ) (Qb : ℝ → ℝ) : Set ℝ := {t | t ∈ Icc t0 T ∧ ∃ z : ℂ, H t z = 0 ∧ Qb t ≤ z.im ^ 2}

/-! ### The force at a contact is below the row slope -/

/-- At a contact on a source row the source law beats the slope. -/
theorem source_contact_lt {wall : Array Seg} {r : Row} {c : SourceCert} (hs : RowSpec wall r)
    (hc : r.cert = .source c) {t x h v : ℝ} (ht1 : (r.tl : ℝ) < t) (ht2 : t ≤ r.tr)
    (hh : 0 < h) (hq1 : (r.qR : ℝ) ≤ h ^ 2) (hq2 : h ^ 2 ≤ r.qL)
    (hVfloor : ∀ t' ∈ Icc (c.btl : ℝ) c.btr, ∀ h' ∈ Icc (c.hlo : ℝ) c.hhi, (c.L : ℝ) ≤ V x h' t')
    (hforce : SourceForce x h t v) : v < -r.speedR := by
  simp only [RowSpec, hc] at hs
  obtain ⟨_, hqF, _, hbtl, hbtr, hL, hhlo, hlohi, hlo2, hhi2, gate⟩ := hs
  have hbtl' : (c.btl : ℝ) ≤ t := le_trans (by exact_mod_cast hbtl) ht1.le
  have hbtr' : t ≤ c.btr := le_trans ht2 (by exact_mod_cast hbtr)
  have hlo2' : ((c.hlo : ℝ)) ^ 2 ≤ h ^ 2 := le_trans (by exact_mod_cast hlo2) hq1
  have hhi2' : h ^ 2 ≤ ((c.hhi : ℝ)) ^ 2 := le_trans hq2 (by exact_mod_cast hhi2)
  have hlo0 : (0 : ℝ) ≤ c.hlo := by exact_mod_cast hhlo.le
  have hhi0 : (0 : ℝ) ≤ c.hhi := le_trans hlo0 (by exact_mod_cast hlohi.le)
  have hhlo' : (c.hlo : ℝ) ≤ h := by nlinarith
  have hhhi' : h ≤ c.hhi := by nlinarith
  have hVL := hVfloor t ⟨hbtl', hbtr'⟩ h ⟨hhlo', hhhi'⟩
  have hL' : (0 : ℝ) < c.L := by exact_mod_cast hL
  have hqR' : (0 : ℝ) < r.qR := by
    have h1 : (Const.qFinal : ℝ) ≤ r.qR := by exact_mod_cast hqF
    have h2 : (Const.qFinal : ℝ) = 1 / 400 := by norm_num [Const.qFinal]
    linarith
  have hsp : r.speedR = (((r.qL - r.qR) / (r.tr - r.tl) : ℚ) : ℝ) := by
    unfold Row.speedR; push_cast; ring
  have hA : ((Const.sourceA : ℚ) : ℝ) = 2 / 15 := by norm_num [Const.sourceA]
  have gateR : r.speedR ≤ 2 / 15 ∨
      (2 / 15 < r.speedR ∧ (r.speedR - 2 / 15) ^ 2 < (4 * (c.L : ℝ)) ^ 2 * r.qR) := by
    unfold SourceGate at gate
    rcases gate with g | ⟨g1, g2⟩
    · left; rw [hsp, ← hA]; exact_mod_cast g
    · right; constructor
      · rw [hsp, ← hA]; exact_mod_cast g1
      · have h2 : ((((r.qL - r.qR) / (r.tr - r.tl) - Const.sourceA) ^ 2 : ℚ) : ℝ)
            < ((16 * c.L ^ 2 * r.qR : ℚ) : ℝ) := by exact_mod_cast g2
        rw [hsp, ← hA]
        push_cast at h2 ⊢
        nlinarith [h2]
  have hsq : Real.sqrt (h ^ 2) = h := Real.sqrt_sq hh.le
  have key := Algebra.source_force (a := 2 / 15) (b := 4 * (c.L : ℝ)) (w := r.speedR) (qR := r.qR)
    (q := h ^ 2) (by norm_num) (by positivity) hqR' hq1 gateR
  rw [hsq] at key
  unfold SourceForce at hforce
  have : -2 / 15 - 4 * h * V x h t ≤ -2 / 15 - 4 * h * c.L := by nlinarith
  linarith

/-- At a contact on a field row the field law beats the slope. -/
theorem field_contact_lt {wall : Array Seg} {r : Row} {c : FieldCert} (hs : RowSpec wall r)
    (hc : r.cert = .field c) {t x h v : ℝ} (ht1 : (r.tl : ℝ) < t) (ht2 : t ≤ r.tr)
    (hh : 0 < h) (hq1 : (r.qR : ℝ) ≤ h ^ 2) (hq2 : h ^ 2 ≤ r.qL)
    (hfloor : H t (x + (c.p : ℝ) * Complex.I) ≠ 0 ∧ (c.s : ℝ) < S x c.p t ∧
      (c.signed = true → J x c.p t ≤ c.c))
    (hΩ : (Const.OmegaL : ℝ) < Omega x)
    (hforceU : UnsignedForce x h t v) (hforceS : SignedForce x h t v) : v < -r.speedR := by
  simp only [RowSpec, hc] at hs
  obtain ⟨_, hqF, _, _, _, _, _, _, hp, _, _, _, _, hqLP, hmode⟩ := hs
  obtain ⟨hne, hS, hJ⟩ := hfloor
  have hp' : (0 : ℝ) < c.p := by exact_mod_cast hp
  have hqR' : (0 : ℝ) < r.qR := by
    have h1 : (Const.qFinal : ℝ) ≤ r.qR := by exact_mod_cast hqF
    have h2 : (Const.qFinal : ℝ) = 1 / 400 := by norm_num [Const.qFinal]
    linarith
  have hsp : r.speedR = (((r.qL - r.qR) / (r.tr - r.tl) : ℚ) : ℝ) := by
    unfold Row.speedR; push_cast; ring
  have hqLP' : (r.qL : ℝ) < (c.p : ℝ) ^ 2 := by exact_mod_cast hqLP
  by_cases hsg : c.signed = true
  · rw [if_pos hsg] at hmode
    unfold SignedSpec at hmode
    obtain ⟨hc0, hδ, hp35, hqMb, h9, hpL0, hgate, hk, hw⟩ := hmode
    have h9' : 9 * ((r.qL : ℝ)) ≤ (c.p : ℝ) ^ 2 := by exact_mod_cast h9
    have h9h : 9 * h ^ 2 ≤ (c.p : ℝ) ^ 2 := by linarith
    have hforce := hforceS c.p h9h hne
    set δ : ℝ := (Const.OmegaL : ℝ) - c.s with hδdef
    set L0 : ℝ := (c.c : ℝ) - δ ^ 2 with hL0def
    have hδ' : (0 : ℝ) < δ := by rw [hδdef]; exact_mod_cast hδ
    have hpL0' : (c.p : ℝ) * L0 ≤ c.s := by rw [hL0def, hδdef]; exact_mod_cast hpL0
    have hKs : ((Ks c.s c.p (c.c - (Const.OmegaL - c.s) ^ 2) r.qL : ℚ) : ℝ) = Algebra.Ks c.s c.p L0 r.qL := by
      unfold Ks Algebra.Ks; rw [hL0def, hδdef]; push_cast; ring
    have hkR : 0 < Algebra.Ks c.s c.p L0 r.qL := by rw [← hKs]; exact_mod_cast hk
    have hwR : r.speedR ≤ 2 + Algebra.Ks c.s c.p L0 r.qL * r.qR := by
      rw [hsp, ← hKs]; exact_mod_cast hw
    have hJ' := hJ hsg
    have hSY : SY x c.p t ≤ (c.c : ℝ) - (S x c.p t - Omega x) ^ 2 := by
      unfold J at hJ'
      have h1 : SY x c.p t ≤ ‖uz x c.p t‖ := by
        unfold SY
        have h2 := Complex.abs_re_le_norm (uz x c.p t)
        have h3 := neg_abs_le (uz x c.p t).re
        linarith
      nlinarith [sq_nonneg ((u x c.p t).re + Real.pi / 8)]
    set q := h ^ 2 with hqdef
    have hqP : q < (c.p : ℝ) ^ 2 := by linarith
    set a := (c.p : ℝ) * ((c.p : ℝ) ^ 2 - q) / (3 * (c.p : ℝ) ^ 2 - q) with hadef
    have ha : 0 < a := Algebra.a_pos hp' hqP
    have hamax : a ≤ (c.p : ℝ) * ((c.p : ℝ) ^ 2 - r.qR) / (3 * (c.p : ℝ) ^ 2 - r.qR) :=
      Algebra.a_antitone hp' hq1 hqP
    have hgate' : 2 * ((c.p : ℝ) * ((c.p : ℝ) ^ 2 - r.qR) / (3 * (c.p : ℝ) ^ 2 - r.qR)) * δ ≤ 1 := by
      have e : ((2 * (c.p * (c.p ^ 2 - r.qR) / (3 * c.p ^ 2 - r.qR)) * (Const.OmegaL - c.s) : ℚ) : ℝ)
          = 2 * ((c.p : ℝ) * ((c.p : ℝ) ^ 2 - r.qR) / (3 * (c.p : ℝ) ^ 2 - r.qR)) * δ := by
        rw [hδdef]; push_cast; ring
      rw [← e]; exact_mod_cast hgate
    have hgateq : 2 * a * δ ≤ 1 := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hamax (by norm_num : (0:ℝ) ≤ 2)) hδ'.le
      linarith
    have hD1 : S x c.p t - a * c.c + a * (S x c.p t - Omega x) ^ 2 ≤ S x c.p t - a * SY x c.p t := by
      have := mul_le_mul_of_nonneg_left hSY ha.le
      nlinarith
    have hD2 : (c.s : ℝ) - a * ((c.c : ℝ) - ((Const.OmegaL : ℝ) - c.s) ^ 2)
        < S x c.p t - a * c.c + a * (S x c.p t - Omega x) ^ 2 :=
      Algebra.omega_branch_strict ha (by linarith) hΩ hS.le (by rw [hδdef] at hgateq; exact hgateq)
    have hD : (c.s : ℝ) - a * L0 < S x c.p t - a * SY x c.p t := by
      rw [hL0def, hδdef]; linarith
    have key := Algebra.signed_row_force_strict (s := c.s) (p := c.p) (L0 := L0) (qR := r.qR) (qL := r.qL)
      (w := r.speedR) (h := h) (D := S x c.p t - a * SY x c.p t) hp' hh hqR' hq1 hq2 h9' hpL0' hkR hwR hD
    linarith
  · rw [if_neg hsg] at hmode
    unfold UnsignedSpec at hmode
    obtain ⟨h5, hk, hw⟩ := hmode
    have h5' : 5 * ((r.qL : ℝ)) ≤ (c.p : ℝ) ^ 2 := by exact_mod_cast h5
    have h5h : 5 * h ^ 2 ≤ (c.p : ℝ) ^ 2 := by linarith
    have hforce := hforceU c.p h5h hne
    have hKu : ((Ku c.s c.p r.qL : ℚ) : ℝ) = Algebra.Ku c.s c.p r.qL := by
      unfold Ku Algebra.Ku; push_cast; ring
    have hkR : 0 < Algebra.Ku c.s c.p r.qL := by rw [← hKu]; exact_mod_cast hk
    have hwR : r.speedR ≤ 2 + Algebra.Ku c.s c.p r.qL * r.qR := by rw [hsp, ← hKu]; exact_mod_cast hw
    have key := Algebra.unsigned_row_force (s := c.s) (p := c.p) (qR := r.qR) (q := h ^ 2) (qL := r.qL)
      (w := r.speedR) (S := S x c.p t) hp' hqR' hq1 hq2 hqLP' hkR hwR hS
    linarith

/-! ### The main theorem -/

theorem barrier_comparison {wall : Array Seg} (l : List Row) (hne : l ≠ []) (hc : Chain l)
    (hs : ∀ r ∈ l, RowSpec wall r) {t0 T : ℝ} (ht0a : ((l.head hne).tl : ℝ) ≤ t0)
    (ht0b : t0 ≤ ((l.head hne).tr : ℝ))
    (hT : T = ((l.getLast hne).tr : ℝ)) (ht0pos : 0 ≤ t0) (hT5 : T ≤ 1 / 5)
    (P : AnalyticPremises t0 T l) :
    ∀ t ∈ Icc t0 T, ∀ z : ℂ, H t z = 0 → z.im ^ 2 < Q l t := by
  have hp : Proper l := fun r hr => ⟨(hs r hr).1, (hs r hr).2.2.1⟩
  have hQc : Continuous (Q l) := continuous_Q l hc hp
  have hQge : ∀ t ∈ Icc t0 T, (1 / 400 : ℝ) ≤ Q l t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      have hr := List.head_mem hne
      exact Q_ge_qFinal hc hs hr ht0a ht0b
    · obtain ⟨r, hr, hr1, hr2⟩ := exists_row_of_mem l hne hc hp t (lt_of_le_of_lt ht0a h)
        (by rw [← hT]; exact ht.2)
      exact Q_ge_qFinal hc hs hr hr1.le hr2
  by_contra hcon
  push_neg at hcon
  obtain ⟨tv, htv, zv, hzv, hQzv⟩ := hcon
  obtain ⟨R, hR⟩ := P.confine
  -- compact witness set
  let G : Set (ℝ × ℂ) := {p | p.1 ∈ Icc t0 T ∧ H p.1 p.2 = 0 ∧ Q l p.1 ≤ p.2.im ^ 2 ∧ ‖p.2‖ ≤ R + 1}
  have hGclosed : IsClosed G := by
    have h1 : IsClosed {p : ℝ × ℂ | Q l p.1 ≤ p.2.im ^ 2} :=
      isClosed_le (hQc.comp continuous_fst) ((Complex.continuous_im.comp continuous_snd).pow 2)
    have h2 : IsClosed {p : ℝ × ℂ | ‖p.2‖ ≤ R + 1} := isClosed_le continuous_snd.norm continuous_const
    have e : G = {p : ℝ × ℂ | p.1 ∈ Icc t0 T ∧ H p.1 p.2 = 0} ∩
        ({p | Q l p.1 ≤ p.2.im ^ 2} ∩ {p | ‖p.2‖ ≤ R + 1}) := by
      ext p; simp only [G, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
    rw [e]; exact P.closed.inter (h1.inter h2)
  have hGbdd : Bornology.IsBounded G := by
    have hsub : G ⊆ Icc t0 T ×ˢ Metric.closedBall (0 : ℂ) (R + 1) := by
      intro p hp'
      exact ⟨hp'.1, by simpa [Metric.mem_closedBall] using hp'.2.2.2⟩
    exact ((Metric.isBounded_Icc t0 T).prod Metric.isBounded_closedBall).subset hsub
  have hGcpt : IsCompact G := Metric.isCompact_of_isClosed_isBounded hGclosed hGbdd
  have hwit : ∀ t ∈ Icc t0 T, ∀ z : ℂ, H t z = 0 → Q l t ≤ z.im ^ 2 → (t, z) ∈ G := by
    intro t ht z hz hQz
    have h400 := hQge t ht
    have him : 1 / 40 ≤ |z.im| := by
      by_contra hlt
      push_neg at hlt
      nlinarith [abs_nonneg z.im, sq_abs z.im]
    have hre := hR t ht z hz him
    have him1 := P.strip t (le_trans ht0pos ht.1) z hz
    have hnorm : ‖z‖ ≤ R + 1 := le_trans (Complex.norm_le_abs_re_add_abs_im z) (by linarith)
    exact ⟨ht, hz, hQz, hnorm⟩
  let F := Viol t0 T (Q l)
  have hFeq : F = Prod.fst '' G := by
    ext t; constructor
    · rintro ⟨ht, z, hz, hQz⟩; exact ⟨(t, z), hwit t ht z hz hQz, rfl⟩
    · rintro ⟨⟨t', z⟩, ⟨ht, hz, hQz, _⟩, rfl⟩; exact ⟨ht, z, hz, hQz⟩
  have hFcpt : IsCompact F := by rw [hFeq]; exact hGcpt.image continuous_fst
  have hFne : F.Nonempty := ⟨tv, htv, zv, hzv, hQzv⟩
  set t1 := sInf F with ht1def
  have ht1F : t1 ∈ F := hFcpt.sInf_mem hFne
  obtain ⟨ht1I, z1, hz1, hQz1⟩ := ht1F
  have hbefore : ∀ t ∈ Ico t0 t1, ∀ z : ℂ, H t z = 0 → z.im ^ 2 < Q l t := by
    intro t ht z hz
    by_contra hcon'
    push_neg at hcon'
    have hmem : t ∈ F := ⟨⟨ht.1, le_trans ht.2.le ht1I.2⟩, z, hz, hcon'⟩
    have := csInf_le hFcpt.isBounded.bddBelow hmem
    exact absurd ht.2 (not_lt.mpr this)
  have ht1gt : t0 < t1 := by
    rcases eq_or_lt_of_le ht1I.1 with h | h
    · exfalso; rw [← h] at hQz1 hz1; exact absurd hQz1 (not_le.mpr (P.entry z1 hz1))
    · exact h
  -- highest zero at t1
  let Z1 : Set ℂ := {z | H t1 z = 0 ∧ Q l t1 ≤ z.im ^ 2 ∧ 0 ≤ z.im}
  have hZ1ne : Z1.Nonempty := by
    rcases le_or_gt 0 z1.im with h | h
    · exact ⟨z1, hz1, hQz1, h⟩
    · refine ⟨starRingEnd ℂ z1, (P.symm t1 z1 hz1).2, by simpa using hQz1, by simp; exact h.le⟩
  have hZ1cpt : IsCompact Z1 := by
    have hcl : IsClosed Z1 := by
      have h1 : IsClosed {z : ℂ | H t1 z = 0} := by
        have hpre := P.closed.preimage (continuous_const.prodMk continuous_id : Continuous fun z : ℂ => (t1, z))
        have e : (fun z : ℂ => (t1, z)) ⁻¹' {p : ℝ × ℂ | p.1 ∈ Icc t0 T ∧ H p.1 p.2 = 0} = {z | H t1 z = 0} := by
          ext z
          simp only [Set.mem_preimage, Set.mem_setOf_eq]
          exact ⟨fun h => h.2, fun h => ⟨ht1I, h⟩⟩
        rw [← e]; exact hpre
      have h2 : IsClosed {z : ℂ | Q l t1 ≤ z.im ^ 2} := isClosed_le continuous_const (Complex.continuous_im.pow 2)
      have h3 : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
      have e : Z1 = {z | H t1 z = 0} ∩ ({z | Q l t1 ≤ z.im ^ 2} ∩ {z | 0 ≤ z.im}) := by
        ext z; simp only [Z1, Set.mem_setOf_eq, Set.mem_inter_iff]
      rw [e]; exact h1.inter (h2.inter h3)
    have hbd : Bornology.IsBounded Z1 := by
      have hsub : Z1 ⊆ Metric.closedBall (0 : ℂ) (R + 1) := by
        intro z hz
        have := hwit t1 ht1I z hz.1 hz.2.1
        simpa [Metric.mem_closedBall] using this.2.2.2
      exact Metric.isBounded_closedBall.subset hsub
    exact Metric.isCompact_of_isClosed_isBounded hcl hbd
  obtain ⟨ρ0, hρ0Z, hρ0max⟩ := hZ1cpt.exists_isMaxOn hZ1ne Complex.continuous_im.continuousOn
  obtain ⟨hρ0zero, hρ0Q, hρ0im⟩ := hρ0Z
  have hρ0pos : 0 < ρ0.im := by
    have h400 := hQge t1 ht1I
    have hsq : 0 < ρ0.im ^ 2 := by linarith
    rcases eq_or_lt_of_le hρ0im with h | h
    · rw [← h] at hsq; simp at hsq
    · exact h
  have hhighest : ∀ z : ℂ, H t1 z = 0 → z.im ≤ ρ0.im := by
    intro z hz
    by_cases hzim : 0 ≤ z.im
    · by_cases hzQ : Q l t1 ≤ z.im ^ 2
      · exact hρ0max ⟨hz, hzQ, hzim⟩
      · push_neg at hzQ
        have : z.im ^ 2 < ρ0.im ^ 2 := lt_of_lt_of_le hzQ hρ0Q
        nlinarith
    · push_neg at hzim; linarith
  have hXre : (Const.X : ℝ) < |ρ0.re| := by
    by_contra hcon'
    push_neg at hcon'
    have := P.head t1 ⟨le_trans ht0pos ht1I.1, le_trans ht1I.2 hT5⟩ ρ0 hρ0zero hcon'
    linarith
  obtain ⟨ρ, hρzero, hρim, hρre⟩ : ∃ ρ : ℂ, H t1 ρ = 0 ∧ ρ.im = ρ0.im ∧ (Const.X : ℝ) < ρ.re := by
    rcases le_or_gt 0 ρ0.re with h | h
    · exact ⟨ρ0, hρ0zero, rfl, by rwa [abs_of_nonneg h] at hXre⟩
    · refine ⟨-(starRingEnd ℂ ρ0), (P.symm t1 _ (P.symm t1 ρ0 hρ0zero).2).1, by simp, ?_⟩
      simp only [Complex.neg_re, Complex.conj_re]
      rwa [abs_of_neg h] at hXre
  have hρpos : 0 < ρ.im := hρim ▸ hρ0pos
  have hρQ : Q l t1 ≤ ρ.im ^ 2 := hρim ▸ hρ0Q
  have hρhigh : ∀ z : ℂ, H t1 z = 0 → z.im ≤ ρ.im := fun z hz => hρim ▸ hhighest z hz
  -- the row ending at (or containing) t1 on the left
  obtain ⟨r, hr, hr1, hr2⟩ := exists_row_of_mem l hne hc hp t1 (lt_of_le_of_lt ht0a ht1gt)
    (by rw [← hT]; exact ht1I.2)
  have hrs := hs r hr
  have hrp := hp r hr
  have hQr : Q l t1 = r.affineR t1 := Q_eq_on_row l hc hp r hr t1 hr1.le hr2
  have hw : 0 < r.speedR := by
    unfold Row.speedR
    have h1 : (r.tl : ℝ) < r.tr := by exact_mod_cast hrp.1
    have h2 : (r.qR : ℝ) < r.qL := by exact_mod_cast hrp.2
    apply div_pos <;> linarith
  have hQleft : ∀ ε : ℝ, 0 ≤ ε → ε ≤ t1 - r.tl → Q l (t1 - ε) = Q l t1 + r.speedR * ε := by
    intro ε hε hε'
    rw [Q_eq_on_row l hc hp r hr (t1 - ε) (by linarith) (by linarith), hQr,
      r.affineR_eq _ hrp.1, r.affineR_eq _ hrp.1]
    ring
  rcases P.dynamics t1 ⟨ht1gt, ht1I.2⟩ ρ hρzero hρre hρpos hρhigh with
    ⟨c, hcpos, C, hC0, ε0, hε0, hmult⟩ |
    ⟨ε0, hε0, γ, hγt1, hγzero, hγcont, v, hγderiv, hFsrc, hFuns, hFsgn⟩
  · -- multiple contact
    set h := ρ.im with hhdef
    have hden : 0 < 2 * h * C + r.speedR := by positivity
    set ε := min (min (ε0 / 2) ((t1 - t0) / 2))
      (min ((t1 - r.tl) / 2) ((2 * h * c / (2 * h * C + r.speedR)) ^ 2 / 2)) with hεdef
    have hεpos : 0 < ε := by
      apply lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by positivity))
    have hε1 : ε < ε0 := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
    have hε2 : ε < t1 - t0 := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)
    have hε3 : ε < t1 - r.tl := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
    have hε4 : ε < (2 * h * c / (2 * h * C + r.speedR)) ^ 2 := by
      have hpos : 0 < (2 * h * c / (2 * h * C + r.speedR)) ^ 2 := by positivity
      exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
    obtain ⟨z, hz, hzim⟩ := hmult ε ⟨hεpos, hε1⟩
    have hsqrt : (2 * h * C + r.speedR) * ε < 2 * h * c * Real.sqrt ε := by
      have h1 : Real.sqrt ε < 2 * h * c / (2 * h * C + r.speedR) := by
        rw [Real.sqrt_lt' (by positivity)]; exact hε4
      have h2 : (2 * h * C + r.speedR) * Real.sqrt ε < 2 * h * c := by
        have := mul_lt_mul_of_pos_left h1 hden
        rwa [mul_div_cancel₀ _ hden.ne'] at this
      have h4 : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hεpos.le
      have h5 : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hεpos
      have h6 := mul_lt_mul_of_pos_right h2 h5
      rw [mul_assoc, h4] at h6
      exact h6
    have hgap : 0 < c * Real.sqrt ε - C * ε := by
      have hwε : 0 ≤ r.speedR * ε := mul_nonneg hw.le hεpos.le
      have h7 : 2 * h * (c * Real.sqrt ε - C * ε) > 0 := by nlinarith
      by_contra hcon
      push_neg at hcon
      have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ 2 * h) hcon
      linarith
    have hzim' : h < z.im := by linarith
    have hviol : Q l (t1 - ε) ≤ z.im ^ 2 := by
      rw [hQleft ε hεpos.le hε3.le]
      have hz2 : h ^ 2 + 2 * h * (c * Real.sqrt ε - C * ε) ≤ z.im ^ 2 := by
        have : h + (c * Real.sqrt ε - C * ε) ≤ z.im := by linarith
        nlinarith [sq_nonneg (c * Real.sqrt ε - C * ε)]
      nlinarith
    have := hbefore (t1 - ε) ⟨by linarith, by linarith⟩ z hz
    linarith
  · -- simple contact with a left branch
    set a := max t0 (t1 - ε0) with hadef
    have ha1 : a < t1 := by rw [hadef]; exact max_lt ht1gt (by linarith)
    have hgneg : ∀ s ∈ Ico a t1, (γ s).im ^ 2 - Q l s < 0 := by
      intro s hs'
      have hs1 : s ∈ Icc (t1 - ε0) t1 := ⟨le_trans (le_max_right _ _) hs'.1, hs'.2.le⟩
      have := hbefore s ⟨le_trans (le_max_left _ _) hs'.1, hs'.2⟩ (γ s) (hγzero s hs1)
      linarith
    have hgcont : ContinuousWithinAt (fun s => (γ s).im ^ 2 - Q l s) (Ico a t1) t1 := by
      have h1 : ContinuousWithinAt γ (Icc (t1 - ε0) t1) t1 := hγcont t1 ⟨by linarith, le_refl _⟩
      have h2 : ContinuousWithinAt γ (Ico a t1) t1 :=
        h1.mono (fun s hs' => ⟨le_trans (le_max_right _ _) hs'.1, hs'.2.le⟩)
      exact ((Complex.continuous_im.continuousAt.comp_continuousWithinAt h2).pow 2).sub
        hQc.continuousWithinAt
    have hclos : t1 ∈ closure (Ico a t1) := by
      rw [closure_Ico ha1.ne]; exact ⟨ha1.le, le_refl _⟩
    have hle : (γ t1).im ^ 2 - Q l t1 ≤ 0 := by
      haveI : (𝓝[Ico a t1] t1).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hclos
      apply le_of_tendsto hgcont
      filter_upwards [self_mem_nhdsWithin] with s hs'
      exact (hgneg s hs').le
    rw [hγt1] at hle
    have hρQeq : ρ.im ^ 2 = Q l t1 := le_antisymm (by linarith) hρQ
    have hqmem := r.affineR_mem hrp.1 hrp.2 hr1.le hr2
    rw [← hQr, ← hρQeq] at hqmem
    have hforce_lt : v < -r.speedR := by
      rcases hcert : r.cert with cs | cf
      · exact source_contact_lt hrs hcert hr1 hr2 hρpos hqmem.1 hqmem.2
          (fun t' ht' h' hh' => P.sourceFloor r hr cs hcert ρ.re hρre.le t' ht' h' hh') hFsrc
      · have hcell : t1 ∈ Icc (cf.otl : ℝ) cf.otr := by
          have hs' := hrs
          simp only [RowSpec, hcert] at hs'
          obtain ⟨_, _, _, hotl, hotr, _⟩ := hs'
          exact ⟨le_trans (by exact_mod_cast hotl) hr1.le, le_trans hr2 (by exact_mod_cast hotr)⟩
        exact field_contact_lt hrs hcert hr1 hr2 hρpos hqmem.1 hqmem.2
          (P.fieldFloor r hr cf hcert ρ.re hρre.le t1 hcell) (P.omegaGap ρ.re hρre.le) hFuns hFsgn
    have hQd : HasDerivWithinAt (Q l) (-r.speedR) (Iic t1) t1 := Q_hasDerivWithinAt_Iic hc hp hr hr1 hr2
    have hgd : HasDerivWithinAt (fun s => (γ s).im ^ 2 - Q l s) (v - -r.speedR) (Iic t1) t1 :=
      hγderiv.sub hQd
    have hmax : IsLocalMaxOn (fun s => (γ s).im ^ 2 - Q l s) (Iic t1) t1 := by
      unfold IsLocalMaxOn IsMaxFilter
      have hmem : Ioc a t1 ∈ 𝓝[Iic t1] t1 := by
        apply mem_nhdsWithin.mpr
        exact ⟨Ioi a, isOpen_Ioi, ha1, fun x hx => ⟨hx.1, hx.2⟩⟩
      filter_upwards [hmem] with s hs'
      rcases eq_or_lt_of_le hs'.2 with h | h
      · rw [h]
      · have h0 : (γ t1).im ^ 2 - Q l t1 = 0 := by rw [hγt1]; linarith
        rw [h0]; exact (hgneg s ⟨hs'.1.le, h⟩).le
    have hcone : (-1 : ℝ) ∈ posTangentConeAt (Iic t1) t1 := by
      apply mem_posTangentConeAt_of_segment_subset
      intro x hx
      rw [segment_eq_uIcc] at hx
      have hx2 : x ≤ max t1 (t1 + -1) := hx.2
      have hmax' : max t1 (t1 + -1) = t1 := max_eq_left (by linarith)
      rw [hmax'] at hx2
      exact hx2
    have hnonpos := hmax.hasFDerivWithinAt_nonpos hgd.hasFDerivWithinAt hcone
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hnonpos
    linarith only [hnonpos, hforce_lt]

end DBN
