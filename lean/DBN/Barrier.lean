import Mathlib
import DBN.Certificate

/-!
# The piecewise-affine barrier `Q`

`Q rows t` is the continuous piecewise-affine function defined by a chained list of rows:
on the row `[tl, tr]` it is the affine interpolation between `(tl, qL)` and `(tr, qR)`; to the left of
the first row it extends the first row affinely, to the right of the last row it extends the last
row affinely (these extensions are never used on `[t0, T]`).

We prove: continuity, the value on each row, the exact left derivative on a row, and the location of a
row `r` with `r.tl < t ≤ r.tr` for every `t` in the covered half-open interval.
-/

noncomputable section

namespace DBN

open Set Filter Topology

/-- Affine interpolation of a row, as a real function of time. -/
def Row.affineR (r : Row) (t : ℝ) : ℝ :=
  (r.qL : ℝ) + ((r.qR : ℝ) - r.qL) * (t - r.tl) / ((r.tr : ℝ) - r.tl)

/-- Slope magnitude `w = (qL - qR)/(tr - tl)` of a row (as a real). -/
def Row.speedR (r : Row) : ℝ := ((r.qL : ℝ) - r.qR) / ((r.tr : ℝ) - r.tl)

theorem Row.affineR_tl (r : Row) : r.affineR r.tl = r.qL := by
  simp [Row.affineR]

theorem Row.affineR_tr (r : Row) (h : r.tl < r.tr) : r.affineR r.tr = r.qR := by
  have : ((r.tr : ℝ) - r.tl) ≠ 0 := by
    have : (r.tl : ℝ) < r.tr := by exact_mod_cast h
    linarith
  unfold Row.affineR
  field_simp
  ring

theorem Row.affineR_eq (r : Row) (t : ℝ) (h : r.tl < r.tr) :
    r.affineR t = (r.qL : ℝ) - r.speedR * (t - r.tl) := by
  have : ((r.tr : ℝ) - r.tl) ≠ 0 := by
    have : (r.tl : ℝ) < r.tr := by exact_mod_cast h
    linarith
  unfold Row.affineR Row.speedR
  field_simp
  ring

theorem Row.continuous_affineR (r : Row) : Continuous r.affineR := by
  unfold Row.affineR
  fun_prop

theorem Row.hasDerivAt_affineR (r : Row) (h : r.tl < r.tr) (t : ℝ) :
    HasDerivAt r.affineR (-r.speedR) t := by
  have e : r.affineR = fun t => (r.qL : ℝ) - r.speedR * (t - r.tl) := by
    funext t; exact r.affineR_eq t h
  rw [e]
  have h1 := ((hasDerivAt_id t).sub_const (r.tl : ℝ)).const_mul r.speedR
  have h2 := h1.const_sub (r.qL : ℝ)
  simpa using h2

/-- On a row the affine value lies between `qR` and `qL`. -/
theorem Row.affineR_mem (r : Row) (h : r.tl < r.tr) (hq : r.qR < r.qL) {t : ℝ}
    (h1 : (r.tl : ℝ) ≤ t) (h2 : t ≤ r.tr) : (r.qR : ℝ) ≤ r.affineR t ∧ r.affineR t ≤ r.qL := by
  have hlt : (r.tl : ℝ) < r.tr := by exact_mod_cast h
  have hqR : (r.qR : ℝ) < r.qL := by exact_mod_cast hq
  have hw : 0 < r.speedR := by
    unfold Row.speedR; apply div_pos <;> linarith
  rw [r.affineR_eq t h]
  constructor
  · -- qL - w (t - tl) ≥ qL - w (tr - tl) = qR
    have : r.speedR * (t - r.tl) ≤ r.speedR * ((r.tr : ℝ) - r.tl) :=
      mul_le_mul_of_nonneg_left (by linarith) hw.le
    have e : r.speedR * ((r.tr : ℝ) - r.tl) = (r.qL : ℝ) - r.qR := by
      have hne : (r.tr : ℝ) - r.tl ≠ 0 := by linarith
      unfold Row.speedR
      rw [div_mul_eq_mul_div, mul_div_assoc, div_self hne, mul_one]
    linarith
  · have : 0 ≤ r.speedR * (t - r.tl) := mul_nonneg hw.le (by linarith)
    linarith

/-- The barrier defined by a list of rows. -/
def Q : List Row → ℝ → ℝ
  | [], _ => 0
  | [r], t => r.affineR t
  | r :: s :: rest, t => if t ≤ r.tr then r.affineR t else Q (s :: rest) t

/-- Rows are proper: `tl < tr` and `qR < qL` (part of `RowSpec`). -/
def Proper (l : List Row) : Prop := ∀ r ∈ l, r.tl < r.tr ∧ r.qR < r.qL

theorem Proper.tail {r : Row} {l : List Row} (h : Proper (r :: l)) : Proper l :=
  fun s hs => h s (List.mem_cons_of_mem r hs)

theorem Proper.head {r : Row} {l : List Row} (h : Proper (r :: l)) : r.tl < r.tr ∧ r.qR < r.qL :=
  h r (List.mem_cons_self ..)

/-- In a proper chain, every later row starts no earlier than the first row ends. -/
theorem Chain.later_ge : ∀ (l : List Row) (r : Row), Chain (r :: l) → Proper (r :: l) →
    ∀ s ∈ l, r.tr ≤ s.tl
  | [], _, _, _, s, hs => absurd hs (List.not_mem_nil)
  | b :: rest, r, hc, hp, s, hs => by
      obtain ⟨h1, _, h3⟩ := hc
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact le_of_eq h1
      · have hb := (hp.tail).head
        have := Chain.later_ge rest b h3 hp.tail s hs'
        calc r.tr = b.tl := h1
          _ ≤ b.tr := hb.1.le
          _ ≤ s.tl := this

/-- `Q` is continuous for a proper chain of rows. -/
theorem continuous_Q : ∀ l : List Row, Chain l → Proper l → Continuous (Q l)
  | [], _, _ => by simp [Q]; exact continuous_const
  | [r], _, _ => by simp [Q]; exact r.continuous_affineR
  | r :: s :: rest, hc, hp => by
      obtain ⟨h1, h2, h3⟩ := hc
      have ih := continuous_Q (s :: rest) h3 hp.tail
      have hr := hp.head
      have hs := hp.tail.head
      show Continuous fun t => if t ≤ (r.tr : ℝ) then r.affineR t else Q (s :: rest) t
      apply Continuous.if_le r.continuous_affineR ih continuous_id continuous_const
      intro t ht
      simp only [id] at ht
      subst ht
      -- Q (s :: rest) (r.tr) = s.affineR r.tr since r.tr = s.tl ≤ s.tr
      have hQ : Q (s :: rest) (r.tr : ℝ) = s.affineR (r.tr : ℝ) := by
        cases rest with
        | nil => simp [Q]
        | cons u rest' =>
            simp only [Q]
            have : (r.tr : ℝ) ≤ s.tr := by
              have : (s.tl : ℝ) ≤ s.tr := by exact_mod_cast hs.1.le
              rw [show (r.tr : ℝ) = s.tl by exact_mod_cast h1]; exact this
            simp [this]
      rw [hQ, r.affineR_tr hr.1]
      have : (r.tr : ℝ) = s.tl := by exact_mod_cast h1
      rw [this, s.affineR_tl]
      exact_mod_cast h2

/-- On a row of a proper chain, `Q` equals that row's affine function. -/
theorem Q_eq_on_row : ∀ (l : List Row), Chain l → Proper l → ∀ r ∈ l, ∀ t : ℝ,
    (r.tl : ℝ) ≤ t → t ≤ r.tr → Q l t = r.affineR t
  | [], _, _, r, hr, _, _, _ => absurd hr (List.not_mem_nil)
  | [a], _, _, r, hr, t, _, _ => by
      have : r = a := List.mem_singleton.mp hr
      subst this; simp [Q]
  | a :: s :: rest, hc, hp, r, hr, t, ht1, ht2 => by
      obtain ⟨h1, h2, h3⟩ := hc
      have ha := hp.head
      simp only [Q]
      rcases List.mem_cons.mp hr with rfl | hr'
      · -- r = a, t ∈ [a.tl, a.tr]
        simp [ht2]
      · -- r is a later row: a.tr ≤ r.tl ≤ t
        have hle : a.tr ≤ r.tl := Chain.later_ge (s :: rest) a ⟨h1, h2, h3⟩ hp r hr'
        have hle' : (a.tr : ℝ) ≤ t := le_trans (by exact_mod_cast hle) ht1
        by_cases hta : t ≤ (a.tr : ℝ)
        · -- then t = a.tr = r.tl, and r must be s
          have hteq : t = a.tr := le_antisymm hta hle'
          have hrtl : (r.tl : ℝ) = a.tr := le_antisymm (hteq ▸ ht1) (by exact_mod_cast hle)
          -- r.tl = a.tr = s.tl; rows are proper so r = s (the only row starting at s.tl)
          have hrs : r = s ∨ r ∈ rest := List.mem_cons.mp hr'
          rcases hrs with rfl | hr''
          · rw [if_pos hta, hteq, a.affineR_tr ha.1]
            have : (a.tr : ℝ) = r.tl := by exact_mod_cast h1
            rw [this, r.affineR_tl]; exact_mod_cast h2
          · -- r ∈ rest: then s.tr ≤ r.tl = a.tr = s.tl < s.tr, contradiction
            have hs := hp.tail.head
            have := Chain.later_ge rest s h3 hp.tail r hr''
            have h1' : a.tr = s.tl := h1
            have : s.tr ≤ s.tl := by
              calc s.tr ≤ r.tl := this
                _ = a.tr := by exact_mod_cast hrtl
                _ = s.tl := h1'
            exact absurd hs.1 (not_lt.mpr this)
        · rw [if_neg hta]
          exact Q_eq_on_row (s :: rest) h3 hp.tail r hr' t ht1 ht2

/-- Every time in `(first.tl, last.tr]` lies in `(r.tl, r.tr]` for some row `r` of the chain. -/
theorem exists_row_of_mem : ∀ (l : List Row) (hne : l ≠ []), Chain l → Proper l → ∀ t : ℝ,
    ((l.head hne).tl : ℝ) < t → t ≤ ((l.getLast hne).tr : ℝ) → ∃ r ∈ l, (r.tl : ℝ) < t ∧ t ≤ r.tr
  | [], hne, _, _, _, _, _ => absurd rfl hne
  | [a], _, _, _, t, h1, h2 => ⟨a, List.mem_singleton_self a, by simpa using h1, by simpa using h2⟩
  | a :: s :: rest, _, hc, hp, t, h1, h2 => by
      obtain ⟨hc1, hc2, hc3⟩ := hc
      by_cases hta : t ≤ (a.tr : ℝ)
      · exact ⟨a, List.mem_cons_self .., by simpa using h1, hta⟩
      · push_neg at hta
        have hne' : (s :: rest) ≠ [] := List.cons_ne_nil s rest
        have h1' : (((s :: rest).head hne').tl : ℝ) < t := by
          simp only [List.head_cons]
          rw [show (s.tl : ℝ) = a.tr by exact_mod_cast hc1.symm]; exact hta
        have h2' : t ≤ (((s :: rest).getLast hne').tr : ℝ) := by
          simpa [List.getLast_cons] using h2
        obtain ⟨r, hr, hr1, hr2⟩ := exists_row_of_mem (s :: rest) hne' hc3 hp.tail t h1' h2'
        exact ⟨r, List.mem_cons_of_mem a hr, hr1, hr2⟩

/-- Left derivative of `Q` at a point `t ∈ (r.tl, r.tr]` of a row `r`. -/
theorem Q_hasDerivWithinAt_Iic {l : List Row} (hc : Chain l) (hp : Proper l) {r : Row} (hr : r ∈ l)
    {t : ℝ} (h1 : (r.tl : ℝ) < t) (h2 : t ≤ r.tr) :
    HasDerivWithinAt (Q l) (-r.speedR) (Iic t) t := by
  have hrp := hp r hr
  have hd : HasDerivWithinAt r.affineR (-r.speedR) (Iic t) t :=
    (r.hasDerivAt_affineR hrp.1 t).hasDerivWithinAt
  apply hd.congr_of_eventuallyEq
  · -- Q l = r.affineR on a left neighbourhood of t within Iic t
    have hmem : Icc (r.tl : ℝ) t ∈ 𝓝[Iic t] t := by
      apply mem_nhdsWithin.mpr
      refine ⟨Ioi (r.tl : ℝ), isOpen_Ioi, h1, ?_⟩
      intro x hx
      exact ⟨le_of_lt hx.1, hx.2⟩
    filter_upwards [hmem] with x hx
    exact Q_eq_on_row l hc hp r hr x hx.1 (le_trans hx.2 h2)
  · exact Q_eq_on_row l hc hp r hr t h1.le h2

/-- `Q ≥ 1/400` on every row of a barrier whose rows all satisfy `RowSpec`. -/
theorem Q_ge_qFinal {wall : Array Seg} {l : List Row} (hc : Chain l) (hs : ∀ r ∈ l, RowSpec wall r)
    {r : Row} (hr : r ∈ l) {t : ℝ} (h1 : (r.tl : ℝ) ≤ t) (h2 : t ≤ r.tr) :
    (1 / 400 : ℝ) ≤ Q l t := by
  have hp : Proper l := fun s hs' => ⟨(hs s hs').1, (hs s hs').2.2.1⟩
  have hrs := hs r hr
  rw [Q_eq_on_row l hc hp r hr t h1 h2]
  have := (r.affineR_mem (hp r hr).1 (hp r hr).2 h1 h2).1
  have hq : (Const.qFinal : ℝ) ≤ r.qR := by exact_mod_cast hrs.2.1
  have : (Const.qFinal : ℝ) = 1 / 400 := by norm_num [Const.qFinal]
  linarith

end DBN
