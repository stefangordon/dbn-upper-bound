import DBN.Profile

/-!
# Rational wall geometry

The concrete M3a wall is a proper decreasing chain. Its monotonicity and the
connection between each stored rational wall value and the real interpolant
are kernel-checked here; no analytic field comparison is assumed.
-/

noncomputable section

namespace DBN

open Set

private theorem Row.antitone_affineR (r : Row) (ht : r.tl < r.tr) (hq : r.qR < r.qL) :
    Antitone r.affineR := by
  intro s t hst
  rw [r.affineR_eq t ht, r.affineR_eq s ht]
  have hw : 0 ≤ r.speedR := by
    unfold Row.speedR
    have h₁ : (r.tl : ℝ) < r.tr := by exact_mod_cast ht
    have h₂ : (r.qR : ℝ) < r.qL := by exact_mod_cast hq
    exact div_nonneg (by linarith) (by linarith)
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left (by linarith) hw) _

/-- A proper decreasing row chain defines a decreasing continuous wall. -/
theorem antitone_Q : ∀ l : List Row, Chain l → Proper l → Antitone (Q l)
  | [], _, _ => by simp [Q, Antitone]
  | [r], _, hp => by
      simpa only [Q] using r.antitone_affineR hp.head.1 hp.head.2
  | r :: s :: rest, hc, hp => by
      have ih := antitone_Q (s :: rest) hc.2.2 hp.tail
      have hr := r.antitone_affineR hp.head.1 hp.head.2
      have hjoin : Q (s :: rest) (r.tr : ℝ) = r.affineR r.tr := by
        have he : (r.tr : ℝ) = s.tl := by exact_mod_cast hc.1
        rw [Q_eq_on_row (s :: rest) hc.2.2 hp.tail s (List.mem_cons_self ..) _
          (by rw [he]) (by rw [he]; exact_mod_cast hp.tail.head.1.le)]
        rw [r.affineR_tr hp.head.1, he, s.affineR_tl]
        exact_mod_cast hc.2.1.symm
      intro a b hab
      change (if b ≤ (r.tr : ℝ) then r.affineR b else Q (s :: rest) b) ≤
        (if a ≤ (r.tr : ℝ) then r.affineR a else Q (s :: rest) a)
      by_cases hb : b ≤ (r.tr : ℝ)
      · rw [if_pos hb, if_pos (hab.trans hb)]
        exact hr hab
      · rw [if_neg hb]
        by_cases ha : a ≤ (r.tr : ℝ)
        · rw [if_pos ha]
          exact (ih (le_of_not_ge hb)).trans (hjoin ▸ hr ha)
        · rw [if_neg ha]
          exact ih hab

set_option maxRecDepth 100000

private theorem wall_chain : Chain (Data.wall.toList.map Seg.toRow) :=
  (chainOK_iff _).mp (by decide +kernel)

private theorem wall_proper : Proper (Data.wall.toList.map Seg.toRow) := by
  have hc : (Data.wall.toList.map Seg.toRow).all (fun r => decide (r.tl < r.tr ∧ r.qR < r.qL)) = true := by
    decide +kernel
  intro r hr
  exact of_decide_eq_true (List.all_eq_true.mp hc r hr)

theorem qM_antitone : Antitone qM := antitone_Q _ wall_chain wall_proper

theorem qM_eq_of_wallSpec {r : Row} {c : FieldCert} (hw : WallSpec Data.wall r c) :
    qM (r.tl : ℝ) = c.qM := by
  obtain ⟨sg, hget, htl, htr, _, heq⟩ := hw
  have hmem : sg.toRow ∈ Data.wall.toList.map Seg.toRow := by
    apply List.mem_map.mpr
    refine ⟨sg, ?_, rfl⟩
    simpa using Array.mem_of_getElem? hget
  rw [qM, Q_eq_on_row _ wall_chain wall_proper sg.toRow hmem _
    (by exact_mod_cast htl) (by exact_mod_cast htr)]
  rw [heq]
  simp [Row.affineR, Seg.toRow, Seg.affine]

end DBN

end
