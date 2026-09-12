import DBN.WallGeometry
import DBN.Check

/-!
# From P4, P5 and the exact P8 endpoint gates to the field-floor premise

The geometry of every old field cell is proved from the frozen rational data.
The hypotheses below isolate the two analytic field comparisons (P4/P5) and
the full finite list of transcendental endpoint inequalities (P8). Only
selected difficult P8 endpoints are separately kernel-checked in `ProfileChecks`;
`ProfileCellGates` is deliberately still an explicit parameter here.
-/

noncomputable section

namespace DBN

open Set

set_option maxRecDepth 100000

/-- The rational geometry needed for profile transfer, separately checked over
every field certificate that occurs in either barrier. -/
private def checkOldCell (r : Row) : Bool :=
  match r.cert with
  | .source _ => true
  | .field c => decide (0 ≤ c.otl ∧ c.otr ≤ Const.TM ∧ r.tl = c.otl)

private theorem oldCells_checked :
    (Data.mainRows ++ Data.fullCRows).all checkOldCell = true := by decide +kernel

/-- The complete time and height domain conditions required by P4/P5. -/
theorem field_domains {r : Row} (hr : r ∈ Data.mainRows ++ Data.fullCRows)
    {c : FieldCert} (hc : r.cert = .field c) {t : ℝ} (ht : t ∈ Icc (c.otl : ℝ) c.otr) :
    t ∈ Icc (0 : ℝ) Const.TM ∧ 0 < (c.p : ℝ) ∧ (c.p : ℝ) ≤ 5 ∧
      Real.sqrt (qM t) < c.p ∧
      (c.signed = true → Real.sqrt (qM t) + 3 / 5 ≤ c.p) := by
  have hrow : RowSpec Data.wall r := by
    rcases List.mem_append.mp hr with hr | hr
    · exact mainRows_spec r hr
    · exact fullCRows_spec r hr
  have hspec : FieldSpec Data.wall r c := by simpa [RowSpec, hc] using hrow.2.2.2
  have hcell := List.all_eq_true.mp oldCells_checked r hr
  simp only [checkOldCell, hc, decide_eq_true_eq] at hcell
  obtain ⟨ht₀, htM, hleft⟩ := hcell
  obtain ⟨_, _, _, _, hw, hp₀, hp₅, _, _, hqp, _, hmode⟩ := hspec
  have hp : (0 : ℝ) < c.p := by exact_mod_cast hp₀
  have hq : qM t ≤ (c.qM : ℝ) := by
    have h := qM_antitone ht.1
    rwa [← hleft, qM_eq_of_wallSpec hw] at h
  refine ⟨⟨le_trans (by exact_mod_cast ht₀) ht.1, le_trans ht.2 (by exact_mod_cast htM)⟩,
    hp, by exact_mod_cast hp₅, (Real.sqrt_lt' hp).mpr (hq.trans_lt (by exact_mod_cast hqp)), ?_⟩
  intro hsigned
  rw [if_pos hsigned] at hmode
  unfold SignedSpec at hmode
  obtain ⟨_, _, hp₃, hq₃, _⟩ := hmode
  have hp₃' : ((3 / 5 : ℚ) : ℝ) ≤ (c.p : ℝ) := Rat.cast_le.mpr hp₃
  norm_num at hp₃'
  have hq₃' : (c.qM : ℝ) ≤ (((c.p - 3 / 5) ^ 2 : ℚ) : ℝ) := Rat.cast_le.mpr hq₃
  push_cast at hq₃'
  have hp' : (0 : ℝ) ≤ (c.p : ℝ) - 3 / 5 := by linarith
  have hq' : qM t ≤ ((c.p : ℝ) - 3 / 5) ^ 2 := hq.trans hq₃'
  have := (Real.sqrt_le_left hp').mpr hq'
  linarith

namespace Profile

/-- P4/P5, stated on their original domains over the concrete heat flow. These
analytic comparisons are not proved by the finite P8 computation. -/
structure DensityJetFields : Prop where
  density : ∀ x : ℝ, (Const.X : ℝ) ≤ x → ∀ t ∈ Icc (0 : ℝ) Const.TM,
    ∀ Y : ℝ, Real.sqrt (qM t) < Y → Y ≤ 5 →
      H t (x + Y * Complex.I) ≠ 0 ∧ fM Y t ≤ S x Y t
  jet : ∀ x : ℝ, (Const.X : ℝ) ≤ x → ∀ t ∈ Icc (0 : ℝ) Const.TM,
    ∀ Y : ℝ, Real.sqrt (qM t) + 3 / 5 ≤ Y → Y ≤ 5 → J x Y t ≤ C Y t

/-- Precisely the P8 endpoint gates, without applying the density subtraction
twice. The quantification includes reused main-row certificates. -/
def ProfileCellGates : Prop :=
  ∀ r ∈ Data.mainRows ++ Data.fullCRows, ∀ c : FieldCert, r.cert = .field c →
    (c.s : ℝ) + 1 / 100000 < f0 c.p c.otl ∧
      (c.signed = true → Cceil c.p c.otl c.otr ≤ c.c)

/-- P4/P5 and the exact P8 point gates imply the entire `fieldFloor` field of
`RemainingPremises`, on every closed old cell. All geometry and profile
monotonicity used in the transfer are proved, not additional hypotheses. -/
theorem fieldFloor_of_profiles (hfields : DensityJetFields) (hgates : ProfileCellGates) :
    ∀ r ∈ Data.mainRows ++ Data.fullCRows, ∀ c : FieldCert, r.cert = .field c →
      ∀ x : ℝ, (Const.X : ℝ) ≤ x → ∀ t ∈ Icc (c.otl : ℝ) c.otr,
        H t (x + (c.p : ℝ) * Complex.I) ≠ 0 ∧ (c.s : ℝ) < S x c.p t ∧
        (c.signed = true → J x c.p t ≤ c.c) := by
  intro r hr c hc x hx t ht
  obtain ⟨htime, hp, hp₅, hheight, hjetHeight⟩ := field_domains hr hc ht
  obtain ⟨hnumS, hnumC⟩ := hgates r hr c hc
  obtain ⟨hzero, hS⟩ := hfields.density x hx t htime c.p hheight hp₅
  refine ⟨hzero, density_gt_of_endpoint hp.le ht.1 htime.2 hnumS hS, ?_⟩
  intro hsigned
  exact jet_le_of_endpoint ht.1 ht.2 (hnumC hsigned)
    (hfields.jet x hx t htime c.p (hjetHeight hsigned) hp₅)

end Profile
end DBN

end
