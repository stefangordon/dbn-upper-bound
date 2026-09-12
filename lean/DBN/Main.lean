import DBN.Heat
import DBN.Algebra
import DBN.Check
import DBN.Barrier
import DBN.Premises
import DBN.FirstContact
import DBN.Kernels
import DBN.External
import DBN.OmegaGap
import DBN.ZeroBranch
import DBN.Hermite
import DBN.PairSum
import DBN.Confinement
import DBN.FieldTransfer

/-!
# Main theorem

`Λ ≤ bound` from the **remaining** analytic premises (`RemainingPremises`): positive-time confinement,
the finite head, the source floors and the field floors. Everything else is a theorem:

* the tail premises (de Bruijn contraction, `Λ > −∞`), the strip, the symmetries, closedness of the
  zero set and `H₀ = ξ` come from leancert (`DBN.External`);
* the finite certificate (`DBN.Check`), the barrier calculus (`DBN.Barrier`), the force lemmas
  (`DBN.Algebra`), the kernel minorants (`DBN.Kernels`) and the first-contact argument
  (`DBN.FirstContact`) are kernel-checked here;
* the strict entry of the main barrier at `t = 3/50` is *derived* by running the first-contact
  argument on the reference barrier `q_bk` from the cushion time `τ₀`, where `q_bk(τ₀) > 1 ≥ Im(ρ)²`;
* the `Ω`-gap `Ω(x) > Ω_L` for `x ≥ X` is proved in `DBN.OmegaGap`;
* the zero dynamics at a highest zero (P1 + P6 + backward Hermite splitting) are proved: the
  differentiable zero branch through a simple zero with its exact velocity `H''/H'` in `DBN.ZeroBranch`
  (implicit function theorem), the backward Hermite splitting at a multiple zero in `DBN.Hermite`
  (double expansion under the heat integral + Hurwitz), and the pair-sum force laws in `DBN.PairSum`
  (leancert's Hadamard zero sum, paired over conjugate indices into the kernels of `DBN.Kernels`).
-/

namespace DBN

open Set

/-- Cushion time: `q_bk > 1` on `[0, τ₀]`; `τ₀ = min(t₁/2, (q₀−1)/(2 w₀))` for the first cell. -/
def τ0 : ℚ := 20000010 / 238529173356019

theorem τ0_pos : (0 : ℚ) < τ0 := by norm_num [τ0]
theorem τ0_lt_aT : τ0 < Const.aT := by norm_num [τ0, Const.aT]
theorem τ0_le_cell : τ0 ≤ 1 / 50000 := by norm_num [τ0]

/-- The exact confinement premise follows from the explicit Polymath tail
proposition. The cited literature theorem is a parameter, not an added axiom. -/
theorem confine_of_polymathPositiveTimeRealTail (hP : PolymathPositiveTimeRealTail) :
    ∃ R : ℝ, ∀ t ∈ Icc (τ0 : ℝ) (Const.Tstar : ℝ), ∀ z : ℂ,
      H t z = 0 → 1 / 40 ≤ |z.im| → |z.re| ≤ R :=
  confinement_of_polymathPositiveTimeRealTail hP (by exact_mod_cast τ0_pos)
    (by norm_num [Const.Tstar]) (by norm_num)

/-- The remaining analytic premises: exactly the not-yet-formalized inputs P2, P3, P4/P5/P8 and P7, stated
over the concrete `H_t` for the time range `[τ₀, T*]` of the reference barrier (which contains `[3/50, T]`).
These are explicit hypotheses, not axioms. `ProfileRemainingPremises` separates P4/P5 from the exact
P8 endpoint gates, and `confine_of_polymathPositiveTimeRealTail` supplies P3 from a precisely named
literature proposition. The analytic finite-head/source/field comparisons and the complete P8 list
remain unproved in this development. -/
structure RemainingPremises : Prop where
  /-- P3: positive-time confinement on `[τ₀, T*]`. -/
  confine : ∃ R : ℝ, ∀ t ∈ Icc (τ0 : ℝ) (Const.Tstar : ℝ), ∀ z : ℂ, H t z = 0 → 1 / 40 ≤ |z.im| → |z.re| ≤ R
  /-- P2: finite head. -/
  head : ∀ t ∈ Icc (0 : ℝ) (1 / 5), ∀ z : ℂ, H t z = 0 → |z.re| ≤ Const.X → z.im = 0
  /-- P7: source floors for the 26 boxes used by the main rows. -/
  sourceFloor : ∀ r ∈ Data.mainRows, ∀ c : SourceCert, r.cert = .source c → ∀ x : ℝ, (Const.X : ℝ) ≤ x →
    ∀ t ∈ Icc (c.btl : ℝ) c.btr, ∀ h ∈ Icc (c.hlo : ℝ) c.hhi, (c.L : ℝ) ≤ V x h t
  /-- P4 + P5 + P8: field floors on the old cells of the main and reference rows. -/
  fieldFloor : ∀ r ∈ Data.mainRows ++ Data.fullCRows, ∀ c : FieldCert, r.cert = .field c →
    ∀ x : ℝ, (Const.X : ℝ) ≤ x → ∀ t ∈ Icc (c.otl : ℝ) c.otr,
      H t (x + (c.p : ℝ) * Complex.I) ≠ 0 ∧ (c.s : ℝ) < S x c.p t ∧
      (c.signed = true → J x c.p t ≤ c.c)

/-- An alternative, more explicit input boundary: the analytic P4/P5 field
comparisons and the exact P8 endpoint gates are separate. Full P8 and the
analytic finite-head/source/field comparisons remain parameters. -/
structure ProfileRemainingPremises : Prop where
  /-- P2: finite head. -/
  head : ∀ t ∈ Icc (0 : ℝ) (1 / 5), ∀ z : ℂ, H t z = 0 → |z.re| ≤ Const.X → z.im = 0
  /-- P7: source floors. -/
  sourceFloor : ∀ r ∈ Data.mainRows, ∀ c : SourceCert, r.cert = .source c → ∀ x : ℝ, (Const.X : ℝ) ≤ x →
    ∀ t ∈ Icc (c.btl : ℝ) c.btr, ∀ h ∈ Icc (c.hlo : ℝ) c.hhi, (c.L : ℝ) ≤ V x h t
  /-- P4/P5 over their original moving-wall domains. -/
  fields : Profile.DensityJetFields
  /-- All P8 point gates, including reused main-row certificates. -/
  cells : Profile.ProfileCellGates

/-- The explicit source, profile and literature interfaces imply every field
of the original main theorem's premise, without changing its statement. -/
theorem remainingPremises_of_polymath_and_profiles (hP : PolymathPositiveTimeRealTail)
    (P : ProfileRemainingPremises) : RemainingPremises where
  confine := confine_of_polymathPositiveTimeRealTail hP
  head := P.head
  sourceFloor := P.sourceFloor
  fieldFloor := Profile.fieldFloor_of_profiles P.fields P.cells

theorem ZeroDynamics.mono {t0 T t0' T' : ℝ} (h : ZeroDynamics t0 T) (h1 : t0 ≤ t0') (h2 : T' ≤ T) :
    ZeroDynamics t0' T' :=
  fun t1 ht1 => h t1 ⟨lt_of_le_of_lt h1 ht1.1, le_trans ht1.2 h2⟩

/-- The zero dynamics on `(τ₀, T*]` are a theorem: the simple-zero branch (`DBN.ZeroBranch`), the
backward Hermite splitting (`DBN.Hermite`) and the pair-sum force laws (`DBN.PairSum`). -/
theorem zeroDynamics_proved : ZeroDynamics (τ0 : ℝ) (Const.Tstar : ℝ) :=
  zeroDynamics_of (hermiteSplit_proved _ _) (pairSumForce_proved _ _)

/-! ### The reference barrier `q_bk` on `[τ₀, T*]` -/

theorem fullC_head_tl : (Data.fullCRows.head fullCRows_nonempty).tl = 0 :=
  checkBarrier_head_tl fullCRows_ok fullCRows_nonempty
theorem fullC_head_qL : (Data.fullCRows.head fullCRows_nonempty).qL = Const.q0 :=
  checkBarrier_head_qL fullCRows_ok fullCRows_nonempty
theorem fullC_last_tr : (Data.fullCRows.getLast fullCRows_nonempty).tr = Const.Tstar :=
  checkBarrier_last_tr fullCRows_ok fullCRows_nonempty

/-- `q_bk(τ₀) = (q₀ + 1)/2 > 1`. -/
theorem Q_fullC_τ0_gt_one : 1 < Q Data.fullCRows (τ0 : ℝ) := by
  have hp : Proper Data.fullCRows := fun r hr => ⟨(fullCRows_spec r hr).1, (fullCRows_spec r hr).2.2.1⟩
  set r := Data.fullCRows.head fullCRows_nonempty with hr
  have hmem : r ∈ Data.fullCRows := List.head_mem fullCRows_nonempty
  have hrp := hp r hmem
  have h1 : (r.tl : ℝ) ≤ τ0 := by rw [hr, fullC_head_tl]; exact_mod_cast τ0_pos.le
  have h2 : (τ0 : ℝ) ≤ r.tr := by rw [hr, fullC_head_tr]; exact_mod_cast τ0_le_cell
  rw [Q_eq_on_row Data.fullCRows fullCRows_chain hp r hmem _ h1 h2, r.affineR_eq _ hrp.1]
  unfold Row.speedR
  rw [hr, fullC_head_tl, fullC_head_tr, fullC_head_qL, fullC_head_qR]
  norm_num [Const.q0, τ0]

/-- `q_bk(3/50) = aQ − 10⁻⁹ < aQ`. -/
theorem Q_fullC_aT_lt_aQ : Q Data.fullCRows (Const.aT : ℝ) < Const.aQ := by
  have hp : Proper Data.fullCRows := fun r hr => ⟨(fullCRows_spec r hr).1, (fullCRows_spec r hr).2.2.1⟩
  obtain ⟨r, hget, hb⟩ := Option.map_eq_some_iff.mp fullC_2999_check
  have hmem : r ∈ Data.fullCRows := List.mem_of_getElem? hget
  obtain ⟨htl, htr, hqR⟩ := decide_eq_true_iff.mp hb
  have hrp := hp r hmem
  have h1 : (r.tl : ℝ) ≤ Const.aT := by rw [htl]; norm_num [Const.aT]
  have h2 : (Const.aT : ℝ) ≤ r.tr := by rw [htr]; norm_num [Const.aT]
  rw [Q_eq_on_row Data.fullCRows fullCRows_chain hp r hmem _ h1 h2]
  have e : (Const.aT : ℝ) = r.tr := by rw [htr]; norm_num [Const.aT]
  rw [e, r.affineR_tr hrp.1, hqR]
  norm_num [Const.aQ]

theorem fullC_sourceFloor : ∀ r ∈ Data.fullCRows, ∀ c : SourceCert, r.cert = .source c → ∀ x : ℝ,
    (Const.X : ℝ) ≤ x → ∀ t ∈ Icc (c.btl : ℝ) c.btr, ∀ h ∈ Icc (c.hlo : ℝ) c.hhi, (c.L : ℝ) ≤ V x h t := by
  intro r hr c hc
  exfalso
  have h := List.all_eq_true.mp fullC_no_source r hr
  rw [hc] at h
  simp at h

/-- The analytic premises of the reference barrier on `[τ₀, T*]`, from the remaining premises. -/
theorem fullCPremises (P : RemainingPremises) :
    AnalyticPremises (τ0 : ℝ) (Const.Tstar : ℝ) Data.fullCRows where
  strip := strip_all
  symm := symm_all
  closed := closed_zeros _ _
  confine := P.confine
  head := P.head
  entry := by
    intro z hz
    have h1 := strip_all (τ0 : ℝ) (by exact_mod_cast τ0_pos.le) z hz
    have h2 : z.im ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one z.im).mpr h1
    exact lt_of_le_of_lt h2 Q_fullC_τ0_gt_one
  dynamics := zeroDynamics_proved
  sourceFloor := fullC_sourceFloor
  fieldFloor := fun r hr => P.fieldFloor r (List.mem_append_right _ hr)
  omegaGap := omegaGap_proved

/-- **Theorem C (formal).** `Im(ρ)² < q_bk(t)` on `[τ₀, T*]`, given the remaining premises. -/
theorem fullC_barrier_comparison (P : RemainingPremises) :
    ∀ t ∈ Icc (τ0 : ℝ) (Const.Tstar : ℝ), ∀ z : ℂ, H t z = 0 → z.im ^ 2 < Q Data.fullCRows t :=
  barrier_comparison Data.fullCRows fullCRows_nonempty fullCRows_chain fullCRows_spec
    (by rw [fullC_head_tl]; exact_mod_cast τ0_pos.le) (by rw [fullC_head_tr]; exact_mod_cast τ0_le_cell)
    (by rw [fullC_last_tr]) (by exact_mod_cast τ0_pos.le)
    (by have := Const.Tstar_lt_TM; have := Const.TM_lt_fifth
        have h : (Const.Tstar : ℚ) < 1 / 5 := by linarith
        have h' : ((Const.Tstar : ℚ) : ℝ) ≤ ((1 / 5 : ℚ) : ℝ) := Rat.cast_le.mpr h.le
        have e : ((1 / 5 : ℚ) : ℝ) = (1 / 5 : ℝ) := by push_cast; ring
        rwa [e] at h')
    (fullCPremises P)

/-! ### The main barrier on `[3/50, T]` -/

/-- The main barrier: `Q` of the 4817 certified rows on `[3/50, T]`. -/
noncomputable def Qmain : ℝ → ℝ := Q Data.mainRows

theorem mainRows_head_tl : (Data.mainRows.head mainRows_nonempty).tl = Const.aT :=
  checkBarrier_head_tl mainRows_ok mainRows_nonempty
theorem mainRows_head_qL : (Data.mainRows.head mainRows_nonempty).qL = Const.aQ :=
  checkBarrier_head_qL mainRows_ok mainRows_nonempty
theorem mainRows_last_tr : (Data.mainRows.getLast mainRows_nonempty).tr = Const.T :=
  checkBarrier_last_tr mainRows_ok mainRows_nonempty
theorem mainRows_last_qR : (Data.mainRows.getLast mainRows_nonempty).qR = Const.qFinal :=
  checkBarrier_last_qR mainRows_ok mainRows_nonempty

theorem Qmain_aT : Qmain (Const.aT : ℝ) = Const.aQ := by
  have hp : Proper Data.mainRows := fun r hr => ⟨(mainRows_spec r hr).1, (mainRows_spec r hr).2.2.1⟩
  set r := Data.mainRows.head mainRows_nonempty with hr
  have hmem : r ∈ Data.mainRows := List.head_mem mainRows_nonempty
  have hrp := hp r hmem
  have h1 : (r.tl : ℝ) = Const.aT := by rw [hr, mainRows_head_tl]
  unfold Qmain
  rw [Q_eq_on_row Data.mainRows mainRows_chain hp r hmem _ (le_of_eq h1)
      (by rw [← h1]; exact_mod_cast hrp.1.le), ← h1, r.affineR_tl, hr, mainRows_head_qL]

/-- Strict entry of the main barrier at `t = 3/50`, derived from the reference barrier. -/
theorem main_entry (P : RemainingPremises) : ∀ z : ℂ, H (Const.aT : ℝ) z = 0 → z.im ^ 2 < Qmain (Const.aT : ℝ) := by
  intro z hz
  have hmem : (Const.aT : ℝ) ∈ Icc (τ0 : ℝ) (Const.Tstar : ℝ) := by
    constructor
    · exact_mod_cast τ0_lt_aT.le
    · have := Const.aT_lt_allEntryT; have := Const.allEntryT_lt_entryT; have := Const.entryT_lt_T
      have := Const.T_lt_Tstar
      have h : (Const.aT : ℚ) ≤ Const.Tstar := by linarith
      exact_mod_cast h
  have h1 := fullC_barrier_comparison P _ hmem z hz
  rw [Qmain_aT]
  exact lt_trans h1 Q_fullC_aT_lt_aQ

/-- The analytic premises of the main barrier on `[3/50, T]`, from the remaining premises. -/
theorem mainPremises (P : RemainingPremises) :
    AnalyticPremises (Const.aT : ℝ) (Const.T : ℝ) Data.mainRows where
  strip := strip_all
  symm := symm_all
  closed := closed_zeros _ _
  confine := by
    obtain ⟨R, hR⟩ := P.confine
    refine ⟨R, fun t ht => hR t ⟨le_trans (by exact_mod_cast τ0_lt_aT.le) ht.1,
      le_trans ht.2 (by exact_mod_cast Const.T_lt_Tstar.le)⟩⟩
  head := P.head
  entry := main_entry P
  dynamics := zeroDynamics_proved.mono (by exact_mod_cast τ0_lt_aT.le) (by exact_mod_cast Const.T_lt_Tstar.le)
  sourceFloor := P.sourceFloor
  fieldFloor := fun r hr => P.fieldFloor r (List.mem_append_left _ hr)
  omegaGap := omegaGap_proved

/-- **Theorem A (formal).** Given the analytic premises for the main barrier, every zero of `H_t`,
`t ∈ [3/50, T]`, has `Im(ρ)² < Qmain t`. -/
theorem main_barrier_comparison (P : AnalyticPremises (Const.aT : ℝ) (Const.T : ℝ) Data.mainRows) :
    ∀ t ∈ Icc (Const.aT : ℝ) (Const.T : ℝ), ∀ z : ℂ, H t z = 0 → z.im ^ 2 < Qmain t :=
  barrier_comparison Data.mainRows mainRows_nonempty mainRows_chain mainRows_spec
    (le_of_eq (by rw [mainRows_head_tl]))
    (by have h1 : (Data.mainRows.head mainRows_nonempty).tl < (Data.mainRows.head mainRows_nonempty).tr :=
          (mainRows_spec _ (List.head_mem mainRows_nonempty)).1
        rw [mainRows_head_tl] at h1
        exact_mod_cast h1.le)
    (by rw [mainRows_last_tr]) (by norm_num [Const.aT])
    (by have := Const.T_lt_Tstar; have := Const.Tstar_lt_TM; have := Const.TM_lt_fifth
        have h : (Const.T : ℚ) < 1 / 5 := by linarith
        have h' : ((Const.T : ℚ) : ℝ) ≤ ((1 / 5 : ℚ) : ℝ) := Rat.cast_le.mpr h.le
        have e : ((1 / 5 : ℚ) : ℝ) = (1 / 5 : ℝ) := by push_cast; ring
        rwa [e] at h') P

/-- `Qmain T = 1/400`: the last row ends at `(T, 1/400)`. -/
theorem Qmain_T : Qmain (Const.T : ℝ) = 1 / 400 := by
  have hp : Proper Data.mainRows := fun r hr => ⟨(mainRows_spec r hr).1, (mainRows_spec r hr).2.2.1⟩
  set r := Data.mainRows.getLast mainRows_nonempty with hr
  have hmem : r ∈ Data.mainRows := List.getLast_mem mainRows_nonempty
  have hrp := hp r hmem
  have hT : (Const.T : ℝ) = r.tr := by rw [hr, mainRows_last_tr]
  unfold Qmain
  rw [Q_eq_on_row Data.mainRows mainRows_chain hp r hmem (Const.T : ℝ)
        (by rw [hT]; exact_mod_cast hrp.1.le) (le_of_eq hT),
      hT, r.affineR_tr hrp.1, hr, mainRows_last_qR]
  norm_num [Const.qFinal]

/-- The terminal barrier comparison at time `T`. -/
def TerminalStrip : Prop := ∀ z : ℂ, H (Const.T : ℝ) z = 0 → z.im ^ 2 < 1 / 400

theorem terminalStrip_of_premises (P : AnalyticPremises (Const.aT : ℝ) (Const.T : ℝ) Data.mainRows) :
    TerminalStrip := by
  intro z hz
  have := main_barrier_comparison P (Const.T : ℝ)
    ⟨by have h : (Const.aT : ℚ) < Const.T := by
          have := Const.aT_lt_allEntryT; have := Const.allEntryT_lt_entryT; have := Const.entryT_lt_T
          linarith
        exact_mod_cast h.le, le_refl _⟩ z hz
  rwa [Qmain_T] at this

/-- `Λ ≤ bound` from the tail premises and the terminal comparison (kept for reference). -/
theorem lambda_le_bound (P : TailPremises) (hT : TerminalStrip) : Lambda ≤ (Const.bound : ℝ) := by
  have h := Lambda_le_of_barrier_terminal P hT
  have e : ((Const.T : ℚ) : ℝ) + 1 / 800 = ((Const.bound : ℚ) : ℝ) := by
    rw [← Const.T_add_tail]
    push_cast [Const.tail]
    ring
  rwa [e] at h

/-- `Λ ≤ bound` from the full analytic premises (tail premises are now theorems). -/
theorem lambda_le_bound_of_premises (P : AnalyticPremises (Const.aT : ℝ) (Const.T : ℝ) Data.mainRows) :
    Lambda ≤ (Const.bound : ℝ) :=
  lambda_le_bound tailPremises (terminalStrip_of_premises P)

/-- **Main theorem.** `Λ ≤ 3885632262767861213460393068710302759 / 24646172707879668706230182733520000000`
from the remaining analytic premises alone. -/
theorem lambda_le_bound_of_remaining (P : RemainingPremises) : Lambda ≤ (Const.bound : ℝ) :=
  lambda_le_bound_of_premises (mainPremises P)

/-- The same bound with confinement discharged from the precise literature
tail proposition and field floors discharged from P4/P5 and the P8 gates. -/
theorem lambda_le_bound_of_polymath_and_profiles (hP : PolymathPositiveTimeRealTail)
    (P : ProfileRemainingPremises) : Lambda ≤ (Const.bound : ℝ) :=
  lambda_le_bound_of_remaining (remainingPremises_of_polymath_and_profiles hP P)

/-- Decimal comparison: the bound is below `79/500 = 0.158`. -/
theorem lambda_lt_79_500 (P : RemainingPremises) : Lambda < 79 / 500 := by
  refine lt_of_le_of_lt (lambda_le_bound_of_remaining P) ?_
  have h : ((Const.bound : ℚ) : ℝ) < ((79 / 500 : ℚ) : ℝ) := Rat.cast_lt.mpr Const.bound_lt_79_500
  have e : ((79 / 500 : ℚ) : ℝ) = (79 / 500 : ℝ) := by push_cast; ring
  rwa [e] at h

end DBN
