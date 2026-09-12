import DBN.Certificate
import DBN.Data.mainRows
import DBN.Data.fullCRows
import DBN.Data.Wall
import DBN.Data.Catalog

/-!
# The finite certificate passes (kernel-checked)

Every Boolean check below is evaluated by the Lean **kernel** (`decide +kernel`) on the frozen data:
the kernel reduces the checker using its GMP-accelerated natural-number arithmetic. No `native_decide`
and no axiom beyond Mathlib's standard three is involved.

The per-row checks are evaluated chunk by chunk (500 rows per chunk, the granularity of the generated
data files) and recombined with `List.all_append`; a single `decide` over all 4817 rows makes the kernel's
reduction get stuck, while the chain, endpoint and catalog checks over the whole list are cheap enough to
run in one piece.
-/

namespace DBN

set_option maxRecDepth 100000

/-- The M3a wall trace is a proper chain on `[0, T_M]`. -/
theorem wall_ok : checkWallTrace Data.wall = true := by decide +kernel

/-! ### Main barrier: 4817 rows on `[3/50, T]` (box-A row, ALL rows 0–224, FORWARD rows 0–4590). -/

theorem mainRows0_ok : Data.mainRows0.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem mainRows1_ok : Data.mainRows1.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem mainRows2_ok : Data.mainRows2.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem mainRows3_ok : Data.mainRows3.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem mainRows4_ok : Data.mainRows4.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem mainRows5_ok : Data.mainRows5.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem mainRows6_ok : Data.mainRows6.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem mainRows7_ok : Data.mainRows7.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem mainRows8_ok : Data.mainRows8.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem mainRows9_ok : Data.mainRows9.toList.all (checkRow Data.wall) = true := by decide +kernel

theorem mainRows_all_ok : Data.mainRows.all (checkRow Data.wall) = true := by
  simp only [Data.mainRows, List.all_append, mainRows0_ok, mainRows1_ok, mainRows2_ok, mainRows3_ok, mainRows4_ok, mainRows5_ok, mainRows6_ok, mainRows7_ok, mainRows8_ok, mainRows9_ok, Bool.and_self]

theorem mainRows_chainOK : chainOK Data.mainRows = true := by decide +kernel
theorem mainRows_head_ok :
    (decide (Data.mainRows.head?.map Row.tl = some Const.aT) && decide (Data.mainRows.head?.map Row.qL = some Const.aQ)) = true := by
  decide +kernel
theorem mainRows_last_ok :
    (decide (Data.mainRows.getLast?.map Row.tr = some Const.T) && decide (Data.mainRows.getLast?.map Row.qR = some Const.qFinal)) = true := by
  decide +kernel
theorem mainRows_ne : (!Data.mainRows.isEmpty) = true := by decide +kernel

/-- The main barrier passes the whole-barrier check: starts at `(3/50, q_bk(3/50) + 10⁻⁹)`, ends at `(T, 1/400)`. -/
theorem mainRows_ok : checkBarrier Data.wall Data.mainRows Const.aT Const.aQ Const.T Const.qFinal = true := by
  have h1 := mainRows_all_ok
  have h2 := mainRows_chainOK
  have h3 := mainRows_ne
  have h4 := mainRows_head_ok
  have h5 := mainRows_last_ok
  simp only [Bool.and_eq_true] at h4 h5
  unfold checkBarrier
  rw [h1, h2, h3, h4.1, h4.2, h5.1, h5.2]
  rfl

/-! ### Reference barrier `q_bk`: 7849 rows on `[0, T*]`, starting at `(1000001/1000000)²`. -/

theorem fullCRows0_ok : Data.fullCRows0.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem fullCRows1_ok : Data.fullCRows1.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem fullCRows2_ok : Data.fullCRows2.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem fullCRows3_ok : Data.fullCRows3.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem fullCRows4_ok : Data.fullCRows4.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem fullCRows5_ok : Data.fullCRows5.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem fullCRows6_ok : Data.fullCRows6.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem fullCRows7_ok : Data.fullCRows7.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem fullCRows8_ok : Data.fullCRows8.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem fullCRows9_ok : Data.fullCRows9.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem fullCRows10_ok : Data.fullCRows10.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem fullCRows11_ok : Data.fullCRows11.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem fullCRows12_ok : Data.fullCRows12.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem fullCRows13_ok : Data.fullCRows13.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem fullCRows14_ok : Data.fullCRows14.toList.all (checkRow Data.wall) = true := by decide +kernel
theorem fullCRows15_ok : Data.fullCRows15.toList.all (checkRow Data.wall) = true := by decide +kernel

theorem fullCRows_all_ok : Data.fullCRows.all (checkRow Data.wall) = true := by
  simp only [Data.fullCRows, List.all_append, fullCRows0_ok, fullCRows1_ok, fullCRows2_ok, fullCRows3_ok, fullCRows4_ok, fullCRows5_ok, fullCRows6_ok, fullCRows7_ok, fullCRows8_ok, fullCRows9_ok, fullCRows10_ok, fullCRows11_ok, fullCRows12_ok, fullCRows13_ok, fullCRows14_ok, fullCRows15_ok, Bool.and_self]

theorem fullCRows_chainOK : chainOK Data.fullCRows = true := by decide +kernel
theorem fullCRows_head_ok :
    (decide (Data.fullCRows.head?.map Row.tl = some 0) && decide (Data.fullCRows.head?.map Row.qL = some Const.q0)) = true := by
  decide +kernel
theorem fullCRows_last_ok :
    (decide (Data.fullCRows.getLast?.map Row.tr = some Const.Tstar) && decide (Data.fullCRows.getLast?.map Row.qR = some Const.qFinal)) = true := by
  decide +kernel
theorem fullCRows_ne : (!Data.fullCRows.isEmpty) = true := by decide +kernel

theorem fullCRows_ok : checkBarrier Data.wall Data.fullCRows 0 Const.q0 Const.Tstar Const.qFinal = true := by
  have h1 := fullCRows_all_ok
  have h2 := fullCRows_chainOK
  have h3 := fullCRows_ne
  have h4 := fullCRows_head_ok
  have h5 := fullCRows_last_ok
  simp only [Bool.and_eq_true] at h4 h5
  unfold checkBarrier
  rw [h1, h2, h3, h4.1, h4.2, h5.1, h5.2]
  rfl

/-- Every source certificate used is literally one of the 26 catalog boxes. -/
theorem mainRows_catalog_ok : checkCatalog Data.catalog Data.mainRows = true := by decide +kernel

theorem mainRows_length : Data.mainRows.length = 4817 := by decide +kernel
theorem fullCRows_length : Data.fullCRows.length = 7849 := by decide +kernel

/-- Consequently every main row satisfies its propositional specification. -/
theorem mainRows_spec : ∀ r ∈ Data.mainRows, RowSpec Data.wall r := checkBarrier_rows mainRows_ok
/-- Every `q_bk` row satisfies its specification. -/
theorem fullCRows_spec : ∀ r ∈ Data.fullCRows, RowSpec Data.wall r := checkBarrier_rows fullCRows_ok
theorem mainRows_nonempty : Data.mainRows ≠ [] := checkBarrier_nonempty mainRows_ok
theorem mainRows_chain : Chain Data.mainRows := checkBarrier_chain mainRows_ok

theorem fullCRows_nonempty : Data.fullCRows ≠ [] := checkBarrier_nonempty fullCRows_ok
theorem fullCRows_chain : Chain Data.fullCRows := checkBarrier_chain fullCRows_ok

/-! ### Row facts used to derive the entry hypothesis of the main barrier from the reference barrier -/

/-- First cell of `q_bk`: `[0, 1/50000]`, from `q₀` down to `999763470827643981/10¹⁸`. -/
theorem fullC_head_tr : (Data.fullCRows.head fullCRows_nonempty).tr = 1 / 50000 := by decide +kernel
theorem fullC_head_qR :
    (Data.fullCRows.head fullCRows_nonempty).qR = 999763470827643981 / 1000000000000000000 := by decide +kernel

/-- Cell 2999 of `q_bk` ends at `t = 3/50` with `q_bk(3/50) = 84648870570133/(2·10¹⁴) = aQ − 10⁻⁹`. -/
theorem fullC_2999_check :
    (Data.fullCRows[2999]?.map fun r =>
      decide (r.tl = 2999 / 50000 ∧ r.tr = 3 / 50 ∧ r.qR = 84648870570133 / 200000000000000)) = some true := by
  decide +kernel

/-- The reference barrier has no source rows. -/
theorem fullC_no_source :
    Data.fullCRows.all (fun r => match r.cert with | .field _ => true | .source _ => false) = true := by
  decide +kernel


end DBN
