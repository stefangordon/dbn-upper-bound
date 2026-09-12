import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import DBN.Constants

/-!
# The finite certificate: rows, gates, and their meaning

A barrier is a list of affine *rows* `[tl, tr] ∋ t ↦ qL + (qR - qL)(t - tl)/(tr - tl)`.
Each row carries a *certificate* licensing the inequality `q_zero' < Q'` at any first contact:

* `SourceCert`: a closed box `[btl, btr] × [hlo, hhi]` with an accepted floor `V ≥ L` for the
  three-probe observable `V = (15/14)S(3h) - (16/21)S(4h) + (1/6)S(5h)`; the source law
  `q' ≤ -2/15 - 4√q V` then beats the row slope when the *strict sqrt-speed gate* holds.
* `FieldCert`: literal old field data `(p, s, c)` valid on a whole old time cell `[otl, otr]`
  (`S(x,p,t) > s`, and in signed mode `J(x,p,t) ≤ c`), the M3a wall value `qM = q_M(tl)`, and the
  fresh coefficient `k = K(qL)`; the field law `q' < -2 - q K(q)` beats the slope when
  `(qL - qR)/(tr - tl) ≤ 2 + k qR`.

`checkRow` is the executable (Boolean) form of the *mathematical* predicates; `RowSpec` is the
propositional form, and `checkRow_iff` proves they agree. Provenance and hash gates of the
reviewed Python checkers are deliberately not part of this file.
-/

namespace DBN

/-- Closed source box with floor `L` for the three-probe observable `V`. -/
structure SourceCert where
  id : ℕ
  L : ℚ
  hlo : ℚ
  hhi : ℚ
  btl : ℚ
  btr : ℚ
deriving Repr, DecidableEq, Inhabited

/-- Old field data on one old time cell `[otl, otr]` (index `oIdx` of the fullC certificate). -/
structure FieldCert where
  signed : Bool
  p : ℚ
  s : ℚ
  c : ℚ      -- unused (0) in unsigned mode
  qM : ℚ     -- q_M(tl), the M3a wall at the row start
  mIdx : ℕ   -- index of the M3a wall cell containing tl
  otl : ℚ
  otr : ℚ
  oIdx : ℕ
deriving Repr, DecidableEq, Inhabited

inductive Cert where
  | source (c : SourceCert)
  | field (c : FieldCert)
deriving Repr, DecidableEq, Inhabited

/-- One affine barrier row. -/
structure Row where
  tl : ℚ
  tr : ℚ
  qL : ℚ
  qR : ℚ
  cert : Cert
deriving Repr, DecidableEq, Inhabited

/-- One affine cell of a reference trace (used for the M3a wall `q_M`). -/
structure Seg where
  tl : ℚ
  tr : ℚ
  qL : ℚ
  qR : ℚ
deriving Repr, DecidableEq, Inhabited

/-- Affine interpolation on a cell. -/
def Seg.affine (s : Seg) (t : ℚ) : ℚ := s.qL + (s.qR - s.qL) * (t - s.tl) / (s.tr - s.tl)

/-- Unsigned field coefficient `K_u(q) = 4s/p - 8/(p² - q)`. -/
def Ku (s p q : ℚ) : ℚ := 4 * s / p - 8 / (p ^ 2 - q)
/-- Signed field coefficient `K_s(q) = 6s/p - 2L0 + q(2L0/p² - 2s/p³) - 16/(p² - q)`. -/
def Ks (s p L0 q : ℚ) : ℚ := 6 * s / p - 2 * L0 + q * (2 * L0 / p ^ 2 - 2 * s / p ^ 3) - 16 / (p ^ 2 - q)

/-! ## Propositional specification -/

/-- Strict sqrt-speed gate for a source row with slope `w = (qL - qR)/dt`:
either `w ≤ 2/15`, or `w > 2/15` and `(w - 2/15)² < 16 L² qR`. -/
def SourceGate (L qL qR dt : ℚ) : Prop :=
  let w := (qL - qR) / dt
  w ≤ Const.sourceA ∨ (Const.sourceA < w ∧ (w - Const.sourceA) ^ 2 < 16 * L ^ 2 * qR)

def SourceSpec (r : Row) (c : SourceCert) : Prop :=
  c.btl ≤ r.tl ∧ r.tr ≤ c.btr ∧ 0 < c.L ∧ 0 < c.hlo ∧ c.hlo < c.hhi ∧
  c.hlo ^ 2 ≤ r.qR ∧ r.qL ≤ c.hhi ^ 2 ∧ SourceGate c.L r.qL r.qR (r.tr - r.tl)

/-- The M3a wall cell `mIdx` contains `tl` and evaluates to `qM` there. -/
def WallSpec (wall : Array Seg) (r : Row) (c : FieldCert) : Prop :=
  ∃ sg, wall[c.mIdx]? = some sg ∧ sg.tl ≤ r.tl ∧ r.tl ≤ sg.tr ∧ sg.tl < sg.tr ∧ c.qM = sg.affine r.tl

def SignedSpec (r : Row) (c : FieldCert) : Prop :=
  let P := c.p ^ 2
  let δ := Const.OmegaL - c.s
  let L0 := c.c - δ ^ 2
  let amax := c.p * (P - r.qR) / (3 * P - r.qR)
  let k := Ks c.s c.p L0 r.qL
  0 < c.c ∧ 0 < δ ∧ 3 / 5 ≤ c.p ∧ c.qM ≤ (c.p - 3 / 5) ^ 2 ∧ 9 * r.qL ≤ P ∧
  c.p * L0 ≤ c.s ∧ 2 * amax * δ ≤ 1 ∧ 0 < k ∧ (r.qL - r.qR) / (r.tr - r.tl) ≤ 2 + k * r.qR

def UnsignedSpec (r : Row) (c : FieldCert) : Prop :=
  let P := c.p ^ 2
  let k := Ku c.s c.p r.qL
  5 * r.qL ≤ P ∧ 0 < k ∧ (r.qL - r.qR) / (r.tr - r.tl) ≤ 2 + k * r.qR

def FieldSpec (wall : Array Seg) (r : Row) (c : FieldCert) : Prop :=
  c.otl ≤ r.tl ∧ r.tr ≤ c.otr ∧ c.otr - c.otl ≤ 1 / 50000 ∧ r.tr ≤ Const.TM ∧
  WallSpec wall r c ∧
  0 < c.p ∧ c.p ≤ 5 ∧ 0 < c.s ∧ 0 ≤ c.qM ∧ c.qM < c.p ^ 2 ∧ r.qL < c.p ^ 2 ∧
  (if c.signed then SignedSpec r c else UnsignedSpec r c)

def RowSpec (wall : Array Seg) (r : Row) : Prop :=
  r.tl < r.tr ∧ Const.qFinal ≤ r.qR ∧ r.qR < r.qL ∧
  match r.cert with
  | .source c => SourceSpec r c
  | .field c => FieldSpec wall r c

/-! ## Executable checker -/

def sourceGate (L qL qR dt : ℚ) : Bool :=
  let w := (qL - qR) / dt
  decide (w ≤ Const.sourceA) || (decide (Const.sourceA < w) && decide ((w - Const.sourceA) ^ 2 < 16 * L ^ 2 * qR))

def checkSource (r : Row) (c : SourceCert) : Bool :=
  decide (c.btl ≤ r.tl) && decide (r.tr ≤ c.btr) && decide (0 < c.L) && decide (0 < c.hlo) &&
  decide (c.hlo < c.hhi) && decide (c.hlo ^ 2 ≤ r.qR) && decide (r.qL ≤ c.hhi ^ 2) &&
  sourceGate c.L r.qL r.qR (r.tr - r.tl)

def checkWall (wall : Array Seg) (r : Row) (c : FieldCert) : Bool :=
  match wall[c.mIdx]? with
  | some sg => decide (sg.tl ≤ r.tl) && decide (r.tl ≤ sg.tr) && decide (sg.tl < sg.tr) &&
      decide (c.qM = sg.affine r.tl)
  | none => false

def checkSigned (r : Row) (c : FieldCert) : Bool :=
  let P := c.p ^ 2
  let δ := Const.OmegaL - c.s
  let L0 := c.c - δ ^ 2
  let amax := c.p * (P - r.qR) / (3 * P - r.qR)
  let k := Ks c.s c.p L0 r.qL
  decide (0 < c.c) && decide (0 < δ) && decide (3 / 5 ≤ c.p) && decide (c.qM ≤ (c.p - 3 / 5) ^ 2) &&
  decide (9 * r.qL ≤ P) && decide (c.p * L0 ≤ c.s) && decide (2 * amax * δ ≤ 1) && decide (0 < k) &&
  decide ((r.qL - r.qR) / (r.tr - r.tl) ≤ 2 + k * r.qR)

def checkUnsigned (r : Row) (c : FieldCert) : Bool :=
  let P := c.p ^ 2
  let k := Ku c.s c.p r.qL
  decide (5 * r.qL ≤ P) && decide (0 < k) && decide ((r.qL - r.qR) / (r.tr - r.tl) ≤ 2 + k * r.qR)

def checkField (wall : Array Seg) (r : Row) (c : FieldCert) : Bool :=
  decide (c.otl ≤ r.tl) && decide (r.tr ≤ c.otr) && decide (c.otr - c.otl ≤ 1 / 50000) &&
  decide (r.tr ≤ Const.TM) && checkWall wall r c &&
  decide (0 < c.p) && decide (c.p ≤ 5) && decide (0 < c.s) && decide (0 ≤ c.qM) &&
  decide (c.qM < c.p ^ 2) && decide (r.qL < c.p ^ 2) &&
  (if c.signed then checkSigned r c else checkUnsigned r c)

def checkRow (wall : Array Seg) (r : Row) : Bool :=
  decide (r.tl < r.tr) && decide (Const.qFinal ≤ r.qR) && decide (r.qR < r.qL) &&
  match r.cert with
  | .source c => checkSource r c
  | .field c => checkField wall r c

/-- Consecutive rows join exactly in time and squared height. -/
def chainOK : List Row → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a.tr = b.tl) && decide (a.qR = b.qL) && chainOK (b :: rest)

def Chain : List Row → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a.tr = b.tl ∧ a.qR = b.qL ∧ Chain (b :: rest)

/-- Whole-barrier check: every row passes, rows chain, and the endpoints are as prescribed. -/
def checkBarrier (wall : Array Seg) (rows : List Row) (t0 q0 t1 q1 : ℚ) : Bool :=
  !rows.isEmpty && rows.all (checkRow wall) && chainOK rows &&
  decide (rows.head?.map Row.tl = some t0) && decide (rows.head?.map Row.qL = some q0) &&
  decide (rows.getLast?.map Row.tr = some t1) && decide (rows.getLast?.map Row.qR = some q1)

/-- Every source certificate appearing in the rows is literally a catalog entry. -/
def checkCatalog (cat : Array SourceCert) (rows : List Row) : Bool :=
  rows.all fun r => match r.cert with
    | .source c => decide (cat[c.id]? = some c)
    | .field _ => true

/-- The wall trace is a chain of proper, non-increasing affine cells ending at `T_M`. -/
def checkWallTrace (wall : Array Seg) : Bool :=
  decide (0 < wall.size) && wall.toList.all (fun s => decide (s.tl < s.tr) && decide (s.qR ≤ s.qL) && decide (0 < s.qR)) &&
  (wall.toList.zip wall.toList.tail).all (fun (a, b) => decide (a.tr = b.tl) && decide (a.qR = b.qL)) &&
  decide (wall[0]!.tl = 0) && decide (wall.back!.tr = Const.TM)

/-! ## The checker decides the specification -/

theorem sourceGate_iff (L qL qR dt : ℚ) : sourceGate L qL qR dt = true ↔ SourceGate L qL qR dt := by
  simp [sourceGate, SourceGate]

theorem checkSource_iff (r : Row) (c : SourceCert) : checkSource r c = true ↔ SourceSpec r c := by
  simp [checkSource, SourceSpec, sourceGate_iff, and_assoc]

theorem checkWall_iff (wall : Array Seg) (r : Row) (c : FieldCert) :
    checkWall wall r c = true ↔ WallSpec wall r c := by
  unfold checkWall WallSpec
  cases h : wall[c.mIdx]? with
  | none => simp
  | some sg => simp [and_assoc]

theorem checkSigned_iff (r : Row) (c : FieldCert) : checkSigned r c = true ↔ SignedSpec r c := by
  simp [checkSigned, SignedSpec, and_assoc]

theorem checkUnsigned_iff (r : Row) (c : FieldCert) : checkUnsigned r c = true ↔ UnsignedSpec r c := by
  simp [checkUnsigned, UnsignedSpec, and_assoc]

theorem checkField_iff (wall : Array Seg) (r : Row) (c : FieldCert) :
    checkField wall r c = true ↔ FieldSpec wall r c := by
  unfold checkField FieldSpec
  by_cases hs : c.signed = true
  · simp [hs, checkWall_iff, checkSigned_iff, and_assoc]
  · simp [hs, checkWall_iff, checkUnsigned_iff, and_assoc]

theorem checkRow_iff (wall : Array Seg) (r : Row) : checkRow wall r = true ↔ RowSpec wall r := by
  unfold checkRow RowSpec
  rcases hc : r.cert with c | c
  · simp [checkSource_iff, and_assoc]
  · simp [checkField_iff, and_assoc]

theorem chainOK_iff : ∀ l : List Row, chainOK l = true ↔ Chain l
  | [] => by simp [chainOK, Chain]
  | [_] => by simp [chainOK, Chain]
  | a :: b :: rest => by
      simp [chainOK, Chain, chainOK_iff (b :: rest), and_assoc]

theorem checkBarrier_rows {wall : Array Seg} {rows : List Row} {t0 q0 t1 q1 : ℚ}
    (h : checkBarrier wall rows t0 q0 t1 q1 = true) : ∀ r ∈ rows, RowSpec wall r := by
  simp only [checkBarrier, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨_, hB⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  intro r hr
  exact (checkRow_iff wall r).mp (hB r hr)

theorem checkBarrier_chain {wall : Array Seg} {rows : List Row} {t0 q0 t1 q1 : ℚ}
    (h : checkBarrier wall rows t0 q0 t1 q1 = true) : Chain rows := by
  simp only [checkBarrier, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hC⟩, _⟩, _⟩, _⟩, _⟩ := h
  exact (chainOK_iff _).mp hC

theorem checkBarrier_nonempty {wall : Array Seg} {rows : List Row} {t0 q0 t1 q1 : ℚ}
    (h : checkBarrier wall rows t0 q0 t1 q1 = true) : rows ≠ [] := by
  simp only [checkBarrier, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have h1 := h.1.1.1.1.1.1
  intro he
  subst he
  simp at h1

theorem checkBarrier_endpoints {wall : Array Seg} {rows : List Row} {t0 q0 t1 q1 : ℚ}
    (h : checkBarrier wall rows t0 q0 t1 q1 = true) :
    rows.head?.map Row.tl = some t0 ∧ rows.head?.map Row.qL = some q0 ∧
      rows.getLast?.map Row.tr = some t1 ∧ rows.getLast?.map Row.qR = some q1 := by
  simp only [checkBarrier, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, hD⟩, hE⟩, hF⟩, hG⟩ := h
  exact ⟨hD, hE, hF, hG⟩

theorem checkBarrier_head_tl {wall : Array Seg} {rows : List Row} {t0 q0 t1 q1 : ℚ}
    (h : checkBarrier wall rows t0 q0 t1 q1 = true) (hne : rows ≠ []) : (rows.head hne).tl = t0 := by
  have := (checkBarrier_endpoints h).1
  rw [List.head?_eq_head hne] at this
  simpa using this

theorem checkBarrier_head_qL {wall : Array Seg} {rows : List Row} {t0 q0 t1 q1 : ℚ}
    (h : checkBarrier wall rows t0 q0 t1 q1 = true) (hne : rows ≠ []) : (rows.head hne).qL = q0 := by
  have := (checkBarrier_endpoints h).2.1
  rw [List.head?_eq_head hne] at this
  simpa using this

theorem checkBarrier_last_tr {wall : Array Seg} {rows : List Row} {t0 q0 t1 q1 : ℚ}
    (h : checkBarrier wall rows t0 q0 t1 q1 = true) (hne : rows ≠ []) : (rows.getLast hne).tr = t1 := by
  have := (checkBarrier_endpoints h).2.2.1
  rw [List.getLast?_eq_getLast hne] at this
  simpa using this

theorem checkBarrier_last_qR {wall : Array Seg} {rows : List Row} {t0 q0 t1 q1 : ℚ}
    (h : checkBarrier wall rows t0 q0 t1 q1 = true) (hne : rows ≠ []) : (rows.getLast hne).qR = q1 := by
  have := (checkBarrier_endpoints h).2.2.2
  rw [List.getLast?_eq_getLast hne] at this
  simpa using this

end DBN
