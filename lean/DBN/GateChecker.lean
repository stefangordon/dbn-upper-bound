import Mathlib
import DBN.Profile
import DBN.FieldTransfer

/-!
# A kernel-checked evaluator for the P8 endpoint gates

`ProfileCellGates` asks, for every field certificate `c` of both barriers, that
`s + 10⁻⁵ < f0(p, t_L) = U_Y/U (p, t_L)` and, in signed mode, `Cceil(p, t_L, t_R) ≤ c`, where `U` is the
explicit three-term heat profile of `DBN.Profile`. These are transcendental inequalities in the
rational row data.

This file proves them all by kernel reduction. The evaluator computes rational lower and upper
bounds for `exp`, `cosh` and `sinh` at rational arguments: a 20-term Taylor polynomial on `x/64`
(Mathlib's `Real.sum_le_exp_of_nonneg` and `Real.exp_bound'`), six squarings, and directional
rounding to the fixed-point scale `2⁻¹⁰⁰` after every squaring. `checkCert_sound` shows that the
Boolean `checkCert` implies both gates; the chunk theorems evaluate `checkCert` on the frozen data
with `decide +kernel`, exactly as `DBN.Check` does for the rational certificate. No `native_decide`.
-/

namespace DBN.Profile.Gate

/-! ### Directional rounding at scale `2⁻¹⁰⁰` -/

def scZ : ℤ := 1267650600228229401496703205376
def sc : ℚ := (scZ : ℚ)

theorem sc_pos : (0 : ℚ) < sc := by unfold sc scZ; norm_num

/-- Round down to a multiple of `2⁻¹⁰⁰`. -/
def rd (q : ℚ) : ℚ := (⌊q * sc⌋ : ℚ) / sc
/-- Round up to a multiple of `2⁻¹⁰⁰`. -/
def ru (q : ℚ) : ℚ := (⌈q * sc⌉ : ℚ) / sc

theorem rd_le (q : ℚ) : rd q ≤ q := by
  unfold rd; rw [div_le_iff₀ sc_pos]; exact Int.floor_le _

theorem le_ru (q : ℚ) : q ≤ ru q := by
  unfold ru; rw [le_div_iff₀ sc_pos]; exact Int.le_ceil _

theorem rd_nonneg {q : ℚ} (h : 0 ≤ q) : 0 ≤ rd q := by
  unfold rd
  apply div_nonneg _ sc_pos.le
  exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg h sc_pos.le)

theorem one_le_rd {q : ℚ} (h : 1 ≤ q) : 1 ≤ rd q := by
  unfold rd
  rw [le_div_iff₀ sc_pos, one_mul]
  have h1 : scZ ≤ ⌊q * sc⌋ := Int.le_floor.mpr (by
    show (scZ : ℚ) ≤ q * sc
    have := sc_pos
    unfold sc at *
    nlinarith)
  show (scZ : ℚ) ≤ (⌊q * sc⌋ : ℚ)
  exact_mod_cast h1

/-! ### The Taylor polynomial of `exp` -/

/-- Horner-style accumulation of `Σ_{j<m} x^j/j!` starting from index `i`. -/
def go (x : ℚ) : ℕ → ℕ → ℚ → ℚ → ℚ
  | 0, _, _, sum => sum
  | m + 1, i, term, sum => go x m (i + 1) (term * x / ((i + 1 : ℕ) : ℚ)) (sum + term)

/-- `Σ_{j<n} x^j/j!`. -/
def taylor (x : ℚ) (n : ℕ) : ℚ := go x n 0 1 0

theorem go_eq (x : ℚ) (m : ℕ) : ∀ i : ℕ,
    go x m i (x ^ i / (i.factorial : ℚ)) (∑ j ∈ Finset.range i, x ^ j / (j.factorial : ℚ)) =
      ∑ j ∈ Finset.range (i + m), x ^ j / (j.factorial : ℚ) := by
  induction m with
  | zero => intro i; simp [go]
  | succ m ih =>
    intro i
    simp only [go]
    have e1 : x ^ i / (i.factorial : ℚ) * x / ((i + 1 : ℕ) : ℚ) =
        x ^ (i + 1) / ((i + 1).factorial : ℚ) := by
      rw [Nat.factorial_succ]
      push_cast
      have h1 : ((i.factorial : ℕ) : ℚ) ≠ 0 := by positivity
      have h2 : ((i : ℚ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    have e2 : ∑ j ∈ Finset.range i, x ^ j / (j.factorial : ℚ) + x ^ i / (i.factorial : ℚ) =
        ∑ j ∈ Finset.range (i + 1), x ^ j / (j.factorial : ℚ) := (Finset.sum_range_succ _ _).symm
    rw [e1, e2, ih (i + 1), show i + 1 + m = i + (m + 1) from by omega]

theorem taylor_eq (x : ℚ) (n : ℕ) : taylor x n = ∑ j ∈ Finset.range n, x ^ j / (j.factorial : ℚ) := by
  have h := go_eq x n 0
  simpa [taylor] using h

theorem taylor_cast (x : ℚ) (n : ℕ) :
    ((taylor x n : ℚ) : ℝ) = ∑ j ∈ Finset.range n, (x : ℝ) ^ j / (j.factorial : ℝ) := by
  rw [taylor_eq]; push_cast; rfl

theorem one_le_taylor {y : ℚ} (hy : 0 ≤ y) : 1 ≤ taylor y 20 := by
  rw [taylor_eq]
  have := Finset.single_le_sum (f := fun j => y ^ j / (j.factorial : ℚ)) (s := Finset.range 20)
    (fun j _ => by positivity) (Finset.mem_range.mpr (by norm_num : 0 < 20))
  simpa using this

/-! ### `exp` on `[0, 1]` -/

def expLoUnit (y : ℚ) : ℚ := rd (taylor y 20)
def expUpUnit (y : ℚ) : ℚ := ru (taylor y 20 + y ^ 20 * 21 / ((Nat.factorial 20 : ℚ) * 20))

theorem one_le_expLoUnit {y : ℚ} (hy : 0 ≤ y) : 1 ≤ expLoUnit y := one_le_rd (one_le_taylor hy)

theorem expLoUnit_le {y : ℚ} (hy : 0 ≤ y) : ((expLoUnit y : ℚ) : ℝ) ≤ Real.exp y := by
  unfold expLoUnit
  calc ((rd (taylor y 20) : ℚ) : ℝ) ≤ ((taylor y 20 : ℚ) : ℝ) := by exact_mod_cast rd_le _
    _ = ∑ j ∈ Finset.range 20, (y : ℝ) ^ j / (j.factorial : ℝ) := taylor_cast y 20
    _ ≤ Real.exp y := Real.sum_le_exp_of_nonneg (by exact_mod_cast hy) 20

theorem le_expUpUnit {y : ℚ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : Real.exp y ≤ ((expUpUnit y : ℚ) : ℝ) := by
  unfold expUpUnit
  have h := Real.exp_bound' (x := (y : ℝ)) (by exact_mod_cast hy0) (by exact_mod_cast hy1)
    (n := 20) (by norm_num)
  calc Real.exp y ≤ ∑ m ∈ Finset.range 20, (y : ℝ) ^ m / (m.factorial : ℝ) +
        (y : ℝ) ^ 20 * ((20 : ℕ) + 1) / ((Nat.factorial 20 : ℝ) * (20 : ℕ)) := h
    _ = ((taylor y 20 + y ^ 20 * 21 / ((Nat.factorial 20 : ℚ) * 20) : ℚ) : ℝ) := by
        rw [Rat.cast_add, taylor_cast]; push_cast; ring
    _ ≤ _ := by exact_mod_cast le_ru _

/-! ### Repeated squaring with rounding -/

def sqDown : ℕ → ℚ → ℚ
  | 0, q => q
  | k + 1, q => sqDown k (rd (q * q))

def sqUp : ℕ → ℚ → ℚ
  | 0, q => q
  | k + 1, q => sqUp k (ru (q * q))

theorem sqDown_le (k : ℕ) : ∀ {q : ℚ} {y : ℝ}, 0 ≤ q → (q : ℝ) ≤ y →
    ((sqDown k q : ℚ) : ℝ) ≤ y ^ (2 ^ k) := by
  induction k with
  | zero => intro q y _ h; simpa [sqDown] using h
  | succ k ih =>
    intro q y hq h
    simp only [sqDown]
    have hy : (0 : ℝ) ≤ y := le_trans (by exact_mod_cast hq) h
    have h1 : (0 : ℚ) ≤ rd (q * q) := rd_nonneg (mul_nonneg hq hq)
    have h2 : ((rd (q * q) : ℚ) : ℝ) ≤ y ^ 2 := by
      calc ((rd (q * q) : ℚ) : ℝ) ≤ ((q * q : ℚ) : ℝ) := by exact_mod_cast rd_le _
        _ = (q : ℝ) * (q : ℝ) := by push_cast; ring
        _ ≤ y * y := mul_le_mul h h (by exact_mod_cast hq) hy
        _ = y ^ 2 := by ring
    have := ih h1 h2
    rwa [← pow_mul, show 2 * 2 ^ k = 2 ^ (k + 1) by ring] at this

theorem one_le_sqDown (k : ℕ) : ∀ {q : ℚ}, 1 ≤ q → 1 ≤ sqDown k q := by
  induction k with
  | zero => intro q h; simpa [sqDown] using h
  | succ k ih =>
    intro q h
    simp only [sqDown]
    exact ih (one_le_rd (by nlinarith))

theorem le_sqUp (k : ℕ) : ∀ {q : ℚ} {y : ℝ}, 0 ≤ y → y ≤ q → y ^ (2 ^ k) ≤ ((sqUp k q : ℚ) : ℝ) := by
  induction k with
  | zero => intro q y _ h; simpa [sqUp] using h
  | succ k ih =>
    intro q y hy h
    simp only [sqUp]
    have hq : (0 : ℝ) ≤ q := le_trans hy h
    have h2 : y ^ 2 ≤ ((ru (q * q) : ℚ) : ℝ) := by
      calc y ^ 2 = y * y := by ring
        _ ≤ (q : ℝ) * (q : ℝ) := mul_le_mul h h hy hq
        _ = ((q * q : ℚ) : ℝ) := by push_cast; ring
        _ ≤ _ := by exact_mod_cast le_ru _
    have := ih (by positivity) h2
    rwa [← pow_mul, show 2 * 2 ^ k = 2 ^ (k + 1) by ring] at this

/-! ### `exp` on `[0, 64]` -/

def expLo (x : ℚ) : ℚ := sqDown 6 (expLoUnit (x / 64))
def expUp (x : ℚ) : ℚ := sqUp 6 (expUpUnit (x / 64))

theorem exp_eq_pow64 (x : ℚ) : Real.exp x = Real.exp ((x / 64 : ℚ) : ℝ) ^ (2 ^ 6) := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem expLo_le {x : ℚ} (hx : 0 ≤ x) : ((expLo x : ℚ) : ℝ) ≤ Real.exp x := by
  rw [exp_eq_pow64]; unfold expLo
  have h0 : (0 : ℚ) ≤ expLoUnit (x / 64) := le_trans zero_le_one (one_le_expLoUnit (by positivity))
  exact sqDown_le 6 h0 (expLoUnit_le (by positivity))

theorem le_expUp {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 64) : Real.exp x ≤ ((expUp x : ℚ) : ℝ) := by
  rw [exp_eq_pow64]; unfold expUp
  exact le_sqUp 6 (Real.exp_pos _).le (le_expUpUnit (by positivity) (by linarith))

theorem one_le_expLo {x : ℚ} (hx : 0 ≤ x) : 1 ≤ expLo x :=
  one_le_sqDown 6 (one_le_expLoUnit (by positivity))

theorem expLo_pos {x : ℚ} (hx : 0 ≤ x) : 0 < expLo x := lt_of_lt_of_le one_pos (one_le_expLo hx)

theorem expUp_pos {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 64) : 0 < expUp x := by
  have := lt_of_lt_of_le (Real.exp_pos (x : ℝ)) (le_expUp hx0 hx1)
  exact_mod_cast this

/-! ### `exp (-x)`, `cosh`, `sinh` -/

def expNegLo (x : ℚ) : ℚ := rd (1 / expUp x)
def expNegUp (x : ℚ) : ℚ := ru (1 / expLo x)

theorem expNegLo_le {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 64) :
    ((expNegLo x : ℚ) : ℝ) ≤ Real.exp (-x) := by
  unfold expNegLo
  rw [Real.exp_neg]
  calc ((rd (1 / expUp x) : ℚ) : ℝ) ≤ ((1 / expUp x : ℚ) : ℝ) := by exact_mod_cast rd_le _
    _ = ((expUp x : ℚ) : ℝ)⁻¹ := by push_cast; ring
    _ ≤ (Real.exp x)⁻¹ := inv_anti₀ (Real.exp_pos _) (le_expUp hx0 hx1)

theorem le_expNegUp {x : ℚ} (hx0 : 0 ≤ x) : Real.exp (-x) ≤ ((expNegUp x : ℚ) : ℝ) := by
  unfold expNegUp
  rw [Real.exp_neg]
  have hpos : (0 : ℝ) < ((expLo x : ℚ) : ℝ) := by exact_mod_cast expLo_pos hx0
  calc (Real.exp x)⁻¹ ≤ ((expLo x : ℚ) : ℝ)⁻¹ := inv_anti₀ hpos (expLo_le hx0)
    _ = ((1 / expLo x : ℚ) : ℝ) := by push_cast; ring
    _ ≤ _ := by exact_mod_cast le_ru _

theorem expNegLo_nonneg {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 64) : 0 ≤ expNegLo x :=
  rd_nonneg (div_nonneg zero_le_one (expUp_pos hx0 hx1).le)

def coshLo (x : ℚ) : ℚ := rd ((expLo x + expNegLo x) / 2)
def coshUp (x : ℚ) : ℚ := ru ((expUp x + expNegUp x) / 2)
def sinhLo (x : ℚ) : ℚ := max 0 (rd ((expLo x - expNegUp x) / 2))

theorem coshLo_le {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 64) : ((coshLo x : ℚ) : ℝ) ≤ Real.cosh x := by
  unfold coshLo
  rw [Real.cosh_eq]
  calc ((rd ((expLo x + expNegLo x) / 2) : ℚ) : ℝ) ≤ (((expLo x + expNegLo x) / 2 : ℚ) : ℝ) := by
        exact_mod_cast rd_le _
    _ = (((expLo x : ℚ) : ℝ) + ((expNegLo x : ℚ) : ℝ)) / 2 := by push_cast; ring
    _ ≤ (Real.exp x + Real.exp (-x)) / 2 :=
        div_le_div_of_nonneg_right (add_le_add (expLo_le hx0) (expNegLo_le hx0 hx1)) (by norm_num)

theorem le_coshUp {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 64) : Real.cosh x ≤ ((coshUp x : ℚ) : ℝ) := by
  unfold coshUp
  rw [Real.cosh_eq]
  calc (Real.exp x + Real.exp (-x)) / 2 ≤ (((expUp x : ℚ) : ℝ) + ((expNegUp x : ℚ) : ℝ)) / 2 :=
        div_le_div_of_nonneg_right (add_le_add (le_expUp hx0 hx1) (le_expNegUp hx0)) (by norm_num)
    _ = (((expUp x + expNegUp x) / 2 : ℚ) : ℝ) := by push_cast; ring
    _ ≤ _ := by exact_mod_cast le_ru _

theorem sinhLo_le {x : ℚ} (hx0 : 0 ≤ x) : ((sinhLo x : ℚ) : ℝ) ≤ Real.sinh x := by
  unfold sinhLo
  rw [Rat.cast_max]
  apply max_le
  · simp only [Rat.cast_zero]
    exact Real.sinh_nonneg_iff.mpr (by exact_mod_cast hx0)
  · rw [Real.sinh_eq]
    calc ((rd ((expLo x - expNegUp x) / 2) : ℚ) : ℝ) ≤ (((expLo x - expNegUp x) / 2 : ℚ) : ℝ) := by
          exact_mod_cast rd_le _
      _ = (((expLo x : ℚ) : ℝ) - ((expNegUp x : ℚ) : ℝ)) / 2 := by push_cast; ring
      _ ≤ (Real.exp x - Real.exp (-x)) / 2 :=
          div_le_div_of_nonneg_right (sub_le_sub (expLo_le hx0) (le_expNegUp hx0)) (by norm_num)

theorem coshLo_nonneg {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 64) : 0 ≤ coshLo x :=
  rd_nonneg (div_nonneg (add_nonneg (expLo_pos hx0).le (expNegLo_nonneg hx0 hx1)) (by norm_num))

theorem sinhLo_nonneg (x : ℚ) : 0 ≤ sinhLo x := le_max_left _ _

/-! ### The three profile bounds -/

def a1 : ℚ := 1758974
def a2 : ℚ := 2464729
def a3 : ℚ := 302096
def r1 : ℚ := 19 / 4
def r2 : ℚ := 97 / 20
def r3 : ℚ := 131 / 20

def Ulo (Y t : ℚ) : ℚ := 1000000000 +
  a1 * expLo (r1 ^ 2 * t) * coshLo (r1 * Y) +
  a2 * expLo (r2 ^ 2 * t) * coshLo (r2 * Y) +
  a3 * expLo (r3 ^ 2 * t) * coshLo (r3 * Y)

def Uup (Y t : ℚ) : ℚ := 1000000000 +
  a1 * expUp (r1 ^ 2 * t) * coshUp (r1 * Y) +
  a2 * expUp (r2 ^ 2 * t) * coshUp (r2 * Y) +
  a3 * expUp (r3 ^ 2 * t) * coshUp (r3 * Y)

def UYlo (Y t : ℚ) : ℚ :=
  a1 * r1 * expLo (r1 ^ 2 * t) * sinhLo (r1 * Y) +
  a2 * r2 * expLo (r2 ^ 2 * t) * sinhLo (r2 * Y) +
  a3 * r3 * expLo (r3 ^ 2 * t) * sinhLo (r3 * Y)

theorem mul3_le {a : ℝ} (ha : 0 ≤ a) {e1 e2 c1 c2 : ℝ} (he0 : 0 ≤ e1) (he : e1 ≤ e2) (hc0 : 0 ≤ c1)
    (hc : c1 ≤ c2) : a * e1 * c1 ≤ a * e2 * c2 :=
  mul_le_mul (mul_le_mul le_rfl he he0 ha) hc hc0 (mul_nonneg ha (le_trans he0 he))

theorem Ulo_le {Y t : ℚ} (hY0 : 0 ≤ Y) (hY : Y ≤ 5) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 5) :
    ((Ulo Y t : ℚ) : ℝ) ≤ U Y t := by
  have e1 := expLo_le (x := r1 ^ 2 * t) (by unfold r1; positivity)
  have e2 := expLo_le (x := r2 ^ 2 * t) (by unfold r2; positivity)
  have e3 := expLo_le (x := r3 ^ 2 * t) (by unfold r3; positivity)
  have c1 := coshLo_le (x := r1 * Y) (by unfold r1; positivity) (by unfold r1; linarith)
  have c2 := coshLo_le (x := r2 * Y) (by unfold r2; positivity) (by unfold r2; linarith)
  have c3 := coshLo_le (x := r3 * Y) (by unfold r3; positivity) (by unfold r3; linarith)
  have p1 : (0 : ℝ) ≤ expLo (r1 ^ 2 * t) := by exact_mod_cast (expLo_pos (by unfold r1; positivity)).le
  have p2 : (0 : ℝ) ≤ expLo (r2 ^ 2 * t) := by exact_mod_cast (expLo_pos (by unfold r2; positivity)).le
  have p3 : (0 : ℝ) ≤ expLo (r3 ^ 2 * t) := by exact_mod_cast (expLo_pos (by unfold r3; positivity)).le
  have q1 : (0 : ℝ) ≤ coshLo (r1 * Y) := by
    exact_mod_cast coshLo_nonneg (by unfold r1; positivity) (by unfold r1; linarith)
  have q2 : (0 : ℝ) ≤ coshLo (r2 * Y) := by
    exact_mod_cast coshLo_nonneg (by unfold r2; positivity) (by unfold r2; linarith)
  have q3 : (0 : ℝ) ≤ coshLo (r3 * Y) := by
    exact_mod_cast coshLo_nonneg (by unfold r3; positivity) (by unfold r3; linarith)
  unfold Ulo U a1 a2 a3
  simp only [r1, r2, r3] at e1 e2 e3 c1 c2 c3 p1 p2 p3 q1 q2 q3 ⊢
  push_cast at e1 e2 e3 c1 c2 c3 p1 p2 p3 q1 q2 q3 ⊢
  have h1 := mul3_le (by norm_num : (0 : ℝ) ≤ 1758974) p1 e1 q1 c1
  have h2 := mul3_le (by norm_num : (0 : ℝ) ≤ 2464729) p2 e2 q2 c2
  have h3 := mul3_le (by norm_num : (0 : ℝ) ≤ 302096) p3 e3 q3 c3
  linarith

theorem le_Uup {Y t : ℚ} (hY0 : 0 ≤ Y) (hY : Y ≤ 5) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 5) :
    U Y t ≤ ((Uup Y t : ℚ) : ℝ) := by
  have e1 := le_expUp (x := r1 ^ 2 * t) (by unfold r1; positivity) (by unfold r1; nlinarith)
  have e2 := le_expUp (x := r2 ^ 2 * t) (by unfold r2; positivity) (by unfold r2; nlinarith)
  have e3 := le_expUp (x := r3 ^ 2 * t) (by unfold r3; positivity) (by unfold r3; nlinarith)
  have c1 := le_coshUp (x := r1 * Y) (by unfold r1; positivity) (by unfold r1; linarith)
  have c2 := le_coshUp (x := r2 * Y) (by unfold r2; positivity) (by unfold r2; linarith)
  have c3 := le_coshUp (x := r3 * Y) (by unfold r3; positivity) (by unfold r3; linarith)
  have p1 := (Real.exp_pos (((r1 ^ 2 * t : ℚ)) : ℝ)).le
  have p2 := (Real.exp_pos (((r2 ^ 2 * t : ℚ)) : ℝ)).le
  have p3 := (Real.exp_pos (((r3 ^ 2 * t : ℚ)) : ℝ)).le
  have q1 := (Real.cosh_pos (((r1 * Y : ℚ)) : ℝ)).le
  have q2 := (Real.cosh_pos (((r2 * Y : ℚ)) : ℝ)).le
  have q3 := (Real.cosh_pos (((r3 * Y : ℚ)) : ℝ)).le
  unfold Uup U a1 a2 a3
  simp only [r1, r2, r3] at e1 e2 e3 c1 c2 c3 p1 p2 p3 q1 q2 q3 ⊢
  push_cast at e1 e2 e3 c1 c2 c3 p1 p2 p3 q1 q2 q3 ⊢
  have h1 := mul3_le (by norm_num : (0 : ℝ) ≤ 1758974) p1 e1 q1 c1
  have h2 := mul3_le (by norm_num : (0 : ℝ) ≤ 2464729) p2 e2 q2 c2
  have h3 := mul3_le (by norm_num : (0 : ℝ) ≤ 302096) p3 e3 q3 c3
  linarith

theorem UYlo_le {Y t : ℚ} (hY0 : 0 ≤ Y) (hY : Y ≤ 5) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 5) :
    ((UYlo Y t : ℚ) : ℝ) ≤ UY Y t := by
  have e1 := expLo_le (x := r1 ^ 2 * t) (by unfold r1; positivity)
  have e2 := expLo_le (x := r2 ^ 2 * t) (by unfold r2; positivity)
  have e3 := expLo_le (x := r3 ^ 2 * t) (by unfold r3; positivity)
  have c1 := sinhLo_le (x := r1 * Y) (by unfold r1; positivity)
  have c2 := sinhLo_le (x := r2 * Y) (by unfold r2; positivity)
  have c3 := sinhLo_le (x := r3 * Y) (by unfold r3; positivity)
  have p1 : (0 : ℝ) ≤ expLo (r1 ^ 2 * t) := by exact_mod_cast (expLo_pos (by unfold r1; positivity)).le
  have p2 : (0 : ℝ) ≤ expLo (r2 ^ 2 * t) := by exact_mod_cast (expLo_pos (by unfold r2; positivity)).le
  have p3 : (0 : ℝ) ≤ expLo (r3 ^ 2 * t) := by exact_mod_cast (expLo_pos (by unfold r3; positivity)).le
  have q1 : (0 : ℝ) ≤ sinhLo (r1 * Y) := by exact_mod_cast sinhLo_nonneg _
  have q2 : (0 : ℝ) ≤ sinhLo (r2 * Y) := by exact_mod_cast sinhLo_nonneg _
  have q3 : (0 : ℝ) ≤ sinhLo (r3 * Y) := by exact_mod_cast sinhLo_nonneg _
  unfold UYlo UY a1 a2 a3
  simp only [r1, r2, r3] at e1 e2 e3 c1 c2 c3 p1 p2 p3 q1 q2 q3 ⊢
  push_cast at e1 e2 e3 c1 c2 c3 p1 p2 p3 q1 q2 q3 ⊢
  have h1 := mul3_le (by norm_num : (0 : ℝ) ≤ 1758974 * (19 / 4)) p1 e1 q1 c1
  have h2 := mul3_le (by norm_num : (0 : ℝ) ≤ 2464729 * (97 / 20)) p2 e2 q2 c2
  have h3 := mul3_le (by norm_num : (0 : ℝ) ≤ 302096 * (131 / 20)) p3 e3 q3 c3
  linarith

theorem Ulo_pos {Y t : ℚ} (hY0 : 0 ≤ Y) (hY : Y ≤ 5) (ht0 : 0 ≤ t) : 0 < Ulo Y t := by
  unfold Ulo
  have p1 := (expLo_pos (x := r1 ^ 2 * t) (by unfold r1; positivity)).le
  have p2 := (expLo_pos (x := r2 ^ 2 * t) (by unfold r2; positivity)).le
  have p3 := (expLo_pos (x := r3 ^ 2 * t) (by unfold r3; positivity)).le
  have q1 := coshLo_nonneg (x := r1 * Y) (by unfold r1; positivity) (by unfold r1; linarith)
  have q2 := coshLo_nonneg (x := r2 * Y) (by unfold r2; positivity) (by unfold r2; linarith)
  have q3 := coshLo_nonneg (x := r3 * Y) (by unfold r3; positivity) (by unfold r3; linarith)
  have ha1 : (0 : ℚ) ≤ a1 := by unfold a1; norm_num
  have ha2 : (0 : ℚ) ≤ a2 := by unfold a2; norm_num
  have ha3 : (0 : ℚ) ≤ a3 := by unfold a3; norm_num
  have := mul_nonneg (mul_nonneg ha1 p1) q1
  have := mul_nonneg (mul_nonneg ha2 p2) q2
  have := mul_nonneg (mul_nonneg ha3 p3) q3
  linarith

/-! ### The gate checker and its soundness -/

theorem density_sound {s p tl : ℚ} (hp0 : 0 ≤ p) (hp : p ≤ 5) (ht0 : 0 ≤ tl) (ht : tl ≤ 1 / 5)
    (hs : 0 ≤ s) (h : (s + 1 / 100000) * Uup p tl < UYlo p tl) :
    (s : ℝ) + 1 / 100000 < f0 p tl := by
  unfold f0
  rw [lt_div_iff₀ (U_pos _ _)]
  have hU := le_Uup hp0 hp ht0 ht
  have hUY := UYlo_le hp0 hp ht0 ht
  have hs' : (0 : ℝ) ≤ (s : ℝ) + 1 / 100000 := by positivity
  calc ((s : ℝ) + 1 / 100000) * U p tl ≤ ((s : ℝ) + 1 / 100000) * ((Uup p tl : ℚ) : ℝ) :=
        mul_le_mul_of_nonneg_left hU hs'
    _ = (((s + 1 / 100000) * Uup p tl : ℚ) : ℝ) := by push_cast; ring
    _ < ((UYlo p tl : ℚ) : ℝ) := by exact_mod_cast h
    _ ≤ UY p tl := hUY

theorem jet_sound {p tl tr c : ℚ} (hp0 : 0 ≤ p) (hp : p ≤ 5) (ht0 : 0 ≤ tl) (ht : tl ≤ 1 / 5)
    (htr0 : 0 ≤ tr) (htr : tr ≤ 1 / 5)
    (h : expUp (tr / 100000) * (8 / 25 + 1130000000000 / Ulo p tl) ≤ c) : Cceil p tl tr ≤ c := by
  unfold Cceil
  have hU := Ulo_le hp0 hp ht0 ht
  have hUpos : (0 : ℝ) < ((Ulo p tl : ℚ) : ℝ) := by exact_mod_cast Ulo_pos hp0 hp ht0
  have hUpos' := U_pos (p : ℝ) tl
  have he := le_expUp (x := tr / 100000) (by positivity) (by linarith)
  have he' : ((tr / 100000 : ℚ) : ℝ) = (tr : ℝ) / 100000 := by push_cast; ring
  rw [he'] at he
  have hdiv : (1130000000000 : ℝ) / U p tl ≤ 1130000000000 / ((Ulo p tl : ℚ) : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hUpos hU
  calc Real.exp ((tr : ℝ) / 100000) * (8 / 25 + 1130000000000 / U p tl)
      ≤ ((expUp (tr / 100000) : ℚ) : ℝ) * (8 / 25 + 1130000000000 / ((Ulo p tl : ℚ) : ℝ)) := by
        apply mul_le_mul he (by linarith)
          (add_nonneg (by norm_num) (div_nonneg (by norm_num) hUpos'.le))
          (by exact_mod_cast (expUp_pos (x := tr / 100000) (by positivity) (by linarith)).le)
    _ = ((expUp (tr / 100000) * (8 / 25 + 1130000000000 / Ulo p tl) : ℚ) : ℝ) := by
        push_cast; ring
    _ ≤ (c : ℝ) := by exact_mod_cast h

/-- The Boolean gate check of one field certificate. -/
def checkCert (c : FieldCert) : Bool :=
  decide (0 ≤ c.p ∧ c.p ≤ 5 ∧ 0 ≤ c.otl ∧ c.otl ≤ 1 / 5 ∧ 0 ≤ c.s ∧
    (c.s + 1 / 100000) * Uup c.p c.otl < UYlo c.p c.otl) &&
  (!c.signed || decide (0 ≤ c.otr ∧ c.otr ≤ 1 / 5 ∧
    expUp (c.otr / 100000) * (8 / 25 + 1130000000000 / Ulo c.p c.otl) ≤ c.c))

/-- Rows without a field certificate have no gate. -/
def checkRow (r : Row) : Bool :=
  match r.cert with
  | .source _ => true
  | .field c => checkCert c

theorem checkCert_sound {c : FieldCert} (h : checkCert c = true) :
    (c.s : ℝ) + 1 / 100000 < f0 c.p c.otl ∧ (c.signed = true → Cceil c.p c.otl c.otr ≤ c.c) := by
  unfold checkCert at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hp0, hp, ht0, ht, hs, hd⟩, hj⟩ := h
  refine ⟨density_sound hp0 hp ht0 ht hs hd, fun hsg => ?_⟩
  rw [hsg, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hj
  obtain ⟨htr0, htr, hjet⟩ := hj
  exact jet_sound hp0 hp ht0 ht htr0 htr hjet

end DBN.Profile.Gate

namespace DBN.Profile.Gate

set_option maxRecDepth 100000

/-! ### Kernel evaluation on the frozen data (500-row chunks, as in `DBN.Check`) -/

theorem gates_main0 : Data.mainRows0.toList.all checkRow = true := by decide +kernel
theorem gates_main1 : Data.mainRows1.toList.all checkRow = true := by decide +kernel
theorem gates_main2 : Data.mainRows2.toList.all checkRow = true := by decide +kernel
theorem gates_main3 : Data.mainRows3.toList.all checkRow = true := by decide +kernel
theorem gates_main4 : Data.mainRows4.toList.all checkRow = true := by decide +kernel
theorem gates_main5 : Data.mainRows5.toList.all checkRow = true := by decide +kernel
theorem gates_main6 : Data.mainRows6.toList.all checkRow = true := by decide +kernel
theorem gates_main7 : Data.mainRows7.toList.all checkRow = true := by decide +kernel
theorem gates_main8 : Data.mainRows8.toList.all checkRow = true := by decide +kernel
theorem gates_main9 : Data.mainRows9.toList.all checkRow = true := by decide +kernel
theorem gates_fullC0 : Data.fullCRows0.toList.all checkRow = true := by decide +kernel
theorem gates_fullC1 : Data.fullCRows1.toList.all checkRow = true := by decide +kernel
theorem gates_fullC2 : Data.fullCRows2.toList.all checkRow = true := by decide +kernel
theorem gates_fullC3 : Data.fullCRows3.toList.all checkRow = true := by decide +kernel
theorem gates_fullC4 : Data.fullCRows4.toList.all checkRow = true := by decide +kernel
theorem gates_fullC5 : Data.fullCRows5.toList.all checkRow = true := by decide +kernel
theorem gates_fullC6 : Data.fullCRows6.toList.all checkRow = true := by decide +kernel
theorem gates_fullC7 : Data.fullCRows7.toList.all checkRow = true := by decide +kernel
theorem gates_fullC8 : Data.fullCRows8.toList.all checkRow = true := by decide +kernel
theorem gates_fullC9 : Data.fullCRows9.toList.all checkRow = true := by decide +kernel
theorem gates_fullC10 : Data.fullCRows10.toList.all checkRow = true := by decide +kernel
theorem gates_fullC11 : Data.fullCRows11.toList.all checkRow = true := by decide +kernel
theorem gates_fullC12 : Data.fullCRows12.toList.all checkRow = true := by decide +kernel
theorem gates_fullC13 : Data.fullCRows13.toList.all checkRow = true := by decide +kernel
theorem gates_fullC14 : Data.fullCRows14.toList.all checkRow = true := by decide +kernel
theorem gates_fullC15 : Data.fullCRows15.toList.all checkRow = true := by decide +kernel

theorem gates_all : (Data.mainRows ++ Data.fullCRows).all checkRow = true := by
  simp only [Data.mainRows, Data.fullCRows, List.all_append,
    gates_main0, gates_main1, gates_main2, gates_main3, gates_main4, gates_main5, gates_main6,
    gates_main7, gates_main8, gates_main9,
    gates_fullC0, gates_fullC1, gates_fullC2, gates_fullC3, gates_fullC4, gates_fullC5, gates_fullC6,
    gates_fullC7, gates_fullC8, gates_fullC9, gates_fullC10, gates_fullC11, gates_fullC12,
    gates_fullC13, gates_fullC14, gates_fullC15, Bool.and_self]

end DBN.Profile.Gate

namespace DBN.Profile

/-- **All P8 endpoint gates hold**, by kernel evaluation of the verified fixed-point evaluator on
every field certificate of both barriers. -/
theorem profileCellGates_proved : ProfileCellGates := by
  intro r hr c hc
  have h := List.all_eq_true.mp Gate.gates_all r hr
  simp only [Gate.checkRow, hc] at h
  exact Gate.checkCert_sound h

end DBN.Profile
