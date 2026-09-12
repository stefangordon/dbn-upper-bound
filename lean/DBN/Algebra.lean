import Mathlib

/-!
# Algebraic force lemmas

These are the exact (real-number) inequalities that turn a certified row into the strict
velocity comparison `q_zero' < Q'` at a first contact. They are pure algebra; the analytic
inputs (zero velocity, kernel minorants, field floors) enter only as hypotheses in `Main`.
-/

noncomputable section

namespace DBN.Algebra

open Real

/-- **Source force.** Let `a ≥ 0`, `b > 0`, `0 < qR ≤ q`. If the strict sqrt-speed gate
`w ≤ a ∨ (a < w ∧ (w-a)² < b² qR)` holds, then `-a - b √q < -w`. With `a = 2/15`, `b = 4L`
this says the source law `q' ≤ -2/15 - 4√q L` beats the affine slope `w` on the whole row. -/
theorem source_force {a b w qR q : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hqR : 0 < qR) (hq : qR ≤ q)
    (gate : w ≤ a ∨ (a < w ∧ (w - a) ^ 2 < b ^ 2 * qR)) :
    -a - b * Real.sqrt q < -w := by
  have hsq : Real.sqrt qR ≤ Real.sqrt q := Real.sqrt_le_sqrt hq
  have hpos : 0 < Real.sqrt qR := Real.sqrt_pos.mpr hqR
  have hb' : 0 < b * Real.sqrt qR := mul_pos hb hpos
  have hbq : b * Real.sqrt qR ≤ b * Real.sqrt q := mul_le_mul_of_nonneg_left hsq hb.le
  rcases gate with h | ⟨h1, h2⟩
  · linarith
  · have h3 : (w - a) ^ 2 < (b * Real.sqrt qR) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hqR.le]; exact h2
    have h4 : w - a < b * Real.sqrt qR := by
      by_contra hcon
      have hcon' : b * Real.sqrt qR ≤ w - a := not_lt.mp hcon
      have : (b * Real.sqrt qR) ^ 2 ≤ (w - a) ^ 2 := by nlinarith
      linarith
    linarith

/-- The distinguished self-pair contribution of the `(3h,4h,5h)` stencil equals `7/(15h)`. -/
theorem self_term (h : ℝ) (hh : h ≠ 0) :
    (15 / 14) * (2 * (3 * h) / ((3 * h) ^ 2 - h ^ 2)) - (16 / 21) * (2 * (4 * h) / ((4 * h) ^ 2 - h ^ 2))
      + (1 / 6) * (2 * (5 * h) / ((5 * h) ^ 2 - h ^ 2)) = 7 / (15 * h) := by
  have e1 : (3 * h) ^ 2 - h ^ 2 = 8 * h ^ 2 := by ring
  have e2 : (4 * h) ^ 2 - h ^ 2 = 15 * h ^ 2 := by ring
  have e3 : (5 * h) ^ 2 - h ^ 2 = 24 * h ^ 2 := by ring
  rw [e1, e2, e3]
  field_simp
  try ring

/-- Stencil admissibility `Σ 4h²/(Y_j² − h²) = 14/15 ≤ 1` for `Y = (3h,4h,5h)`. -/
theorem stencil_admissible (h : ℝ) (hh : h ≠ 0) :
    4 * h ^ 2 / ((3 * h) ^ 2 - h ^ 2) + 4 * h ^ 2 / ((4 * h) ^ 2 - h ^ 2) + 4 * h ^ 2 / ((5 * h) ^ 2 - h ^ 2)
      = 14 / 15 := by
  have e1 : (3 * h) ^ 2 - h ^ 2 = 8 * h ^ 2 := by ring
  have e2 : (4 * h) ^ 2 - h ^ 2 = 15 * h ^ 2 := by ring
  have e3 : (5 * h) ^ 2 - h ^ 2 = 24 * h ^ 2 := by ring
  rw [e1, e2, e3]
  field_simp
  try ring

/-- Unsigned field coefficient `K_u(q) = 4s/p − 8/(p² − q)`. -/
def Ku (s p q : ℝ) : ℝ := 4 * s / p - 8 / (p ^ 2 - q)
/-- Signed field coefficient. -/
def Ks (s p L0 q : ℝ) : ℝ := 6 * s / p - 2 * L0 + q * (2 * L0 / p ^ 2 - 2 * s / p ^ 3) - 16 / (p ^ 2 - q)

/-- `K_u` is non-increasing in `q` below `p²`. -/
theorem Ku_antitone {s p q1 q2 : ℝ} (h1 : q1 ≤ q2) (h2 : q2 < p ^ 2) : Ku s p q2 ≤ Ku s p q1 := by
  unfold Ku
  have hA : 0 < p ^ 2 - q2 := by linarith
  have : 8 / (p ^ 2 - q1) ≤ 8 / (p ^ 2 - q2) :=
    div_le_div_of_nonneg_left (by norm_num) hA (by linarith)
  linarith

/-- `K_s` is non-increasing in `q` below `p²` provided `p L0 ≤ s` and `p > 0`. -/
theorem Ks_antitone {s p L0 q1 q2 : ℝ} (hp : 0 < p) (hL : p * L0 ≤ s) (h1 : q1 ≤ q2) (h2 : q2 < p ^ 2) :
    Ks s p L0 q2 ≤ Ks s p L0 q1 := by
  have hA : 0 < p ^ 2 - q2 := by linarith
  have hfrac : 16 / (p ^ 2 - q1) ≤ 16 / (p ^ 2 - q2) :=
    div_le_div_of_nonneg_left (by norm_num) hA (by linarith)
  have hp3 : 0 < p ^ 3 := by positivity
  have hcoef : 2 * L0 / p ^ 2 - 2 * s / p ^ 3 ≤ 0 := by
    have e : 2 * L0 / p ^ 2 - 2 * s / p ^ 3 = 2 * (p * L0 - s) / p ^ 3 := by
      field_simp
      try ring
    rw [e]
    apply div_nonpos_of_nonpos_of_nonneg _ hp3.le
    linarith
  have hprod : (q2 - q1) * (2 * L0 / p ^ 2 - 2 * s / p ^ 3) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hcoef
  have key : Ks s p L0 q2 - Ks s p L0 q1
      = (q2 - q1) * (2 * L0 / p ^ 2 - 2 * s / p ^ 3) + (16 / (p ^ 2 - q1) - 16 / (p ^ 2 - q2)) := by
    unfold Ks; ring
  linarith

/-- **Minimized-Ω branch.** For `a > 0`, `s ≤ Ω_L ≤ Ω`, `S ≥ s` and the branch gate
`2a(Ω_L − s) ≤ 1`: `S − a c + a (S − Ω)² ≥ s − a (c − (Ω_L − s)²)`. -/
theorem omega_branch {a s OmegaL Omega S c : ℝ} (ha : 0 < a) (hδ : s ≤ OmegaL) (hΩ : OmegaL ≤ Omega)
    (hS : s ≤ S) (hgate : 2 * a * (OmegaL - s) ≤ 1) :
    s - a * (c - (OmegaL - s) ^ 2) ≤ S - a * c + a * (S - Omega) ^ 2 := by
  have h1 : 0 ≤ (S - s) * (1 - 2 * a * (OmegaL - s)) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ a * (S - s - (Omega - OmegaL)) ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  have h3 : 0 ≤ a * (OmegaL - s) * (Omega - OmegaL) :=
    mul_nonneg (mul_nonneg ha.le (by linarith)) (by linarith)
  nlinarith

/-- Strict version: if moreover `Ω_L < Ω` and `s < Ω_L`, the inequality is strict. -/
theorem omega_branch_strict {a s OmegaL Omega S c : ℝ} (ha : 0 < a) (hδ : s < OmegaL) (hΩ : OmegaL < Omega)
    (hS : s ≤ S) (hgate : 2 * a * (OmegaL - s) ≤ 1) :
    s - a * (c - (OmegaL - s) ^ 2) < S - a * c + a * (S - Omega) ^ 2 := by
  have h1 : 0 ≤ (S - s) * (1 - 2 * a * (OmegaL - s)) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ a * (S - s - (Omega - OmegaL)) ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  have h3 : 0 < a * (OmegaL - s) * (Omega - OmegaL) :=
    mul_pos (mul_pos ha (by linarith)) (by linarith)
  nlinarith

/-- The signed coefficient identity `2(3P−q)(s − a(q)L0)/p³ − 16/(P−q) = K_s(q)` with
`a(q) = p(P−q)/(3P−q)`, `P = p²`. -/
theorem Ks_factorization {s p L0 q : ℝ} (hp : 0 < p) (hq : q < p ^ 2) (h3 : 0 < 3 * p ^ 2 - q) :
    2 * (3 * p ^ 2 - q) * (s - (p * (p ^ 2 - q) / (3 * p ^ 2 - q)) * L0) / p ^ 3 - 16 / (p ^ 2 - q)
      = Ks s p L0 q := by
  unfold Ks
  have hpq : p ^ 2 - q ≠ 0 := by linarith
  have h3' : 3 * p ^ 2 - q ≠ 0 := h3.ne'
  have hp' : p ≠ 0 := hp.ne'
  field_simp
  try ring

/-- **Unsigned row force.** With `S > s`, `p > 0`, `0 < qR ≤ q ≤ qL < p²`, `k = K_u(qL) > 0` and
the speed gate `w ≤ 2 + k qR`:  `-2 - 4qS/p + 8q/(p²−q) < -w`. -/
theorem unsigned_row_force {s p qR q qL w S : ℝ} (hp : 0 < p) (hqR : 0 < qR) (hq1 : qR ≤ q) (hq2 : q ≤ qL)
    (hqL : qL < p ^ 2) (hk : 0 < Ku s p qL) (hw : w ≤ 2 + Ku s p qL * qR) (hS : s < S) :
    -2 - 4 * q * S / p + 8 * q / (p ^ 2 - q) < -w := by
  have hq : 0 < q := lt_of_lt_of_le hqR hq1
  have hKq : Ku s p qL ≤ Ku s p q := Ku_antitone hq2 hqL
  have e : -2 - 4 * q * s / p + 8 * q / (p ^ 2 - q) = -2 - q * Ku s p q := by
    unfold Ku
    have : p ^ 2 - q ≠ 0 := by linarith
    field_simp
    try ring
  have hstrict : 4 * q * s / p < 4 * q * S / p := by
    apply div_lt_div_of_pos_right _ hp
    nlinarith
  have h1 : -2 - q * Ku s p q ≤ -2 - q * Ku s p qL := by nlinarith
  have h2 : -2 - q * Ku s p qL ≤ -2 - qR * Ku s p qL := by nlinarith
  linarith

/-- **Signed row force.** Let `P = p²`, `q ∈ [qR, qL]`, `9 qL ≤ P`, `α = h(3P−q)/(2p³)`, `a = p(P−q)/(3P−q)`.
Given the jet lower bound `D ≥ s − a L0` (from `omega_branch`) with `L0 = c − (Ω_L − s)²`,
`k = K_s(qL) > 0`, `p L0 ≤ s`, and the speed gate `w ≤ 2 + k qR`:
`-2 - 4hαD + 16q/(P−q) ≤ -w`, where `q = h²`. Strictness is supplied by `omega_branch_strict`. -/
theorem signed_row_force {s p L0 qR qL w h D : ℝ} (hp : 0 < p) (hqR : 0 < qR) (hq1 : qR ≤ h ^ 2)
    (hq2 : h ^ 2 ≤ qL) (h9 : 9 * qL ≤ p ^ 2) (hL : p * L0 ≤ s) (hk : 0 < Ks s p L0 qL)
    (hw : w ≤ 2 + Ks s p L0 qL * qR)
    (hD : s - (p * (p ^ 2 - h ^ 2) / (3 * p ^ 2 - h ^ 2)) * L0 ≤ D) :
    -2 - 4 * h * (h * (3 * p ^ 2 - h ^ 2) / (2 * p ^ 3)) * D + 16 * h ^ 2 / (p ^ 2 - h ^ 2) ≤ -w := by
  set q := h ^ 2 with hqdef
  have hq : 0 < q := lt_of_lt_of_le hqR hq1
  have hqLP : qL < p ^ 2 := by nlinarith
  have hqP : q < p ^ 2 := by linarith
  have h3 : 0 < 3 * p ^ 2 - q := by nlinarith
  have hp3 : 0 < p ^ 3 := by positivity
  set A := 2 * q * (3 * p ^ 2 - q) / p ^ 3 with hAdef
  set E := s - (p * (p ^ 2 - q) / (3 * p ^ 2 - q)) * L0 with hEdef
  have eα : 4 * h * (h * (3 * p ^ 2 - q) / (2 * p ^ 3)) = A := by
    rw [hAdef, hqdef]; field_simp; try ring
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  have hAE : A * E ≤ A * D := mul_le_mul_of_nonneg_left hD hA
  -- -2 - q K_s(q) = -2 - A E + 16 q/(p² - q)
  have eK : q * Ks s p L0 q = A * E - 16 * q / (p ^ 2 - q) := by
    rw [← Ks_factorization hp hqP h3, hAdef, hEdef]
    have : p ^ 2 - q ≠ 0 := by linarith
    field_simp
    try ring
  have hKq : Ks s p L0 qL ≤ Ks s p L0 q := Ks_antitone hp hL hq2 hqLP
  have h1 : q * Ks s p L0 qL ≤ q * Ks s p L0 q := mul_le_mul_of_nonneg_left hKq hq.le
  have h2 : qR * Ks s p L0 qL ≤ q * Ks s p L0 qL := mul_le_mul_of_nonneg_right hq1 hk.le
  rw [eα]
  linarith

/-- `a(q) = p(P−q)/(3P−q)` is non-increasing in `q` below `P = p²`. -/
theorem a_antitone {p q1 q2 : ℝ} (hp : 0 < p) (h1 : q1 ≤ q2) (h2 : q2 < p ^ 2) :
    p * (p ^ 2 - q2) / (3 * p ^ 2 - q2) ≤ p * (p ^ 2 - q1) / (3 * p ^ 2 - q1) := by
  have hA : 0 < 3 * p ^ 2 - q2 := by nlinarith
  have hB : 0 < 3 * p ^ 2 - q1 := by nlinarith
  rw [div_le_div_iff₀ hA hB]
  nlinarith [mul_nonneg (mul_nonneg hp.le (sq_nonneg p)) (sub_nonneg.mpr h1)]

/-- `a(q) > 0` for `q < p²`. -/
theorem a_pos {p q : ℝ} (hp : 0 < p) (hq : q < p ^ 2) : 0 < p * (p ^ 2 - q) / (3 * p ^ 2 - q) := by
  have hA : 0 < 3 * p ^ 2 - q := by nlinarith
  exact div_pos (mul_pos hp (by linarith)) hA

/-- Strict signed row force: with `D > s − a L0` the comparison is strict. -/
theorem signed_row_force_strict {s p L0 qR qL w h D : ℝ} (hp : 0 < p) (hh : 0 < h) (hqR : 0 < qR)
    (hq1 : qR ≤ h ^ 2) (hq2 : h ^ 2 ≤ qL) (h9 : 9 * qL ≤ p ^ 2) (hL : p * L0 ≤ s) (hk : 0 < Ks s p L0 qL)
    (hw : w ≤ 2 + Ks s p L0 qL * qR)
    (hD : s - (p * (p ^ 2 - h ^ 2) / (3 * p ^ 2 - h ^ 2)) * L0 < D) :
    -2 - 4 * h * (h * (3 * p ^ 2 - h ^ 2) / (2 * p ^ 3)) * D + 16 * h ^ 2 / (p ^ 2 - h ^ 2) < -w := by
  have hqP : h ^ 2 < p ^ 2 := by nlinarith
  have h3 : 0 < 3 * p ^ 2 - h ^ 2 := by nlinarith
  have hαpos : 0 < 4 * h * (h * (3 * p ^ 2 - h ^ 2) / (2 * p ^ 3)) := by positivity
  have base := signed_row_force hp hqR hq1 hq2 h9 hL hk hw
    (le_refl (s - (p * (p ^ 2 - h ^ 2) / (3 * p ^ 2 - h ^ 2)) * L0))
  have := mul_lt_mul_of_pos_left hD hαpos
  linarith

end DBN.Algebra

end
