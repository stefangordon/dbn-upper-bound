import Mathlib

/-!
# Kernel minorants (manuscript P6)

For a zero pair at horizontal distance `d` and height `b ≥ 0`, and a probe height `y > b`, the
conjugate-pair Poisson kernel is

  `K y d b = (y - b)/(d² + (y - b)²) + (y + b)/(d² + (y + b)²)`.

We prove the three pointwise minorants used by the force laws, for `0 ≤ b ≤ h` and all `d`
(with the pair not coinciding with the contact zero, i.e. `d² + (h - b)² > 0`):

* (a) unsigned: `K h d b ≥ (h/p) K p d b` when `p² ≥ 5h²`;
* (b) three-probe: `K h d b ≥ (15/14) K (3h) d b − (16/21) K (4h) d b + (1/6) K (5h) d b`;
* (c) signed confluent: `K h d b ≥ α (K p d b − a ∂ₚK p d b)` when `p² ≥ 9h²`, with
  `α = h(3p²−h²)/(2p³)`, `a = p(p²−h²)/(3p²−h²)`.

Each proof clears denominators (an exact rational identity) and shows the numerator is a
polynomial in `D = d²`, `B = b²`, `H = h²` (and `P = p²`) with nonnegative coefficients on the
region `0 ≤ B ≤ H`, `D ≥ 0`. The coefficient decompositions were obtained with a computer algebra
system and are re-verified here by `ring`.
-/

noncomputable section

namespace DBN.Kernels

/-- Conjugate-pair Poisson kernel at probe height `y`. -/
def K (y d b : ℝ) : ℝ := (y - b) / (d ^ 2 + (y - b) ^ 2) + (y + b) / (d ^ 2 + (y + b) ^ 2)

/-- `∂ₚ K p d b`. -/
def dK (y d b : ℝ) : ℝ :=
  (d ^ 2 - (y - b) ^ 2) / (d ^ 2 + (y - b) ^ 2) ^ 2 + (d ^ 2 - (y + b) ^ 2) / (d ^ 2 + (y + b) ^ 2) ^ 2

theorem hasDerivAt_K (y d b : ℝ) (h1 : d ^ 2 + (y - b) ^ 2 ≠ 0) (h2 : d ^ 2 + (y + b) ^ 2 ≠ 0) :
    HasDerivAt (fun y => K y d b) (dK y d b) y := by
  have hn1 : HasDerivAt (fun y : ℝ => y - b) 1 y := (hasDerivAt_id' y).sub_const b
  have hn2 : HasDerivAt (fun y : ℝ => y + b) 1 y := (hasDerivAt_id' y).add_const b
  have hA : HasDerivAt (fun y : ℝ => d ^ 2 + (y - b) ^ 2) (2 * (y - b)) y := by
    have h := (hn1.pow 2).const_add (d ^ 2)
    refine h.congr_deriv ?_
    simp
  have hB : HasDerivAt (fun y : ℝ => d ^ 2 + (y + b) ^ 2) (2 * (y + b)) y := by
    have h := (hn2.pow 2).const_add (d ^ 2)
    refine h.congr_deriv ?_
    simp
  have h := (hn1.div hA h1).add (hn2.div hB h2)
  unfold K dK
  refine h.congr_deriv ?_
  ring

/-- Combined form `K y d b = 2y (d² + y² − b²) / ((d² + (y−b)²)(d² + (y+b)²))`. -/
theorem K_eq (y d b : ℝ) (h1 : d ^ 2 + (y - b) ^ 2 ≠ 0) (h2 : d ^ 2 + (y + b) ^ 2 ≠ 0) :
    K y d b = 2 * y * (d ^ 2 + y ^ 2 - b ^ 2) / ((d ^ 2 + (y - b) ^ 2) * (d ^ 2 + (y + b) ^ 2)) := by
  unfold K
  rw [div_add_div _ _ h1 h2]
  congr 1
  ring

theorem den_pos_of_lt (d : ℝ) {y b : ℝ} (hb : 0 ≤ b) (hy : b < y) :
    0 < d ^ 2 + (y - b) ^ 2 ∧ 0 < d ^ 2 + (y + b) ^ 2 := by
  constructor <;> nlinarith [sq_nonneg d, sq_nonneg (y - b), sq_nonneg (y + b)]

/-- **(a) Unsigned minorant.** -/
theorem unsigned {h p d b : ℝ} (hb : 0 ≤ b) (hbh : b ≤ h) (hh : 0 < h) (hp : h < p)
    (h5 : 5 * h ^ 2 ≤ p ^ 2) (hne : 0 < d ^ 2 + (h - b) ^ 2) :
    (h / p) * K p d b ≤ K h d b := by
  have hp0 : 0 < p := lt_trans hh hp
  have hA : 0 < d ^ 2 + (h + b) ^ 2 := by nlinarith [sq_nonneg d]
  obtain ⟨hC, hD⟩ := den_pos_of_lt d hb (lt_of_le_of_lt hbh hp)
  have hne' := hne.ne'
  have hA' := hA.ne'
  have hC' := hC.ne'
  have hD' := hD.ne'
  have hp' := hp0.ne'
  rw [K_eq h d b hne' hA', K_eq p d b hC' hD']
  have e1 : h / p * (2 * p * (d ^ 2 + p ^ 2 - b ^ 2) / ((d ^ 2 + (p - b) ^ 2) * (d ^ 2 + (p + b) ^ 2)))
      = 2 * h * (d ^ 2 + p ^ 2 - b ^ 2) / ((d ^ 2 + (p - b) ^ 2) * (d ^ 2 + (p + b) ^ 2)) := by
    rw [div_mul_div_comm, show h * (2 * p * (d ^ 2 + p ^ 2 - b ^ 2)) = p * (2 * h * (d ^ 2 + p ^ 2 - b ^ 2)) by ring,
      mul_div_mul_left _ _ hp']
  rw [e1, ← sub_nonneg, div_sub_div _ _ (mul_ne_zero hne' hA') (mul_ne_zero hC' hD')]
  apply div_nonneg _ (by positivity)
  have e : 2 * h * (d ^ 2 + h ^ 2 - b ^ 2) * ((d ^ 2 + (p - b) ^ 2) * (d ^ 2 + (p + b) ^ 2))
        - (d ^ 2 + (h - b) ^ 2) * (d ^ 2 + (h + b) ^ 2) * (2 * h * (d ^ 2 + p ^ 2 - b ^ 2))
      = 2 * h * (p ^ 2 - h ^ 2) *
          ((d ^ 2) ^ 2 + (h ^ 2 + p ^ 2 - 6 * b ^ 2) * d ^ 2 + (h ^ 2 - b ^ 2) * (p ^ 2 - b ^ 2)) := by
    ring
  rw [e]
  have c1 : 0 ≤ h ^ 2 + p ^ 2 - 6 * b ^ 2 := by nlinarith
  have c0 : 0 ≤ (h ^ 2 - b ^ 2) * (p ^ 2 - b ^ 2) := mul_nonneg (by nlinarith) (by nlinarith)
  have hph : 0 ≤ p ^ 2 - h ^ 2 := by nlinarith
  apply mul_nonneg (mul_nonneg (by positivity) hph)
  nlinarith [sq_nonneg (d ^ 2), mul_nonneg c1 (sq_nonneg d)]

/-- **(c) Signed confluent minorant.** -/
theorem signed {h p d b : ℝ} (hb : 0 ≤ b) (hbh : b ≤ h) (hh : 0 < h) (hp : h < p)
    (h9 : 9 * h ^ 2 ≤ p ^ 2) (hne : 0 < d ^ 2 + (h - b) ^ 2) :
    (h * (3 * p ^ 2 - h ^ 2) / (2 * p ^ 3)) *
        (K p d b - (p * (p ^ 2 - h ^ 2) / (3 * p ^ 2 - h ^ 2)) * dK p d b) ≤ K h d b := by
  have hp0 : 0 < p := lt_trans hh hp
  have hA : 0 < d ^ 2 + (h + b) ^ 2 := by nlinarith [sq_nonneg d]
  obtain ⟨hC, hD⟩ := den_pos_of_lt d hb (lt_of_le_of_lt hbh hp)
  have h3 : 0 < 3 * p ^ 2 - h ^ 2 := by nlinarith
  have hne' := hne.ne'
  have hA' := hA.ne'
  have hC' := hC.ne'
  have hD' := hD.ne'
  have hp' := hp0.ne'
  have h3' := h3.ne'
  rw [← sub_nonneg]
  have key : K h d b - (h * (3 * p ^ 2 - h ^ 2) / (2 * p ^ 3)) *
        (K p d b - (p * (p ^ 2 - h ^ 2) / (3 * p ^ 2 - h ^ 2)) * dK p d b)
      = 2 * h * (p ^ 2 - h ^ 2) ^ 2 *
          ((d ^ 2) ^ 3 + (h ^ 2 + 2 * p ^ 2 - 15 * b ^ 2) * (d ^ 2) ^ 2
            + (15 * (b ^ 2) ^ 2 - 6 * b ^ 2 * h ^ 2 - 12 * b ^ 2 * p ^ 2 + 2 * h ^ 2 * p ^ 2 + (p ^ 2) ^ 2) * d ^ 2
            + (h ^ 2 - b ^ 2) * (p ^ 2 - b ^ 2) ^ 2) /
        ((d ^ 2 + (h - b) ^ 2) * (d ^ 2 + (h + b) ^ 2) * (d ^ 2 + (p - b) ^ 2) ^ 2 * (d ^ 2 + (p + b) ^ 2) ^ 2) := by
    unfold K dK
    field_simp
    ring
  rw [key]
  apply div_nonneg _ (by positivity)
  have c2 : 0 ≤ h ^ 2 + 2 * p ^ 2 - 15 * b ^ 2 := by nlinarith
  have c1 : 0 ≤ 15 * (b ^ 2) ^ 2 - 6 * b ^ 2 * h ^ 2 - 12 * b ^ 2 * p ^ 2 + 2 * h ^ 2 * p ^ 2 + (p ^ 2) ^ 2 := by
    have e : 15 * (b ^ 2) ^ 2 - 6 * b ^ 2 * h ^ 2 - 12 * b ^ 2 * p ^ 2 + 2 * h ^ 2 * p ^ 2 + (p ^ 2) ^ 2
        = (p ^ 2 - h ^ 2) * (p ^ 2 - 9 * h ^ 2) + (h ^ 2 - b ^ 2) * (12 * p ^ 2 - 9 * h ^ 2 - 15 * b ^ 2) := by
      ring
    rw [e]
    have t1 : 0 ≤ (p ^ 2 - h ^ 2) * (p ^ 2 - 9 * h ^ 2) := mul_nonneg (by nlinarith) (by nlinarith)
    have t2 : 0 ≤ (h ^ 2 - b ^ 2) * (12 * p ^ 2 - 9 * h ^ 2 - 15 * b ^ 2) := mul_nonneg (by nlinarith) (by nlinarith)
    linarith
  have c0 : 0 ≤ (h ^ 2 - b ^ 2) * (p ^ 2 - b ^ 2) ^ 2 := mul_nonneg (by nlinarith) (sq_nonneg _)
  apply mul_nonneg (by positivity)
  nlinarith [pow_nonneg (sq_nonneg d) 3, mul_nonneg c2 (sq_nonneg (d ^ 2)), mul_nonneg c1 (sq_nonneg d)]

set_option maxHeartbeats 4000000 in
/-- **(b) Three-probe minorant** with the stencil `(15/14, −16/21, 1/6)` at heights `3h, 4h, 5h`. -/
theorem threeProbe {h d b : ℝ} (hb : 0 ≤ b) (hbh : b ≤ h) (hh : 0 < h) (hne : 0 < d ^ 2 + (h - b) ^ 2) :
    (15 / 14) * K (3 * h) d b - (16 / 21) * K (4 * h) d b + (1 / 6) * K (5 * h) d b ≤ K h d b := by
  have hA : 0 < d ^ 2 + (h + b) ^ 2 := by nlinarith [sq_nonneg d]
  obtain ⟨h3a, h3b⟩ := den_pos_of_lt d hb (show b < 3 * h by linarith)
  obtain ⟨h4a, h4b⟩ := den_pos_of_lt d hb (show b < 4 * h by linarith)
  obtain ⟨h5a, h5b⟩ := den_pos_of_lt d hb (show b < 5 * h by linarith)
  have hne' := hne.ne'
  have hA' := hA.ne'
  have h3a' := h3a.ne'
  have h3b' := h3b.ne'
  have h4a' := h4a.ne'
  have h4b' := h4b.ne'
  have h5a' := h5a.ne'
  have h5b' := h5b.ne'
  rw [← sub_nonneg]
  have key : K h d b - ((15 / 14) * K (3 * h) d b - (16 / 21) * K (4 * h) d b + (1 / 6) * K (5 * h) d b)
      = 5760 * h ^ 7 *
          ((d ^ 2) ^ 4 + (51 * h ^ 2 - 28 * b ^ 2) * (d ^ 2) ^ 3
            + (70 * (b ^ 2) ^ 2 - 765 * b ^ 2 * h ^ 2 + 819 * (h ^ 2) ^ 2) * (d ^ 2) ^ 2
            + (-28 * (b ^ 2) ^ 3 + 765 * (b ^ 2) ^ 2 * h ^ 2 - 4914 * b ^ 2 * (h ^ 2) ^ 2 + 4369 * (h ^ 2) ^ 3) * d ^ 2
            + (h ^ 2 - b ^ 2) * (9 * h ^ 2 - b ^ 2) * (16 * h ^ 2 - b ^ 2) * (25 * h ^ 2 - b ^ 2)) /
        ((d ^ 2 + (h - b) ^ 2) * (d ^ 2 + (h + b) ^ 2) * (d ^ 2 + (3 * h - b) ^ 2) * (d ^ 2 + (3 * h + b) ^ 2)
          * (d ^ 2 + (4 * h - b) ^ 2) * (d ^ 2 + (4 * h + b) ^ 2)
          * (d ^ 2 + (5 * h - b) ^ 2) * (d ^ 2 + (5 * h + b) ^ 2)) := by
    unfold K
    set A1 := d ^ 2 + (h - b) ^ 2 with hA1
    set A2 := d ^ 2 + (h + b) ^ 2 with hA2
    set A3 := d ^ 2 + (3 * h - b) ^ 2 with hA3
    set A4 := d ^ 2 + (3 * h + b) ^ 2 with hA4
    set A5 := d ^ 2 + (4 * h - b) ^ 2 with hA5
    set A6 := d ^ 2 + (4 * h + b) ^ 2 with hA6
    set A7 := d ^ 2 + (5 * h - b) ^ 2 with hA7
    set A8 := d ^ 2 + (5 * h + b) ^ 2 with hA8
    rw [div_add_div _ _ hne' hA', div_add_div _ _ h3a' h3b', div_add_div _ _ h4a' h4b', div_add_div _ _ h5a' h5b']
    rw [eq_div_iff (by positivity)]
    field_simp
    rw [hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8]
    ring
  rw [key]
  apply div_nonneg _ (by positivity)
  have hBH : b ^ 2 ≤ h ^ 2 := by nlinarith
  have hB0 : 0 ≤ b ^ 2 := sq_nonneg b
  have c3 : 0 ≤ 51 * h ^ 2 - 28 * b ^ 2 := by nlinarith
  have c2 : 0 ≤ 70 * (b ^ 2) ^ 2 - 765 * b ^ 2 * h ^ 2 + 819 * (h ^ 2) ^ 2 := by
    have e : 70 * (b ^ 2) ^ 2 - 765 * b ^ 2 * h ^ 2 + 819 * (h ^ 2) ^ 2
        = 124 * (h ^ 2) ^ 2 + (h ^ 2 - b ^ 2) * (695 * h ^ 2 - 70 * b ^ 2) := by ring
    rw [e]
    have t : 0 ≤ (h ^ 2 - b ^ 2) * (695 * h ^ 2 - 70 * b ^ 2) := mul_nonneg (by linarith) (by nlinarith)
    nlinarith [sq_nonneg (h ^ 2)]
  have c1 : 0 ≤ -28 * (b ^ 2) ^ 3 + 765 * (b ^ 2) ^ 2 * h ^ 2 - 4914 * b ^ 2 * (h ^ 2) ^ 2 + 4369 * (h ^ 2) ^ 3 := by
    have e : -28 * (b ^ 2) ^ 3 + 765 * (b ^ 2) ^ 2 * h ^ 2 - 4914 * b ^ 2 * (h ^ 2) ^ 2 + 4369 * (h ^ 2) ^ 3
        = 192 * (h ^ 2) ^ 3 + (h ^ 2 - b ^ 2) * (3468 * (h ^ 2) ^ 2 + (h ^ 2 - b ^ 2) * (709 * h ^ 2 - 28 * b ^ 2)) := by
      ring
    rw [e]
    have t1 : 0 ≤ (h ^ 2 - b ^ 2) * (709 * h ^ 2 - 28 * b ^ 2) := mul_nonneg (by linarith) (by nlinarith)
    have t2 : 0 ≤ (h ^ 2 - b ^ 2) * (3468 * (h ^ 2) ^ 2 + (h ^ 2 - b ^ 2) * (709 * h ^ 2 - 28 * b ^ 2)) :=
      mul_nonneg (by linarith) (by nlinarith [sq_nonneg (h ^ 2)])
    nlinarith [pow_nonneg (sq_nonneg h) 3]
  have c0 : 0 ≤ (h ^ 2 - b ^ 2) * (9 * h ^ 2 - b ^ 2) * (16 * h ^ 2 - b ^ 2) * (25 * h ^ 2 - b ^ 2) := by
    apply mul_nonneg (mul_nonneg (mul_nonneg _ _) _) _ <;> nlinarith
  apply mul_nonneg (by positivity)
  have hD := sq_nonneg d
  nlinarith [pow_nonneg hD 4, pow_nonneg hD 3, mul_nonneg c3 (pow_nonneg hD 3), mul_nonneg c2 (pow_nonneg hD 2),
    mul_nonneg c1 hD]

/-- The stencil's self-pair term: `Σ c_j K_{Y_j}(0, h) = 7/(15h)`. -/
theorem threeProbe_self (h : ℝ) (hh : 0 < h) :
    (15 / 14) * K (3 * h) 0 h - (16 / 21) * K (4 * h) 0 h + (1 / 6) * K (5 * h) 0 h = 7 / (15 * h) := by
  unfold K
  have : h ≠ 0 := hh.ne'
  field_simp
  ring

/-- Self-pair term at a probe `p`: `K p 0 h = 2p/(p² − h²)`. -/
theorem K_self (p h : ℝ) (hp : h < p) (hh : 0 < h) : K p 0 h = 2 * p / (p ^ 2 - h ^ 2) := by
  unfold K
  have h1 : p - h ≠ 0 := by linarith
  have h2 : p + h ≠ 0 := by linarith
  have h3 : p ^ 2 - h ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

/-- Self-pair derivative term: `∂ₚ K p 0 h = −2(p² + h²)/(p² − h²)²`. -/
theorem dK_self (p h : ℝ) (hp : h < p) (hh : 0 < h) :
    dK p 0 h = -2 * (p ^ 2 + h ^ 2) / (p ^ 2 - h ^ 2) ^ 2 := by
  unfold dK
  have h1 : p - h ≠ 0 := by linarith
  have h2 : p + h ≠ 0 := by linarith
  have h3 : p ^ 2 - h ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

end DBN.Kernels

end
