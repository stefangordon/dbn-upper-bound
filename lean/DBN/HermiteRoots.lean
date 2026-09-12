import Mathlib
import DBN.Hermite

/-!
# The forward Hermite model polynomial and its real roots

`Pf m w = Σ_{2j+k=m} (-1)^j w^k/(j! k!)` is the limit polynomial of the forward scaled expansion
`ε^{-m/2} H_{t+ε}(ρ + √ε w)`; it is `(2^{m/2}/m!) He_m(w/√2)` for the probabilists' Hermite
polynomial. This file proves directly that it has `m` distinct real roots: `Pf_{m+1}' = Pf_m`, the
three-term recurrence `(m+2) Pf_{m+2} = w Pf_{m+1} − 2 Pf_m` (from equal derivatives and equal values
at `0`), hence `F_m = Pf_m e^{−w²/4}` satisfies `F_m' = −((m+1)/2) F_{m+1}`, and Rolle's theorem
between consecutive roots and on both tails produces `m+1` distinct roots of `Pf_{m+1}` from `m`
distinct roots of `Pf_m`.
-/

noncomputable section

namespace DBN.HermiteRoots

open Set Finset Filter Topology
open DBN.Hermite (E mem_E)

/-- The forward model polynomial `Σ_{2j+k=m} (-1)^j w^k/(j! k!)`. -/
def Pf (m : ℕ) (w : ℝ) : ℝ :=
  ∑ p ∈ E m, (-1 : ℝ) ^ p.1 * w ^ p.2 / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ))

theorem E_zero : E 0 = {(0, 0)} := by
  ext p; simp only [mem_E, Finset.mem_singleton, Prod.ext_iff]; omega

theorem E_one : E 1 = {(0, 1)} := by
  ext p; simp only [mem_E, Finset.mem_singleton, Prod.ext_iff]; omega

theorem Pf_zero (w : ℝ) : Pf 0 w = 1 := by
  unfold Pf; rw [E_zero]; simp

theorem Pf_one (w : ℝ) : Pf 1 w = w := by
  unfold Pf; rw [E_one]; simp

/-- `Pf_{m+1}' = Pf_m`: the Appell property. -/
theorem hasDerivAt_Pf (m : ℕ) (w : ℝ) : HasDerivAt (Pf (m + 1)) (Pf m w) w := by
  unfold Pf
  have h := HasDerivAt.sum (u := E (m + 1))
    (A := fun p (w : ℝ) => (-1 : ℝ) ^ p.1 * w ^ p.2 / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ)))
    (A' := fun p => (-1 : ℝ) ^ p.1 * ((p.2 : ℝ) * w ^ (p.2 - 1)) /
      ((p.1.factorial : ℝ) * (p.2.factorial : ℝ)))
    (fun p _ => ((hasDerivAt_pow p.2 w).const_mul ((-1 : ℝ) ^ p.1)).div_const _)
  have e : (∑ p ∈ E (m + 1), fun (w : ℝ) =>
      (-1 : ℝ) ^ p.1 * w ^ p.2 / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ))) =
      fun w => ∑ p ∈ E (m + 1), (-1 : ℝ) ^ p.1 * w ^ p.2 / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ)) := by
    funext w; simp [Finset.sum_apply]
  rw [e] at h
  refine h.congr_deriv ?_
  rw [← Finset.sum_filter_add_sum_filter_not (E (m + 1)) (fun p => p.2 = 0)]
  have h0 : ∑ p ∈ (E (m + 1)).filter (fun p => p.2 = 0),
      (-1 : ℝ) ^ p.1 * ((p.2 : ℝ) * w ^ (p.2 - 1)) / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [hp.2]; simp
  rw [h0, zero_add]
  symm
  refine Finset.sum_nbij (fun q => (q.1, q.2 + 1)) ?_ ?_ ?_ ?_
  · intro q hq
    rw [mem_E] at hq
    simp only [Finset.mem_filter, mem_E]
    omega
  · intro q _ q' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (by omega)
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, mem_E] at hp
    refine ⟨(p.1, p.2 - 1), ?_, ?_⟩
    · simp only [Finset.mem_coe, mem_E]; omega
    · ext
      · rfl
      · simp only; omega
  · intro q hq
    rw [mem_E] at hq
    simp only [Nat.factorial_succ, Nat.add_sub_cancel]
    push_cast
    have h1 : ((q.1.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have h2 : ((q.2.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    have h3 : ((q.2 : ℝ) + 1) ≠ 0 := by positivity
    field_simp <;> ring

theorem differentiable_Pf (m : ℕ) : Differentiable ℝ (Pf m) := by
  cases m with
  | zero => intro w; rw [show Pf 0 = fun _ => (1 : ℝ) from funext Pf_zero]; exact differentiableAt_const _
  | succ m => intro w; exact (hasDerivAt_Pf m w).differentiableAt

theorem deriv_Pf (m : ℕ) : deriv (Pf (m + 1)) = Pf m := funext fun w => (hasDerivAt_Pf m w).deriv

theorem deriv_Pf_zero : deriv (Pf 0) = fun _ => 0 := by
  rw [show Pf 0 = fun _ => (1 : ℝ) from funext Pf_zero]; simp

/-- The value at `0`. -/
theorem Pf_at_zero (m : ℕ) :
    Pf m 0 = if Even m then (-1 : ℝ) ^ (m / 2) / ((m / 2).factorial : ℝ) else 0 := by
  unfold Pf
  split_ifs with hm
  · rw [Finset.sum_eq_single (m / 2, 0)]
    · simp
    · intro p hp hne
      rw [mem_E] at hp
      have : p.2 ≠ 0 := by
        intro h
        apply hne
        obtain ⟨r, hr⟩ := hm
        ext
        · simp only; omega
        · exact h
      simp [this]
    · intro h
      exfalso; apply h
      rw [mem_E]
      obtain ⟨r, hr⟩ := hm
      omega
  · apply Finset.sum_eq_zero
    intro p hp
    rw [mem_E] at hp
    have : p.2 ≠ 0 := by
      intro h
      apply hm
      exact ⟨p.1, by omega⟩
    simp [this]

/-- The three-term recurrence `(m+2) Pf_{m+2} = w Pf_{m+1} − 2 Pf_m`. -/
theorem Pf_rec (m : ℕ) (w : ℝ) :
    ((m + 2 : ℕ) : ℝ) * Pf (m + 2) w = w * Pf (m + 1) w - 2 * Pf m w := by
  induction m generalizing w with
  | zero =>
    -- direct computation: `Pf 2 w = w²/2 − 1`
    have hE : E 2 = {(0, 2), (1, 0)} := by
      ext p; simp only [mem_E, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]; omega
    unfold Pf
    rw [hE, E_one, E_zero]
    simp [Nat.factorial]
    ring
  | succ m ih =>
    -- the difference has zero derivative and vanishes at `0`
    set D : ℝ → ℝ := fun w => ((m + 1 + 2 : ℕ) : ℝ) * Pf (m + 1 + 2) w - (w * Pf (m + 1 + 1) w - 2 * Pf (m + 1) w) with hD
    have hderiv : ∀ x, HasDerivAt D 0 x := by
      intro x
      have h1 := (hasDerivAt_Pf (m + 2) x).const_mul ((m + 1 + 2 : ℕ) : ℝ)
      have h2 := (hasDerivAt_id x).mul (hasDerivAt_Pf (m + 1) x)
      have h3 := (hasDerivAt_Pf m x).const_mul (2 : ℝ)
      have h := h1.sub (h2.sub h3)
      refine h.congr_deriv ?_
      have := ih x
      simp only [id]
      push_cast at this ⊢
      linear_combination this
    have hconst : ∀ x, D x = D 0 := fun x =>
      is_const_of_deriv_eq_zero (fun x => (hderiv x).differentiableAt) (fun x => (hderiv x).deriv) x 0
    have hD0 : D 0 = 0 := by
      simp only [hD, zero_mul, zero_sub, Pf_at_zero]
      rcases Nat.even_or_odd (m + 1) with he | ho
      · obtain ⟨r, hr⟩ := he
        have h1 : Even (m + 1 + 2) := ⟨r + 1, by omega⟩
        rw [if_pos h1, if_pos ⟨r, hr⟩]
        have e1 : (m + 1 + 2) / 2 = r + 1 := by omega
        have e2 : (m + 1) / 2 = r := by omega
        have e3 : m + 1 + 2 = 2 * (r + 1) := by omega
        rw [e1, e2, e3, Nat.factorial_succ, pow_succ]
        have hf : ((r.factorial : ℕ) : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp
        ring
      · have h1 : ¬ Even (m + 1 + 2) := by
          intro h; obtain ⟨r, hr⟩ := h; obtain ⟨s, hs⟩ := ho; omega
        have h2 : ¬ Even (m + 1) := Nat.not_even_iff_odd.mpr ho
        rw [if_neg h1, if_neg h2]; ring
    have := hconst w
    rw [hD0] at this
    simp only [hD] at this
    linarith

/-! ### The Gaussian-weighted functions -/

def G (w : ℝ) : ℝ := Real.exp (-(w ^ 2 / 4))

theorem G_pos (w : ℝ) : 0 < G w := Real.exp_pos _

theorem hasDerivAt_G (w : ℝ) : HasDerivAt G (-(w / 2) * G w) w := by
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2 / 4)) (-(2 * w ^ (2 - 1) / 4)) w :=
    ((hasDerivAt_pow 2 w).div_const 4).neg
  have h := h1.exp
  unfold G
  refine h.congr_deriv ?_
  norm_num
  ring

/-- `F m = Pf m · e^{−w²/4}`. -/
def F (m : ℕ) (w : ℝ) : ℝ := Pf m w * G w

theorem F_eq_zero_iff (m : ℕ) (w : ℝ) : F m w = 0 ↔ Pf m w = 0 := by
  unfold F; constructor
  · intro h; rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h (G_pos w).ne'
  · intro h; rw [h, zero_mul]

theorem hasDerivAt_F_zero (w : ℝ) : HasDerivAt (F 0) (-(1 / 2) * F 1 w) w := by
  have e : F 0 = G := funext fun w => by unfold F; rw [Pf_zero, one_mul]
  rw [e]
  refine (hasDerivAt_G w).congr_deriv ?_
  unfold F; rw [Pf_one]; ring

theorem hasDerivAt_F_succ (m : ℕ) (w : ℝ) :
    HasDerivAt (F (m + 1)) (-(((m + 2 : ℕ) : ℝ) / 2) * F (m + 2) w) w := by
  have h := (hasDerivAt_Pf m w).mul (hasDerivAt_G w)
  refine h.congr_deriv ?_
  unfold F
  have := Pf_rec m w
  push_cast at this ⊢
  linear_combination (G w / 2) * this

/-- The derivative of `F m` vanishes exactly where `F (m+1)` does. -/
theorem hasDerivAt_F (m : ℕ) (w : ℝ) :
    HasDerivAt (F m) (-(((m + 1 : ℕ) : ℝ) / 2) * F (m + 1) w) w := by
  cases m with
  | zero => simpa using hasDerivAt_F_zero w
  | succ m => exact hasDerivAt_F_succ m w

/-! ### Degree bound and decay -/

/-- `Pf m` as a polynomial. -/
def PfPoly (m : ℕ) : Polynomial ℝ :=
  ∑ p ∈ E m, Polynomial.C ((-1 : ℝ) ^ p.1 / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ))) *
    Polynomial.X ^ p.2

theorem PfPoly_eval (m : ℕ) (w : ℝ) : (PfPoly m).eval w = Pf m w := by
  unfold PfPoly Pf
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem PfPoly_natDegree_le (m : ℕ) : (PfPoly m).natDegree ≤ m := by
  unfold PfPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro p hp
  rw [mem_E] at hp
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem PfPoly_coeff_top (m : ℕ) : (PfPoly m).coeff m = 1 / (m.factorial : ℝ) := by
  unfold PfPoly
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (0, m)]
  · simp [Polynomial.coeff_C_mul_X_pow]
  · intro p hp hne
    rw [mem_E] at hp
    rw [Polynomial.coeff_C_mul_X_pow, if_neg]
    intro h
    apply hne
    ext
    · simp only; omega
    · simp only; omega
  · intro h; exfalso; apply h; rw [mem_E]; simp

theorem PfPoly_ne_zero (m : ℕ) : PfPoly m ≠ 0 := by
  intro h
  have := PfPoly_coeff_top m
  rw [h, Polynomial.coeff_zero] at this
  have h2 : (1 : ℝ) / (m.factorial : ℝ) ≠ 0 := one_div_ne_zero (by positivity)
  exact h2 this.symm

/-- `Pf m` has at most `m` distinct real roots. -/
theorem card_roots_le (m : ℕ) (s : Finset ℝ) (hs : ∀ x ∈ s, Pf m x = 0) : s.card ≤ m := by
  have hsub : s ⊆ (PfPoly m).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (PfPoly_ne_zero m), Polynomial.IsRoot,
      PfPoly_eval]
    exact hs x hx
  calc s.card ≤ (PfPoly m).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (PfPoly m).roots := Multiset.toFinset_card_le _
    _ ≤ (PfPoly m).natDegree := Polynomial.card_roots' _
    _ ≤ m := PfPoly_natDegree_le m

/-- `w^k e^{−w²/4} → 0` at `+∞`: squeeze against `w^k e^{−w}` for `w ≥ 4`. -/
theorem tendsto_pow_mul_G_atTop (k : ℕ) : Tendsto (fun w : ℝ => w ^ k * G w) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with w hw
    unfold G; positivity
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with w hw
    unfold G
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith

theorem tendsto_F_atTop (m : ℕ) : Tendsto (F m) atTop (𝓝 0) := by
  have e : F m = fun w => ∑ p ∈ E m, ((-1 : ℝ) ^ p.1 / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ))) *
      (w ^ p.2 * G w) := by
    funext w; unfold F Pf; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun p _ => by ring
  rw [e]
  have := tendsto_finset_sum (E m) fun p _ => (tendsto_pow_mul_G_atTop p.2).const_mul
    ((-1 : ℝ) ^ p.1 / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ)))
  simpa using this

theorem tendsto_F_atBot (m : ℕ) : Tendsto (F m) atBot (𝓝 0) := by
  have e : F m = fun w => ∑ p ∈ E m, ((-1 : ℝ) ^ p.1 / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ))) *
      (w ^ p.2 * G w) := by
    funext w; unfold F Pf; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun p _ => by ring
  rw [e]
  have hneg : ∀ k : ℕ, Tendsto (fun w : ℝ => w ^ k * G w) atBot (𝓝 0) := by
    intro k
    have h := (tendsto_pow_mul_G_atTop k).comp tendsto_neg_atBot_atTop
    have e2 : (fun w : ℝ => w ^ k * G w) = fun w => (-1) ^ k * ((fun w : ℝ => w ^ k * G w) (-w)) := by
      funext w
      simp only [G, neg_sq]
      rw [neg_pow]
      have h4 : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      linear_combination (-(w ^ k * Real.exp (-(w ^ 2 / 4)))) * h4
    rw [e2]
    exact (h.const_mul ((-1 : ℝ) ^ k)).trans (by simp)
  have := tendsto_finset_sum (E m) fun p _ => (hneg p.2).const_mul
    ((-1 : ℝ) ^ p.1 / ((p.1.factorial : ℝ) * (p.2.factorial : ℝ)))
  simpa using this




/-! ### Rolle on the tails -/

/-- If a differentiable function vanishes at `a`, tends to `0` at `+∞` and is nonzero somewhere
right of `a`, its derivative vanishes somewhere right of `a`. -/
theorem exists_deriv_zero_Ioi {f f' : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (f' x) x) {a : ℝ} (ha : f a = 0)
    (hlim : Tendsto f atTop (𝓝 0)) {w : ℝ} (haw : a < w) (hfw : f w ≠ 0) :
    ∃ c, a < c ∧ f' c = 0 := by
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hpos : 0 < |f w| / 2 := by have := abs_pos.mpr hfw; linarith
  have hev : ∀ᶠ x in atTop, |f x| < |f w| / 2 := by
    have := Metric.tendsto_nhds.mp hlim (|f w| / 2) hpos
    simpa [Real.dist_eq] using this
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  set b := max N (w + 1) with hb
  have hwb : w < b := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hab : a < b := haw.trans hwb
  have hfb : |f b| < |f w| / 2 := hN b (le_max_left _ _)
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab.le)
    (continuous_abs.comp hcont).continuousOn (f := fun x => |f x|)
  have hcw : |f w| ≤ |f c| := hmax ⟨haw.le, hwb.le⟩
  have hfc : f c ≠ 0 := by
    intro h; rw [h, abs_zero] at hcw; exact absurd hcw (not_le.mpr (abs_pos.mpr hfw))
  have hca : c ≠ a := by intro h; rw [h, ha] at hfc; exact hfc rfl
  have hcb : c ≠ b := by intro h; rw [h] at hcw; linarith [abs_nonneg (f w)]
  have hc' : c ∈ Ioo a b := ⟨lt_of_le_of_ne hc.1 (Ne.symm hca), lt_of_le_of_ne hc.2 hcb⟩
  have hloc : IsLocalMax (fun x => |f x|) c := hmax.isLocalMax (Icc_mem_nhds hc'.1 hc'.2)
  refine ⟨c, hc'.1, ?_⟩
  rcases lt_or_gt_of_ne hfc with hneg | hpos'
  · have hmin : IsLocalMin f c := by
      filter_upwards [hloc] with x hx
      rw [abs_of_neg hneg] at hx
      linarith [neg_abs_le (f x)]
    exact hmin.hasDerivAt_eq_zero (hd c)
  · have hmax' : IsLocalMax f c := by
      filter_upwards [hloc] with x hx
      rw [abs_of_pos hpos'] at hx
      linarith [le_abs_self (f x)]
    exact hmax'.hasDerivAt_eq_zero (hd c)

theorem exists_deriv_zero_Iio {f f' : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (f' x) x) {a : ℝ} (ha : f a = 0)
    (hlim : Tendsto f atBot (𝓝 0)) {w : ℝ} (hwa : w < a) (hfw : f w ≠ 0) :
    ∃ c, c < a ∧ f' c = 0 := by
  have hd' : ∀ x, HasDerivAt (fun x => f (-x)) (-f' (-x)) x := by
    intro x
    have := (hd (-x)).comp x (hasDerivAt_neg x)
    simpa [Function.comp_def] using this
  have hlim' : Tendsto (fun x => f (-x)) atTop (𝓝 0) := hlim.comp tendsto_neg_atTop_atBot
  obtain ⟨c, hc, hc'⟩ := exists_deriv_zero_Ioi hd' (a := -a) (by simpa using ha) hlim'
    (w := -w) (by linarith) (by simpa using hfw)
  exact ⟨-c, by linarith, by simpa using hc'⟩

/-! ### Rolle between consecutive roots (max-erase induction) -/

/-- From `k+1` distinct zeros of `f`, `k` distinct zeros of `f'` strictly between them. -/
theorem rolle_between {f f' : ℝ → ℝ} (hd : ∀ x, HasDerivAt f (f' x) x) :
    ∀ (k : ℕ) (s : Finset ℝ), s.card = k + 1 → (∀ x ∈ s, f x = 0) →
      ∃ T : Finset ℝ, T.card = k ∧ (∀ c ∈ T, f' c = 0) ∧
        ∀ c ∈ T, (∃ x ∈ s, x < c) ∧ ∃ y ∈ s, c < y := by
  intro k
  induction k with
  | zero => intro s _ _; exact ⟨∅, rfl, by simp, by simp⟩
  | succ k ih =>
    intro s hcard hs
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    set M := s.max' hne with hM
    have hMmem : M ∈ s := Finset.max'_mem s hne
    set s' := s.erase M with hs'
    have hcard' : s'.card = k + 1 := by rw [hs', Finset.card_erase_of_mem hMmem, hcard]; rfl
    have hs'sub : s' ⊆ s := Finset.erase_subset _ _
    obtain ⟨T', hT'card, hT'zero, hT'between⟩ := ih s' hcard' fun x hx => hs x (hs'sub hx)
    have hne' : s'.Nonempty := Finset.card_pos.mp (by omega)
    set M' := s'.max' hne' with hM'
    have hM'mem : M' ∈ s' := Finset.max'_mem s' hne'
    have hM'lt : M' < M := Finset.lt_max'_of_mem_erase_max' s hne hM'mem
    have hcont : Continuous f := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
    obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_zero hM'lt hcont.continuousOn
      (by rw [hs M' (hs'sub hM'mem), hs M hMmem]) (fun x _ => hd x)
    have hcT' : c ∉ T' := by
      intro hcT
      obtain ⟨_, y, hy, hcy⟩ := hT'between c hcT
      have := Finset.le_max' s' y hy
      linarith [hc.1]
    refine ⟨insert c T', ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hcT', hT'card]
    · intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · rw [h]; exact hc'
      · exact hT'zero x h
    · intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · rw [h]; exact ⟨⟨M', hs'sub hM'mem, hc.1⟩, ⟨M, hMmem, hc.2⟩⟩
      · obtain ⟨⟨a, ha, hax⟩, ⟨b, hb, hxb⟩⟩ := hT'between x h
        exact ⟨⟨a, hs'sub ha, hax⟩, ⟨b, hs'sub hb, hxb⟩⟩

/-- All roots of `Pf m` lie in any set of `m` distinct roots. -/
theorem root_mem_of_card {m : ℕ} {s : Finset ℝ} (hcard : s.card = m) (hs : ∀ x ∈ s, Pf m x = 0)
    {x : ℝ} (hx : Pf m x = 0) : x ∈ s := by
  by_contra hxs
  have := card_roots_le m (insert x s) (by
    intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · rw [h]; exact hx
    · exact hs y h)
  rw [Finset.card_insert_of_notMem hxs, hcard] at this
  omega

/-- **`Pf m` has exactly `m` distinct real roots.** -/
theorem exists_roots : ∀ m : ℕ, ∃ s : Finset ℝ, s.card = m ∧ ∀ x ∈ s, Pf m x = 0
  | 0 => ⟨∅, rfl, by simp⟩
  | 1 => ⟨{0}, rfl, by simp [Pf_one]⟩
  | m + 2 => by
    obtain ⟨s, hcard, hs⟩ := exists_roots (m + 1)
    have hF : ∀ x ∈ s, F (m + 1) x = 0 := fun x hx => (F_eq_zero_iff _ _).mpr (hs x hx)
    have hd := hasDerivAt_F (m + 1)
    -- the derivative of `F (m+1)` vanishes exactly at the roots of `Pf (m+2)`
    have hzero : ∀ c, -(((m + 1 + 1 : ℕ) : ℝ) / 2) * F (m + 1 + 1) c = 0 → Pf (m + 2) c = 0 := by
      intro c hc
      have h2 : (-(((m + 1 + 1 : ℕ) : ℝ) / 2)) ≠ 0 := by apply neg_ne_zero.mpr; positivity
      have := (mul_eq_zero.mp hc).resolve_left h2
      exact (F_eq_zero_iff _ _).mp this
    obtain ⟨T, hTcard, hTzero, hTbetween⟩ := rolle_between hd m s hcard hF
    -- tails
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    set a := s.min' hne with ha
    set b := s.max' hne with hb
    have hamem : a ∈ s := Finset.min'_mem s hne
    have hbmem : b ∈ s := Finset.max'_mem s hne
    have hnz : ∀ w, w ∉ s → Pf (m + 1) w ≠ 0 := fun w hw h => hw (root_mem_of_card hcard hs h)
    have hbw : b + 1 ∉ s := fun h => by have := Finset.le_max' s _ h; linarith
    have haw : a - 1 ∉ s := fun h => by have := Finset.min'_le s _ h; linarith
    obtain ⟨cR, hcR, hcR'⟩ := exists_deriv_zero_Ioi hd (hF b hbmem) (tendsto_F_atTop (m + 1))
      (w := b + 1) (by linarith) (fun h => hnz _ hbw ((F_eq_zero_iff _ _).mp h))
    obtain ⟨cL, hcL, hcL'⟩ := exists_deriv_zero_Iio hd (hF a hamem) (tendsto_F_atBot (m + 1))
      (w := a - 1) (by linarith) (fun h => hnz _ haw ((F_eq_zero_iff _ _).mp h))
    -- every element of `T` lies strictly between `a` and `b`
    have hTa : ∀ c ∈ T, a < c := fun c hc => by
      obtain ⟨⟨x, hx, hxc⟩, _⟩ := hTbetween c hc
      exact lt_of_le_of_lt (Finset.min'_le s x hx) hxc
    have hTb : ∀ c ∈ T, c < b := fun c hc => by
      obtain ⟨_, ⟨y, hy, hcy⟩⟩ := hTbetween c hc
      exact lt_of_lt_of_le hcy (Finset.le_max' s y hy)
    have hRT : cR ∉ T := fun h => by have := hTb cR h; linarith
    have hLT : cL ∉ insert cR T := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · have := Finset.min'_le s b hbmem; linarith
      · have := hTa cL h; linarith
    refine ⟨insert cL (insert cR T), ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hLT, Finset.card_insert_of_notMem hRT, hTcard]
    · intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · rw [h]; exact hzero _ hcL'
      · rcases Finset.mem_insert.mp h with h | h
        · rw [h]; exact hzero _ hcR'
        · exact hzero _ (hTzero x h)

end DBN.HermiteRoots
