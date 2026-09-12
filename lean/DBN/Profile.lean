import DBN.Premises
import LeanCert.Tactic.IntervalAuto

/-!
# The explicit density and jet profiles

These are the concrete functions used in P4, P5 and P8. In particular P8 tests
`s + 1/100000 < f0 p tl`, where `f0 = UY / U`. The subtraction in `fM` is
applied only once, when transferring this numerical inequality to `S`.
-/

noncomputable section

namespace DBN.Profile

/-- Positive heat profile used in the M3a density field. -/
def U (Y t : ℝ) : ℝ := 1000000000 +
  1758974 * Real.exp ((19 / 4 : ℝ) ^ 2 * t) * Real.cosh (19 / 4 * Y) +
  2464729 * Real.exp ((97 / 20 : ℝ) ^ 2 * t) * Real.cosh (97 / 20 * Y) +
  302096 * Real.exp ((131 / 20 : ℝ) ^ 2 * t) * Real.cosh (131 / 20 * Y)

/-- Explicit derivative of `U` in the height variable. -/
def UY (Y t : ℝ) : ℝ :=
  1758974 * (19 / 4) * Real.exp ((19 / 4 : ℝ) ^ 2 * t) * Real.sinh (19 / 4 * Y) +
  2464729 * (97 / 20) * Real.exp ((97 / 20 : ℝ) ^ 2 * t) * Real.sinh (97 / 20 * Y) +
  302096 * (131 / 20) * Real.exp ((131 / 20 : ℝ) ^ 2 * t) * Real.sinh (131 / 20 * Y)

def f0 (Y t : ℝ) : ℝ := UY Y t / U Y t
def delta (t : ℝ) : ℝ := Real.exp (90 * t) / 100000000000000
def fM (Y t : ℝ) : ℝ := f0 Y t - delta t
def C (Y t : ℝ) : ℝ :=
  Real.exp (t / 100000) * (8 / 25 + 1130000000000 / U Y t)

/-- The endpoint upper bound actually checked for the jet profile. -/
def Cceil (Y tl tr : ℝ) : ℝ :=
  Real.exp (tr / 100000) * (8 / 25 + 1130000000000 / U Y tl)

theorem U_pos (Y t : ℝ) : 0 < U Y t := by
  unfold U
  positivity

/-- Positivity of each heat mode makes `U` increase in time, at every height. -/
theorem U_mono (Y : ℝ) : Monotone (U Y) := by
  intro t₁ t₂ ht
  unfold U
  gcongr

/-- Time derivative of the profile. -/
def Ut (Y t : ℝ) : ℝ :=
  (19 / 4 : ℝ) ^ 2 * (1758974 * Real.exp ((19 / 4 : ℝ) ^ 2 * t) * Real.cosh (19 / 4 * Y)) +
  (97 / 20 : ℝ) ^ 2 * (2464729 * Real.exp ((97 / 20 : ℝ) ^ 2 * t) * Real.cosh (97 / 20 * Y)) +
  (131 / 20 : ℝ) ^ 2 * (302096 * Real.exp ((131 / 20 : ℝ) ^ 2 * t) * Real.cosh (131 / 20 * Y))

def UYt (Y t : ℝ) : ℝ :=
  (19 / 4 : ℝ) ^ 2 * (1758974 * (19 / 4) * Real.exp ((19 / 4 : ℝ) ^ 2 * t) * Real.sinh (19 / 4 * Y)) +
  (97 / 20 : ℝ) ^ 2 * (2464729 * (97 / 20) * Real.exp ((97 / 20 : ℝ) ^ 2 * t) * Real.sinh (97 / 20 * Y)) +
  (131 / 20 : ℝ) ^ 2 * (302096 * (131 / 20) * Real.exp ((131 / 20 : ℝ) ^ 2 * t) * Real.sinh (131 / 20 * Y))

private theorem mode_hasDerivAt (a lam b t : ℝ) :
    HasDerivAt (fun t => a * Real.exp (lam ^ 2 * t) * b)
      (lam ^ 2 * (a * Real.exp (lam ^ 2 * t) * b)) t := by
  convert! ((((hasDerivAt_id t).const_mul (lam ^ 2)).exp).const_mul a).mul_const b using 1
  dsimp only [id_eq]
  ring

theorem hasDerivAt_U (Y t : ℝ) : HasDerivAt (U Y) (Ut Y t) t := by
  convert!
    (((hasDerivAt_const t (1000000000 : ℝ)).add
      (mode_hasDerivAt 1758974 (19 / 4) (Real.cosh (19 / 4 * Y)) t)).add
      (mode_hasDerivAt 2464729 (97 / 20) (Real.cosh (97 / 20 * Y)) t)).add
      (mode_hasDerivAt 302096 (131 / 20) (Real.cosh (131 / 20 * Y)) t) using 1
  simp [Ut]

theorem hasDerivAt_UY (Y t : ℝ) : HasDerivAt (UY Y) (UYt Y t) t := by
  convert!
    ((mode_hasDerivAt (1758974 * (19 / 4)) (19 / 4) (Real.sinh (19 / 4 * Y)) t).add
      (mode_hasDerivAt (2464729 * (97 / 20)) (97 / 20) (Real.sinh (97 / 20 * Y)) t)).add
      (mode_hasDerivAt (302096 * (131 / 20)) (131 / 20) (Real.sinh (131 / 20 * Y)) t) using 1

private theorem mode_height_hasDerivAt (a lam t Y : ℝ) :
    HasDerivAt (fun Y => a * Real.exp (lam ^ 2 * t) * Real.cosh (lam * Y))
      (a * lam * Real.exp (lam ^ 2 * t) * Real.sinh (lam * Y)) Y := by
  convert! (((hasDerivAt_id Y).const_mul lam).cosh).const_mul
    (a * Real.exp (lam ^ 2 * t)) using 1
  dsimp only [id_eq]
  ring

/-- The explicit `UY` is the actual derivative of `U` in the height variable. -/
theorem hasDerivAt_U_height (Y t : ℝ) : HasDerivAt (fun y => U y t) (UY Y t) Y := by
  convert!
    (((hasDerivAt_const Y (1000000000 : ℝ)).add
      (mode_height_hasDerivAt 1758974 (19 / 4) t Y)).add
      (mode_height_hasDerivAt 2464729 (97 / 20) t Y)).add
      (mode_height_hasDerivAt 302096 (131 / 20) t Y) using 1
  simp [UY]

private theorem sinh_cross_nonneg {a b Y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hY : 0 ≤ Y) :
    0 ≤ b * Real.sinh (b * Y) * Real.cosh (a * Y) -
      a * Real.sinh (a * Y) * Real.cosh (b * Y) := by
  have hb : 0 ≤ b := le_trans ha hab
  have h₁ : 0 ≤ Real.sinh ((b - a) * Y) :=
    Real.sinh_nonneg_iff.mpr (mul_nonneg (sub_nonneg.mpr hab) hY)
  have h₂ : 0 ≤ Real.sinh (b * Y) := Real.sinh_nonneg_iff.mpr (mul_nonneg hb hY)
  calc
    _ = a * Real.sinh ((b - a) * Y) +
        (b - a) * Real.sinh (b * Y) * Real.cosh (a * Y) := by
      rw [sub_mul, Real.sinh_sub]
      ring
    _ ≥ 0 := add_nonneg (mul_nonneg ha h₁)
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) h₂) (Real.cosh_pos _).le)

private theorem covariance_nonneg
    {d a b c v₁ v₂ v₃ n₁ n₂ n₃ r₁ r₂ r₃ : ℝ}
    (hd : 0 ≤ d) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂) (hn₃ : 0 ≤ n₃)
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hr₃ : 0 ≤ r₃)
    (hr₁₂ : 0 ≤ r₂ - r₁) (hr₁₃ : 0 ≤ r₃ - r₁) (hr₂₃ : 0 ≤ r₃ - r₂)
    (h₁₂ : 0 ≤ n₂ * v₁ - n₁ * v₂)
    (h₁₃ : 0 ≤ n₃ * v₁ - n₁ * v₃)
    (h₂₃ : 0 ≤ n₃ * v₂ - n₂ * v₃) :
    0 ≤ (r₁ * a * n₁ + r₂ * b * n₂ + r₃ * c * n₃) * (d + a * v₁ + b * v₂ + c * v₃) -
      (a * n₁ + b * n₂ + c * n₃) * (r₁ * a * v₁ + r₂ * b * v₂ + r₃ * c * v₃) := by
  calc
    _ = d * (r₁ * a * n₁ + r₂ * b * n₂ + r₃ * c * n₃) +
        a * b * (r₂ - r₁) * (n₂ * v₁ - n₁ * v₂) +
        a * c * (r₃ - r₁) * (n₃ * v₁ - n₁ * v₃) +
        b * c * (r₃ - r₂) * (n₃ * v₂ - n₂ * v₃) := by ring
    _ ≥ 0 := by positivity

/-- The covariance identity has the needed sign for every nonnegative height. -/
theorem density_time_numerator_nonneg {Y : ℝ} (hY : 0 ≤ Y) (t : ℝ) :
    0 ≤ UYt Y t * U Y t - UY Y t * Ut Y t := by
  have hs₁ : 0 ≤ (19 / 4 : ℝ) * Real.sinh (19 / 4 * Y) := by positivity
  have hs₂ : 0 ≤ (97 / 20 : ℝ) * Real.sinh (97 / 20 * Y) := by positivity
  have hs₃ : 0 ≤ (131 / 20 : ℝ) * Real.sinh (131 / 20 * Y) := by positivity
  have h₁₂ := sinh_cross_nonneg (a := (19 / 4 : ℝ)) (b := 97 / 20) (by norm_num) (by norm_num) hY
  have h₁₃ := sinh_cross_nonneg (a := (19 / 4 : ℝ)) (b := 131 / 20) (by norm_num) (by norm_num) hY
  have h₂₃ := sinh_cross_nonneg (a := (97 / 20 : ℝ)) (b := 131 / 20) (by norm_num) (by norm_num) hY
  have h := covariance_nonneg
    (d := 1000000000)
    (a := 1758974 * Real.exp ((19 / 4 : ℝ) ^ 2 * t))
    (b := 2464729 * Real.exp ((97 / 20 : ℝ) ^ 2 * t))
    (c := 302096 * Real.exp ((131 / 20 : ℝ) ^ 2 * t))
    (r₁ := (19 / 4 : ℝ) ^ 2) (r₂ := (97 / 20 : ℝ) ^ 2) (r₃ := (131 / 20 : ℝ) ^ 2)
    (by norm_num) (by positivity) (by positivity) (by positivity)
    hs₁ hs₂ hs₃ (by positivity) (by positivity) (by positivity)
    (by norm_num) (by norm_num) (by norm_num) h₁₂ h₁₃ h₂₃
  convert h using 1
  dsimp [U, UY, Ut, UYt]
  ring

/-- It is the unmodified profile `f0 = UY/U` that is used monotonically in P8.
No monotonicity of `fM = f0 - delta` is asserted or needed. -/
theorem f0_mono {Y : ℝ} (hY : 0 ≤ Y) : Monotone (f0 Y) := by
  apply monotone_of_hasDerivAt_nonneg (f' := fun t => (UYt Y t * U Y t - UY Y t * Ut Y t) / (U Y t) ^ 2)
  · intro t
    exact (hasDerivAt_UY Y t).div (hasDerivAt_U Y t) (U_pos Y t).ne'
  · intro t
    exact div_nonneg (density_time_numerator_nonneg hY t) (sq_nonneg _)

/-- The uniform subtraction budget, at the exact horizon. A coarse integer
argument avoids expensive interval reduction of the long rational horizon. -/
theorem delta_TM_lt : delta (Const.TM : ℝ) < 1 / 100000 := by
  have htime : 90 * (Const.TM : ℝ) ≤ 15 := by norm_num [Const.TM]
  have hexp : Real.exp (15 : ℝ) < 1000000000 := by
    have h₁ : Real.exp (1 : ℝ) < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h₂ : Real.exp (1 : ℝ) ^ 15 < 3 ^ 15 := pow_lt_pow_left₀ h₁ (Real.exp_pos _).le (by norm_num)
    rw [← Real.exp_nat_mul] at h₂
    norm_num at h₂ ⊢
    linarith
  unfold delta
  have := lt_of_le_of_lt (Real.exp_le_exp.mpr htime) hexp
  linarith

theorem delta_lt_of_le {t : ℝ} (ht : t ≤ (Const.TM : ℝ)) : delta t < 1 / 100000 := by
  apply lt_of_le_of_lt ?_ delta_TM_lt
  unfold delta
  gcongr

/-- The pointwise jet profile is bounded by the mixed-endpoint expression on the whole cell. -/
theorem C_le_Cceil {Y tl t tr : ℝ} (htl : tl ≤ t) (htr : t ≤ tr) :
    C Y t ≤ Cceil Y tl tr := by
  have hUpos := U_pos Y t
  have hU : 1130000000000 / U Y t ≤ 1130000000000 / U Y tl :=
    div_le_div_of_nonneg_left (by norm_num) (U_pos Y tl) (U_mono Y htl)
  unfold C Cceil
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    linarith
  · linarith
  · positivity
  · positivity

/-- The exact P8 density gate transfers to `S > s` using P4 and only one subtraction budget. -/
theorem density_gt_of_endpoint {x p tl t s : ℝ} (hp : 0 ≤ p) (htl : tl ≤ t)
    (ht : t ≤ (Const.TM : ℝ)) (hnum : s + 1 / 100000 < f0 p tl)
    (hfield : fM p t ≤ S x p t) : s < S x p t := by
  have hmono := f0_mono hp htl
  have hdelta := delta_lt_of_le ht
  unfold fM at hfield
  linarith

/-- The exact P8 jet gate transfers to `J ≤ c` using P5 on the whole closed cell. -/
theorem jet_le_of_endpoint {x p tl t tr c : ℝ} (htl : tl ≤ t) (htr : t ≤ tr)
    (hnum : Cceil p tl tr ≤ c) (hfield : J x p t ≤ C p t) : J x p t ≤ c :=
  hfield.trans ((C_le_Cceil htl htr).trans hnum)

end DBN.Profile

end
