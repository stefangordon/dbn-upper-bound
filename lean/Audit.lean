import DBN
import LeanCert.Tactic.Verification

/-!
Run `lake env lean Audit.lean` after `lake build`.

The typed examples pin the headline statements and the original premise constructor. The trust assertions
fail on proof holes, native/compiler proof dependencies, or axioms outside
Lean/Mathlib's `propext`, `Classical.choice`, and `Quot.sound` foundations.
The print commands make the exact premise interfaces and actual dependencies
available to a reviewer. This audit does not discharge those premises.
-/

example : DBN.RemainingPremises → DBN.Lambda ≤ (DBN.Const.bound : ℝ) :=
  DBN.lambda_le_bound_of_remaining

/-- Pin the mathematical bound itself, in addition to its symbolic name. -/
example (P : DBN.RemainingPremises) : DBN.Lambda ≤
    (3885632262767861213460393068710302759 / 24646172707879668706230182733520000000 : ℝ) := by
  simpa [DBN.Const.bound] using DBN.lambda_le_bound_of_remaining P

example : DBN.PolymathPositiveTimeRealTail → DBN.ProfileRemainingPremises →
    DBN.Lambda ≤ (DBN.Const.bound : ℝ) :=
  DBN.lambda_le_bound_of_polymath_and_profiles

example : DBN.ApproximationPremises → DBN.Lambda ≤ (DBN.Const.bound : ℝ) :=
  DBN.lambda_le_bound_of_approximation

/-- Keep the published four-input interface: a stronger replacement for `head`
must not silently change the meaning of the existing headline theorem. -/
example
    (confine : ∃ R : ℝ, ∀ t ∈ Set.Icc (DBN.τ0 : ℝ) (DBN.Const.Tstar : ℝ),
      ∀ z : ℂ, DBN.H t z = 0 → 1 / 40 ≤ |z.im| → |z.re| ≤ R)
    (head : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 5), ∀ z : ℂ,
      DBN.H t z = 0 → |z.re| ≤ DBN.Const.X → z.im = 0)
    (sourceFloor : ∀ r ∈ DBN.Data.mainRows, ∀ c : DBN.SourceCert,
      r.cert = .source c → ∀ x : ℝ, (DBN.Const.X : ℝ) ≤ x →
      ∀ t ∈ Set.Icc (c.btl : ℝ) c.btr, ∀ h ∈ Set.Icc (c.hlo : ℝ) c.hhi,
      (c.L : ℝ) ≤ DBN.V x h t)
    (fieldFloor : ∀ r ∈ DBN.Data.mainRows ++ DBN.Data.fullCRows, ∀ c : DBN.FieldCert,
      r.cert = .field c → ∀ x : ℝ, (DBN.Const.X : ℝ) ≤ x →
      ∀ t ∈ Set.Icc (c.otl : ℝ) c.otr,
      DBN.H t (x + (c.p : ℝ) * Complex.I) ≠ 0 ∧ (c.s : ℝ) < DBN.S x c.p t ∧
      (c.signed = true → DBN.J x c.p t ≤ c.c)) : DBN.RemainingPremises :=
  ⟨confine, head, sourceFloor, fieldFloor⟩

#assert_trust kernel DBN.lambda_le_bound_of_remaining
#assert_trust kernel DBN.lambda_le_bound_of_polymath_and_profiles
#assert_trust kernel DBN.lambda_le_bound_of_approximation
#assert_trust kernel DBN.confine_of_approximation
#assert_trust kernel DBN.Approx.gamma_crude
#assert_trust kernel DBN.Zeta.norm_zeta_ge
#assert_trust kernel DBN.Zeta.term_le
#assert_trust kernel DBN.Zeta.Phi_eq
#assert_trust kernel DBN.Zeta.norm_Phi_le
#assert_trust kernel DBN.Zeta.heat_identity
#assert_trust kernel DBN.Zeta.norm_Rheat_le
#assert_trust kernel DBN.Zeta.norm_TN_le
#assert_trust kernel DBN.zeroDynamics_proved
#assert_trust kernel DBN.head_of_finiteRH
#assert_trust kernel DBN.boundaryNonvanishing_of_approximation
#assert_trust kernel DBN.tailPremises
#assert_trust kernel DBN.confinement_of_polymathPositiveTimeRealTail
#assert_trust kernel DBN.Profile.fieldFloor_of_profiles
#assert_trust kernel DBN.Profile.profileCellGates_proved
#assert_trust kernel DBN.Profile.f0_mono
#assert_trust kernel DBN.Profile.hasDerivAt_U_height
#assert_trust kernel DBN.Profile.delta_TM_lt
#assert_trust kernel DBN.Profile.density_1251
#assert_trust kernel DBN.Profile.density_3356
#assert_trust kernel DBN.Profile.jet_3356
#assert_trust kernel DBN.Profile.jet_5845
#assert_trust kernel DBN.Profile.overderated_3356_false

#print DBN.RemainingPremises
#print DBN.PolymathPositiveTimeRealTail
#print DBN.ProfileRemainingPremises
#print DBN.ApproximationPremises
#print DBN.FiniteRH
#print DBN.BoundaryNonvanishing
#print DBN.EnlargedApproximation
#print DBN.BoundaryMainTermBound
#print DBN.Profile.DensityJetFields
#print DBN.Profile.ProfileCellGates
#print axioms DBN.lambda_le_bound_of_remaining
#print axioms DBN.lambda_le_bound_of_polymath_and_profiles
#print axioms DBN.lambda_le_bound_of_approximation
#print axioms DBN.confine_of_approximation
#print axioms DBN.Approx.gamma_crude
#print axioms DBN.Zeta.norm_zeta_ge
#print axioms DBN.Zeta.term_le
#print axioms DBN.Zeta.Phi_eq
#print axioms DBN.Zeta.norm_Phi_le
#print axioms DBN.Zeta.heat_identity
#print axioms DBN.Zeta.norm_Rheat_le
#print axioms DBN.Zeta.norm_TN_le
#print axioms DBN.zeroDynamics_proved
#print axioms DBN.head_of_finiteRH
#print axioms DBN.boundaryNonvanishing_of_approximation
#print axioms DBN.tailPremises
#print axioms DBN.confinement_of_polymathPositiveTimeRealTail
#print axioms DBN.Profile.fieldFloor_of_profiles
#print axioms DBN.Profile.f0_mono
#print axioms DBN.Profile.hasDerivAt_U_height
#print axioms DBN.Profile.delta_TM_lt
#print axioms DBN.Profile.density_1251
#print axioms DBN.Profile.density_3356
#print axioms DBN.Profile.jet_3356
#print axioms DBN.Profile.jet_5845
#print axioms DBN.Profile.overderated_3356_false
#print axioms DBN.Profile.profileCellGates_proved
