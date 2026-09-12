import DBN
import LeanCert.Tactic.Verification

/-!
Run `lake env lean Audit.lean` after `lake build`.

The typed examples pin the two headline statements. The trust assertions
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

#assert_trust kernel DBN.lambda_le_bound_of_remaining
#assert_trust kernel DBN.lambda_le_bound_of_polymath_and_profiles
#assert_trust kernel DBN.zeroDynamics_proved
#assert_trust kernel DBN.tailPremises
#assert_trust kernel DBN.confinement_of_polymathPositiveTimeRealTail
#assert_trust kernel DBN.Profile.fieldFloor_of_profiles
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
#print DBN.Profile.DensityJetFields
#print DBN.Profile.ProfileCellGates
#print axioms DBN.lambda_le_bound_of_remaining
#print axioms DBN.lambda_le_bound_of_polymath_and_profiles
#print axioms DBN.zeroDynamics_proved
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
