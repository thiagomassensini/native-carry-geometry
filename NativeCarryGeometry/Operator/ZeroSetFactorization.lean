import NativeCarryGeometry.Measure.CarryProbability
import NativeCarryGeometry.Operator.QuadraticDomain
import NativeCarryGeometry.Operator.BoundaryOperator

/-!
# Native zeros and radial-presentation factorization

The native operator is assembled upstream from the carry-mass tower.  Its zero
predicate is therefore just boundary closure of that already weighted state.

The two-coordinate `(sigma,time)` family below is a secondary radial
presentation.  Its factorization theorem says when that deformation represents
the native tower; it does not inject mass into the operator after construction.
-/

namespace NativeCarryGeometry.Operator

noncomputable section

/-- Zero predicate of the native real operator: the tower is already weighted. -/
abbrev IsNativeRealCarryOperatorZero
    (camera : ℕ) (time : ℝ) : Prop :=
  NativeBoundaryConvergesToZero camera time

/--
A zero in the radial deformation chart that genuinely represents the native
mass-built tower.
-/
def IsRadialDeformationPresentationZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  RealCarryEnergyCompatible sigma time ∧
    RadialDeformationBoundaryConvergesToZero camera sigma time

/-- Compatibility alias for the radial-presentation predicate. -/
abbrev IsRealCarryOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  IsRadialDeformationPresentationZero camera sigma time

/--
NCG-OPR-004: Radial Presentation Factorization.

For every natural camera width, a radial deformation represents a native zero
exactly on the unique native shell and at a native boundary resonance.
-/
theorem isRealCarryOperatorZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    IsRealCarryOperatorZero camera sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsBoundaryResonance camera time := by
  unfold IsRealCarryOperatorZero
    IsRadialDeformationPresentationZero
  constructor
  · rintro ⟨henergy, hclose⟩
    have hpositional :
        Measure.PositionalMassCompatible 2 sigma :=
      (Measure.positionalMassCompatible_iff_realEnergyCompatible
        2 (by norm_num) sigma time).2 henergy
    have hsigma : sigma = (1 : ℝ) / 2 :=
      (Measure.positionalMassCompatible_iff
        2 (by norm_num) sigma).1 hpositional
    subst sigma
    exact ⟨rfl,
      (radialDeformationBoundary_half_iff_native camera time).1 hclose⟩
  · rintro ⟨hsigma, hclose⟩
    subst sigma
    have hpositional :
        Measure.PositionalMassCompatible 2 ((1 : ℝ) / 2) :=
      (Measure.positionalMassCompatible_iff
        2 (by norm_num) ((1 : ℝ) / 2)).2 rfl
    have henergy :
        RealCarryEnergyCompatible ((1 : ℝ) / 2) time :=
      (Measure.positionalMassCompatible_iff_realEnergyCompatible
        2 (by norm_num) ((1 : ℝ) / 2) time).1 hpositional
    exact ⟨henergy,
      (radialDeformationBoundary_half_iff_native camera time).2 hclose⟩

/-- The native operator zero and boundary resonance are literally the same predicate. -/
theorem isNativeRealCarryOperatorZero_iff
    (camera : ℕ) (time : ℝ) :
    IsNativeRealCarryOperatorZero camera time ↔
      IsBoundaryResonance camera time :=
  Iff.rfl

/-- NCG-OPR-005: Radial-Presentation Uniqueness Corollary. -/
theorem realCarryOperatorZero_sigma_eq_half
    {camera : ℕ} {sigma time : ℝ}
    (hzero : IsRealCarryOperatorZero camera sigma time) :
    sigma = (1 : ℝ) / 2 :=
  ((isRealCarryOperatorZero_iff camera sigma time).1 hzero).1

/-- NCG-OPR-006: Off-Shell Nonrepresentation Corollary. -/
theorem not_realCarryOperatorZero_of_sigma_ne_half
    {camera : ℕ} {sigma time : ℝ}
    (hoff : sigma ≠ (1 : ℝ) / 2) :
    ¬ IsRealCarryOperatorZero camera sigma time := by
  intro hzero
  exact hoff (realCarryOperatorZero_sigma_eq_half hzero)

end
end NativeCarryGeometry.Operator
