import NativeCarryGeometry.Measure.CarryProbability
import NativeCarryGeometry.Operator.QuadraticDomain
import NativeCarryGeometry.Operator.BoundaryOperator

/-!
# Native operator-zero predicate and radial-chart representation

The native operator is assembled upstream from the carry-mass tower.  Its zero
predicate is therefore just boundary closure of that already weighted state.

The two-coordinate `(sigma,time)` family below is a secondary radial
presentation.  Its factorization theorem says when that deformation represents
the native tower; the presentation never supplies mass to the operator later.
-/

namespace NativeCarryGeometry.Operator

noncomputable section

/--
The one native operator-zero predicate.  The tower is already
weighted by the carry mass before this predicate is formed.
-/
abbrev IsNativeCarryOperatorZero
    (camera : ℕ) (time : ℝ) : Prop :=
  NativeBoundaryConvergesToZero camera time

/--
Legacy coordinate-labelled alias.  It is definitionally the same native
operator-zero predicate, not a separate “real zero”.
-/
abbrev IsNativeRealCarryOperatorZero
    (camera : ℕ) (time : ℝ) : Prop :=
  IsNativeCarryOperatorZero camera time

/--
The ambient radial chart represents the native zero locus exactly when it preserves
the upstream carry mass and its deformed boundary cancels.  This is a
representation predicate, not another kind of zero.
-/
def RadialChartRepresentsNativeZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  RadialDeformationRepresentsNativeMass sigma time ∧
    RadialChartCancelsAt camera sigma time

/-- Legacy compatibility alias for `RadialChartRepresentsNativeZero`. -/
abbrev IsRadialDeformationPresentationZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  RadialChartRepresentsNativeZero camera sigma time

/-- Legacy compatibility alias; this does not introduce an additional operator-zero predicate. -/
abbrev IsRealCarryOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  RadialChartRepresentsNativeZero camera sigma time

/--
NCG-OPR-004: Legacy Boundary Radial-Chart Native-Representation Factorization.

For every natural camera width, a radial deformation represents the native
zero locus exactly on the unique native shell and at a native boundary
resonance.
-/
theorem isRealCarryOperatorZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    IsRealCarryOperatorZero camera sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsBoundaryResonance camera time := by
  unfold IsRealCarryOperatorZero
    RadialChartRepresentsNativeZero
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
        RadialDeformationRepresentsNativeMass ((1 : ℝ) / 2) time :=
      (Measure.positionalMassCompatible_iff_realEnergyCompatible
        2 (by norm_num) ((1 : ℝ) / 2) time).1 hpositional
    exact ⟨henergy,
      (radialDeformationBoundary_half_iff_native camera time).2 hclose⟩

/-- The native operator-zero predicate and boundary resonance are definitionally equal. -/
theorem isNativeCarryOperatorZero_iff
    (camera : ℕ) (time : ℝ) :
    IsNativeCarryOperatorZero camera time ↔
      IsBoundaryResonance camera time :=
  Iff.rfl

/-- Legacy coordinate-labelled form of `isNativeCarryOperatorZero_iff`. -/
theorem isNativeRealCarryOperatorZero_iff
    (camera : ℕ) (time : ℝ) :
    IsNativeRealCarryOperatorZero camera time ↔
      IsBoundaryResonance camera time :=
  isNativeCarryOperatorZero_iff camera time

/--
NCG-OPR-007: Canonical Radial-Chart Representation Factorization.

Varying `sigma` varies the quadratic norm of the ambient chart.  Such a chart
represents the native operator-zero locus exactly at the mass-preserving exponent
and at a native boundary resonance.
-/
theorem radialChartRepresentsNativeZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    RadialChartRepresentsNativeZero camera sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsNativeCarryOperatorZero camera time := by
  simpa [RadialChartRepresentsNativeZero, IsNativeCarryOperatorZero,
    IsBoundaryResonance] using
    (isRealCarryOperatorZero_iff camera sigma time)

/-- NCG-OPR-005: Legacy Radial-Chart Native-Representation Half-Shell Corollary. -/
theorem realCarryOperatorZero_sigma_eq_half
    {camera : ℕ} {sigma time : ℝ}
    (hzero : IsRealCarryOperatorZero camera sigma time) :
    sigma = (1 : ℝ) / 2 :=
  ((isRealCarryOperatorZero_iff camera sigma time).1 hzero).1

/-- NCG-OPR-006: Legacy Off-Shell Native-Nonrepresentation Corollary. -/
theorem not_realCarryOperatorZero_of_sigma_ne_half
    {camera : ℕ} {sigma time : ℝ}
    (hoff : sigma ≠ (1 : ℝ) / 2) :
    ¬ IsRealCarryOperatorZero camera sigma time := by
  intro hzero
  exact hoff (realCarryOperatorZero_sigma_eq_half hzero)

end
end NativeCarryGeometry.Operator
