import NativeCarryGeometry.Measure.CarryProbability
import NativeCarryGeometry.Operator.QuadraticDomain
import NativeCarryGeometry.Operator.BoundaryOperator

/-!
# Native and radial-family operator zeros

The native operator is assembled upstream from the carry-mass tower and has
only phase time as a free coordinate.  The larger radial family varies the
amplitude exponent `sigma` and has its own raw zero predicate at every supplied
coordinate.

Mass compatibility is kept separate.  It says when a radial-family point
represents the already weighted native operator; it never defines whether the
radial resultant is zero.
-/

namespace NativeCarryGeometry.Operator

noncomputable section

/-- Zero of the fixed, carry-built native operator. -/
abbrev IsNativeCarryOperatorZero
    (camera : ℕ) (time : ℝ) : Prop :=
  NativeBoundaryConvergesToZero camera time

/-- Coordinate-labelled alias for the fixed native operator zero. -/
abbrev IsNativeRealCarryOperatorZero
    (camera : ℕ) (time : ℝ) : Prop :=
  IsNativeCarryOperatorZero camera time

/--
Raw zero of the radial operator family at the supplied `(sigma,time)`
coordinates.  No mass-compatibility premise is part of this predicate.
-/
abbrev IsRadialCarryOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  RadialChartCancelsAt camera sigma time

/-- Public coordinate-labelled spelling of the raw radial-family zero predicate. -/
abbrev IsRealCarryOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  IsRadialCarryOperatorZero camera sigma time

/--
A radial-family zero represents a zero of the fixed native operator precisely
when the radial deformation also preserves the upstream native mass.
-/
def RadialChartRepresentsNativeZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  RadialDeformationRepresentsNativeMass sigma time ∧
    IsRadialCarryOperatorZero camera sigma time

/--
NCG-OPR-004: Radial Operator Zero/Boundary Cancellation Identity.

Calling the radial resultant a zero records exactly its boundary cancellation;
no critical-shell condition is hidden in the predicate.
-/
theorem isRealCarryOperatorZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    IsRealCarryOperatorZero camera sigma time ↔
      RadialChartCancelsAt camera sigma time :=
  Iff.rfl

/-- The fixed native operator-zero predicate is its boundary resonance. -/
theorem isNativeCarryOperatorZero_iff
    (camera : ℕ) (time : ℝ) :
    IsNativeCarryOperatorZero camera time ↔
      IsBoundaryResonance camera time :=
  Iff.rfl

/-- Coordinate-labelled form of `isNativeCarryOperatorZero_iff`. -/
theorem isNativeRealCarryOperatorZero_iff
    (camera : ℕ) (time : ℝ) :
    IsNativeRealCarryOperatorZero camera time ↔
      IsBoundaryResonance camera time :=
  isNativeCarryOperatorZero_iff camera time

/--
NCG-OPR-005: Half-Shell Radial/Native Zero Identity.

At the carry-built half exponent, the raw radial family is extensionally the
fixed native operator, so their zero predicates agree.
-/
theorem realCarryOperatorZero_half_iff_native
    (camera : ℕ) (time : ℝ) :
    IsRealCarryOperatorZero camera ((1 : ℝ) / 2) time ↔
      IsNativeCarryOperatorZero camera time := by
  change
    RadialDeformationBoundaryConvergesToZero
        camera ((1 : ℝ) / 2) time ↔
      NativeBoundaryConvergesToZero camera time
  exact radialDeformationBoundary_half_iff_native camera time

/--
NCG-OPR-006: Native Representation Predicate Separation.

Representation is exactly the conjunction of an independent mass-compatibility
statement and a raw radial-family zero.
-/
theorem radialChartRepresentsNativeZero_iff_massCompatible_and_zero
    (camera : ℕ) (sigma time : ℝ) :
    RadialChartRepresentsNativeZero camera sigma time ↔
      RadialDeformationRepresentsNativeMass sigma time ∧
        IsRealCarryOperatorZero camera sigma time :=
  Iff.rfl

/--
NCG-OPR-007: Canonical Radial-Chart Native-Representation Factorization.

This theorem classifies representations of the fixed native zero locus.  It
does not classify the raw zero locus of the radial family.
-/
theorem radialChartRepresentsNativeZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    RadialChartRepresentsNativeZero camera sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsNativeCarryOperatorZero camera time := by
  constructor
  · rintro ⟨hmass, hzero⟩
    have hsigma : sigma = (1 : ℝ) / 2 :=
      (radialDeformationRepresentsNativeMass_iff sigma time).1 hmass
    subst sigma
    exact ⟨rfl,
      (realCarryOperatorZero_half_iff_native camera time).1 hzero⟩
  · rintro ⟨hsigma, hzero⟩
    subst sigma
    exact ⟨
      (radialDeformationRepresentsNativeMass_iff
        ((1 : ℝ) / 2) time).2 rfl,
      (realCarryOperatorZero_half_iff_native camera time).2 hzero⟩

end
end NativeCarryGeometry.Operator
