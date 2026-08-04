import NativeCarryGeometry.Measure.QuadraticAmplitude
import NativeCarryGeometry.Operator.RealState

/-!
# Quadratic realization of the native tower

This is the first cross-layer module after the carry measure and the native
real state have both been constructed.  The import direction is deliberate:
the measure is upstream of the state, never injected into an already-defined
operator.
-/

namespace NativeCarryGeometry.Measure

noncomputable section

/-- NCG-AMP-006: Quadratic Domain Crosswalk. -/
theorem positionalMassCompatible_iff_realEnergyCompatible
    (b : ℕ) (hb : 1 < b) (sigma time : ℝ) :
    PositionalMassCompatible b sigma ↔
      Operator.RealCarryEnergyCompatible sigma time := by
  rw [positionalMassCompatible_iff b hb sigma,
    Operator.realCarryEnergyCompatible_iff sigma time]

/--
Canonical-name form: the positional mass domain and the radial deformation
represent the same already-constructed native mass shell.
-/
theorem positionalMassCompatible_iff_radialDeformationRepresentsNativeMass
    (b : ℕ) (hb : 1 < b) (sigma time : ℝ) :
    PositionalMassCompatible b sigma ↔
      Operator.RadialDeformationRepresentsNativeMass sigma time :=
  positionalMassCompatible_iff_realEnergyCompatible
    b hb sigma time

end
end NativeCarryGeometry.Measure
