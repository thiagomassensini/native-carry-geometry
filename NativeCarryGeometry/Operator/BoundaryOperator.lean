import NativeCarryGeometry.Operator.FiniteRealOperator

/-!
# Boundary closure of the real carry operator

This module introduces only convergence of finite real resultants.  It has no
dependency on Green identities, spectral pencils, or an external analytic
function.
-/

open scoped Topology

namespace NativeCarryGeometry.Operator

open Filter

noncomputable section

/--
The finite resultants of the native carry-built operator converge to zero.
Only the phase time remains free because the vertical tower already contains
its carry mass and quadratic amplitude.
-/
def NativeBoundaryConvergesToZero
    (camera : ℕ) (time : ℝ) : Prop :=
  Tendsto
    (fun cutoff : ℕ =>
      finiteNativeRealCarryOperator camera cutoff time)
    atTop (nhds 0)

/--
Boundary closure of the secondary radial deformation family.
-/
def RadialDeformationBoundaryConvergesToZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  Tendsto
    (fun cutoff : ℕ =>
      finiteRadialDeformation camera cutoff sigma time)
    atTop (nhds 0)

/-- Compatibility alias for radial-deformation boundary closure. -/
abbrev BoundaryConvergesToZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  RadialDeformationBoundaryConvergesToZero camera sigma time

/-- The half-exponent deformation chart is exactly the native boundary. -/
theorem radialDeformationBoundary_half_iff_native
    (camera : ℕ) (time : ℝ) :
    RadialDeformationBoundaryConvergesToZero
        camera ((1 : ℝ) / 2) time ↔
      NativeBoundaryConvergesToZero camera time := by
  unfold RadialDeformationBoundaryConvergesToZero
    NativeBoundaryConvergesToZero
  simp only [finiteRadialDeformation,
    finiteNativeRealCarryOperator,
    Internal.Analytic.Cp.nativeCarryRealPlaneFiniteChart_eq_chartAt_half]

/--
A boundary resonance is precisely a zero of the native boundary operator.
The mass is already in the tower; it is not conjoined here as an extra test.
-/
def IsBoundaryResonance
    (camera : ℕ) (time : ℝ) : Prop :=
  NativeBoundaryConvergesToZero camera time

end
end NativeCarryGeometry.Operator
