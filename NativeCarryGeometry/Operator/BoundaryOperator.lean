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
The finite resultants of a camera converge to the zero vector at the stated
radial exponent and phase time.
-/
def BoundaryConvergesToZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  Tendsto
    (fun cutoff : ℕ =>
      finiteRealCarryOperator camera cutoff sigma time)
    atTop (nhds 0)

/--
A boundary resonance is closure after the quadratic carry shell has been
fixed.  The remaining free coordinate is `time`.
-/
def IsBoundaryResonance
    (camera : ℕ) (time : ℝ) : Prop :=
  BoundaryConvergesToZero camera ((1 : ℝ) / 2) time

end
end NativeCarryGeometry.Operator
