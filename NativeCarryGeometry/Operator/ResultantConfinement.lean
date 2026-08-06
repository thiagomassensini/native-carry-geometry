import NativeCarryGeometry.Operator.BoundaryOperator
import NativeCarryGeometry.Bracket.RadialCurvature

/-!
# Resultant confinement proof probe

This module asks Lean for the strong statement directly: cancellation of the
resultant itself must force the quadratic equilibrium exponent.  No
mass-compatibility premise is conjoined to cancellation, and no alternate zero
predicate is introduced.
-/

namespace NativeCarryGeometry.Operator

noncomputable section

/--
Proof probe: for a nondegenerate odd-prime camera, cancellation of the radial
resultant itself forces the quadratic equilibrium exponent.

The final curvature-rigidity implication is already proved.  The remaining
goal is exactly the global-to-local bridge from resultant cancellation to
vanishing of the bracket curvature detector.
-/
theorem radialChartCancelsAt_sigma_eq_half
    (camera : ℕ) (hprime : Nat.Prime camera) (hodd : Odd camera)
    {sigma time center : ℝ} (hsigma : 0 < sigma)
    (hcenter :
      (Internal.Genuine.Cp.halfRange camera : ℝ) < center)
    (hzero : RadialChartCancelsAt camera sigma time) :
    sigma = (1 : ℝ) / 2 := by
  apply
    (Bracket.Curvature.balancedRadialCurvature_eq_zero_iff
      camera hprime hodd hsigma hcenter).1
  aesop

end

end NativeCarryGeometry.Operator
