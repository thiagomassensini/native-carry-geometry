import NativeCarryGeometry.Bracket.RadialCurvature
import NativeCarryGeometry.Equivalence.RealAnalyticBoundary

/-!
# Raw Genuine confinement: exact native reduction

This experiment isolates the stronger statement in which raw camera-three
boundary closure, rather than the full carry-operator zero predicate, must
force the quadratic shell.  Only the native carry geometry is used.

## Formal status

This file is a Lean-checked reduction, not a declaration that unconditional
raw confinement has already been discharged.  It proves that the following
global propositions are equivalent:

* raw canonical-continuation confinement;
* raw camera-three boundary confinement;
* reconstruction of the real carry-energy law from raw closure;
* saturation of the quadratic radial branch; and
* annihilation of the native signed radial curvature.

The theorem `rawCanonicalContinuationConfinement_of_boundaryCurvature`
therefore exposes the remaining bridge as the explicit hypothesis
`RawCameraThreeBoundaryDetectsRadialCurvature`.  No compatibility condition is
inserted into the definition of raw closure, and no terminal unconditional
theorem is claimed by this experimental module.
-/

open scoped Topology

namespace NativeCarryGeometry.Experimental

open Filter

noncomputable section

/--
The stronger real-plane target: every raw zero of the nondegenerate primitive
camera in the canonical strip lies on the quadratic carry shell.
-/
def RawCameraThreeBoundaryConfinement : Prop :=
  ∀ {sigma time : ℝ},
    0 < sigma →
    sigma < 1 →
    Operator.BoundaryConvergesToZero 3 sigma time →
      sigma = (1 : ℝ) / 2

/--
Equivalent mass form of the same target: raw boundary closure reconstructs
the energy law of the uncompressed carry state.
-/
def RawCameraThreeBoundaryPreservesEnergy : Prop :=
  ∀ {sigma time : ℝ},
    0 < sigma →
    sigma < 1 →
    Operator.BoundaryConvergesToZero 3 sigma time →
      Operator.RealCarryEnergyCompatible sigma time

/--
Branch form of the same target: a closing raw camera saturates the quadratic
branch energy determined by positional carry.
-/
def RawCameraThreeBoundarySaturatesBranch : Prop :=
  ∀ {sigma time : ℝ},
    0 < sigma →
    sigma < 1 →
    Operator.BoundaryConvergesToZero 3 sigma time →
      Measure.radialBranchEnergy 3 sigma = 1

/--
The requested statement in the canonical analytic presentation.
-/
def RawCanonicalContinuationConfinement : Prop :=
  ∀ {s : ℂ},
    s ∈ Analytic.canonicalStrip →
    Analytic.canonicalCarryContinuation s = 0 →
      s.re = (1 : ℝ) / 2

/--
Native curvature form of the target.  The center `2` is the first convenient
strictly interior center for camera `3`, whose half-range is `1`.
-/
def RawCameraThreeBoundaryDetectsRadialCurvature : Prop :=
  ∀ {sigma time : ℝ},
    0 < sigma →
    sigma < 1 →
    Operator.BoundaryConvergesToZero 3 sigma time →
      Bracket.Curvature.balancedRadialCurvatureAtSigma
        3 sigma 2 = 0

/--
Raw closure always makes the visible energy of the aggregate resultant tend
to zero.  This is weaker than recovering the pointwise carry energy law.
-/
theorem visibleEnergy_tendsto_zero_of_boundaryConvergesToZero
    {camera : ℕ} {sigma time : ℝ}
    (hclose :
      Operator.BoundaryConvergesToZero camera sigma time) :
    Tendsto
      (fun cutoff : ℕ =>
        Operator.visibleEnergy
          (Operator.finiteRealCarryOperator
            camera cutoff sigma time))
      atTop (nhds 0) := by
  have henergy :
      Continuous
        (fun u : ℝ × ℝ => u.1 ^ 2 + u.2 ^ 2) :=
    (continuous_fst.pow 2).add (continuous_snd.pow 2)
  simpa using henergy.continuousAt.tendsto.comp hclose

/--
The raw confinement statement is exactly the assertion that raw closure
reconstructs the quadratic carry-energy law.
-/
theorem rawCameraThreeBoundaryConfinement_iff_preservesEnergy :
    RawCameraThreeBoundaryConfinement ↔
      RawCameraThreeBoundaryPreservesEnergy := by
  constructor
  · intro hconf sigma time hsigma0 hsigma1 hclose
    exact
      (Operator.realCarryEnergyCompatible_iff sigma time).2
        (hconf hsigma0 hsigma1 hclose)
  · intro henergy sigma time hsigma0 hsigma1 hclose
    exact
      (Operator.realCarryEnergyCompatible_iff sigma time).1
        (henergy hsigma0 hsigma1 hclose)

/--
The requested confinement is exactly saturation of the native radial branch.
-/
theorem rawCameraThreeBoundaryConfinement_iff_saturatesBranch :
    RawCameraThreeBoundaryConfinement ↔
      RawCameraThreeBoundarySaturatesBranch := by
  constructor
  · intro hconf sigma time hsigma0 hsigma1 hclose
    exact
      (Measure.radialBranchEnergy_eq_one_iff
        3 (by norm_num) hsigma0).2
        (hconf hsigma0 hsigma1 hclose)
  · intro hsaturates sigma time hsigma0 hsigma1 hclose
    exact
      (Measure.radialBranchEnergy_eq_one_iff
        3 (by norm_num) hsigma0).1
        (hsaturates hsigma0 hsigma1 hclose)

/--
The raw real-plane target and the raw canonical-continuation target are
literally the same proposition through the already proved camera-three
boundary representation theorem.
-/
theorem rawCanonicalContinuationConfinement_iff_boundaryConfinement :
    RawCanonicalContinuationConfinement ↔
      RawCameraThreeBoundaryConfinement := by
  constructor
  · intro hcanonical sigma time hsigma0 hsigma1 hclose
    let s : ℂ := ⟨sigma, time⟩
    have hs : s ∈ Analytic.canonicalStrip := by
      exact
        ⟨by simpa [s] using hsigma0,
          by simpa [s] using hsigma1⟩
    have hcloseAtS :
        Operator.BoundaryConvergesToZero 3 s.re s.im := by
      simpa [s] using hclose
    have hzero :
        Analytic.canonicalCarryContinuation s = 0 :=
      (Equivalence.boundaryConvergesToZero_iff_canonicalCarryContinuation_eq_zero
        hs).1 hcloseAtS
    simpa [s] using hcanonical hs hzero
  · intro hboundary s hs hzero
    have hclose :
        Operator.BoundaryConvergesToZero 3 s.re s.im :=
      (Equivalence.boundaryConvergesToZero_iff_canonicalCarryContinuation_eq_zero
        hs).2 hzero
    exact hboundary hs.1 hs.2 hclose

/--
Direct carry formulation: raw continuation confinement is the same theorem as
quadratic branch saturation at every raw camera-three closure.
-/
theorem rawCanonicalContinuationConfinement_iff_saturatesBranch :
    RawCanonicalContinuationConfinement ↔
      RawCameraThreeBoundarySaturatesBranch :=
  rawCanonicalContinuationConfinement_iff_boundaryConfinement.trans
    rawCameraThreeBoundaryConfinement_iff_saturatesBranch

/--
Direct state formulation: raw continuation confinement is the same theorem as
reconstruction of the real carry-energy law from raw closure.
-/
theorem rawCanonicalContinuationConfinement_iff_preservesEnergy :
    RawCanonicalContinuationConfinement ↔
      RawCameraThreeBoundaryPreservesEnergy :=
  rawCanonicalContinuationConfinement_iff_boundaryConfinement.trans
    rawCameraThreeBoundaryConfinement_iff_preservesEnergy

/--
The desired raw confinement is also exactly the assertion that a raw closing
boundary annihilates the native signed radial curvature.
-/
theorem rawCameraThreeBoundaryConfinement_iff_detectsRadialCurvature :
    RawCameraThreeBoundaryConfinement ↔
      RawCameraThreeBoundaryDetectsRadialCurvature := by
  constructor
  · intro hconf sigma time hsigma0 hsigma1 hclose
    apply
      (Bracket.Curvature.balancedRadialCurvature_eq_zero_iff
        3 (by norm_num) (by norm_num) hsigma0
        (by
          norm_num [Internal.Genuine.Cp.halfRange])).2
    exact hconf hsigma0 hsigma1 hclose
  · intro hcurvature sigma time hsigma0 hsigma1 hclose
    exact
      (Bracket.Curvature.balancedRadialCurvature_eq_zero_iff
        3 (by norm_num) (by norm_num) hsigma0
        (by
          norm_num [Internal.Genuine.Cp.halfRange])).1
        (hcurvature hsigma0 hsigma1 hclose)

/--
One native bridge is sufficient for the requested theorem.  The remaining
proof obligation is deliberately visible in the hypothesis rather than
hidden inside the definition of a zero.
-/
theorem rawCanonicalContinuationConfinement_of_boundaryCurvature
    (hcurvature : RawCameraThreeBoundaryDetectsRadialCurvature) :
    RawCanonicalContinuationConfinement :=
  (rawCanonicalContinuationConfinement_iff_boundaryConfinement).2
    ((rawCameraThreeBoundaryConfinement_iff_detectsRadialCurvature).2
      hcurvature)

end

end NativeCarryGeometry.Experimental
