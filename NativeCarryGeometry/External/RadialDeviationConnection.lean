import NativeCarryGeometry.External.CanonicalVerticalReconstruction
import NativeCarryGeometry.Operator.BoundaryOperator
import NativeCarryGeometry.Bracket.RadialCurvature
import NativeCarryGeometry.Equivalence.ComplexCoordinates

/-!
# Radial-deviation connection probe

Every finite prefix of the radial resultant sequence is stored
coordinate-for-coordinate in the transported vertical core.  The vertical
TFVD reconstruction therefore preserves the complete prefix before the camera
readout is interpreted.

The final theorem asks whether raw boundary cancellation alone forces the local
radial-deviation detector to vanish.  It is intentionally compiled as a probe:
the only acceptable proof is one derived from the checked-in definitions and
the transported lossless reconstruction.
-/

open scoped Topology

namespace NativeCarryGeometry.External

open Filter

noncomputable section

/-- Finite prefix of the exact radial-resultant sequence, before taking its
boundary limit. -/
noncomputable def radialResultantPrefixCore
    (camera prefix : ℕ) (sigma time : ℝ) : NativeVerticalCore :=
  Finsupp.onFinset (Finset.range prefix)
    (fun cutoff =>
      if cutoff < prefix then
        NativeCarryGeometry.Equivalence.complexCoordinates
          (NativeCarryGeometry.Operator.finiteRadialDeformation
            camera cutoff sigma time)
      else 0)
    (by
      intro cutoff hcutoff
      by_contra hmem
      have hnot : ¬ cutoff < prefix := by
        simpa only [Finset.mem_range, not_false_eq_true] using hmem
      simp [hnot] at hcutoff)

/-- Every active coordinate is literally the corresponding finite real
resultant in faithful complex coordinates. -/
@[simp] theorem radialResultantPrefixCore_apply_of_lt
    (camera prefix : ℕ) (sigma time : ℝ)
    (cutoff : ℕ) (hcutoff : cutoff < prefix) :
    radialResultantPrefixCore camera prefix sigma time cutoff =
      NativeCarryGeometry.Equivalence.complexCoordinates
        (NativeCarryGeometry.Operator.finiteRadialDeformation
          camera cutoff sigma time) := by
  classical
  simp [radialResultantPrefixCore, hcutoff]

/-- The transported vertical machinery reconstructs every finite prefix
without losing a coordinate. -/
theorem radialResultantPrefixCore_vertical_reconstruction
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (camera prefix : ℕ) (sigma time : ℝ) :
    carryVerticalL2WeightedGreen q
          (carryWeightedVerticalCenteredBracket q
            (nativeCanonicalVerticalRealization
              (radialResultantPrefixCore
                camera prefix sigma time))) +
        carryWeightedVerticalReturn q hqpos.le hq1
          (carryWeightedVerticalTrace q
            (nativeCanonicalVerticalRealization
              (radialResultantPrefixCore
                camera prefix sigma time))) =
      nativeCanonicalVerticalRealization
        (radialResultantPrefixCore camera prefix sigma time) :=
  nativeCanonicalTfvd_vertical_reconstruction
    q hqpos hq1
      (radialResultantPrefixCore camera prefix sigma time)

/--
Strong connection probe: raw cancellation of the radial resultant should force
the radial-deviation detector to vanish and hence force the quadratic
equilibrium exponent.

The reconstruction hypothesis below is not assumed: it is generated from the
transported theorem for every finite prefix.
-/
theorem radialChartCancelsAt_sigma_eq_half_via_vertical_reconstruction
    (camera : ℕ) (hprime : Nat.Prime camera) (hodd : Odd camera)
    {sigma time center : ℝ} (hsigma : 0 < sigma)
    (hcenter :
      (NativeCarryGeometry.Internal.Genuine.Cp.halfRange camera : ℝ) <
        center)
    (hzero :
      NativeCarryGeometry.Operator.RadialChartCancelsAt
        camera sigma time) :
    sigma = (1 : ℝ) / 2 := by
  have hreconstruction :
      ∀ prefix : ℕ,
        carryVerticalL2WeightedGreen ((1 : ℝ) / 2)
              (carryWeightedVerticalCenteredBracket ((1 : ℝ) / 2)
                (nativeCanonicalVerticalRealization
                  (radialResultantPrefixCore
                    camera prefix sigma time))) +
            carryWeightedVerticalReturn ((1 : ℝ) / 2)
              (by norm_num : (0 : ℝ) ≤ 1 / 2)
              (by norm_num : (1 : ℝ) / 2 < 1)
              (carryWeightedVerticalTrace ((1 : ℝ) / 2)
                (nativeCanonicalVerticalRealization
                  (radialResultantPrefixCore
                    camera prefix sigma time))) =
          nativeCanonicalVerticalRealization
            (radialResultantPrefixCore
              camera prefix sigma time) := by
    intro prefix
    exact radialResultantPrefixCore_vertical_reconstruction
      ((1 : ℝ) / 2) (by norm_num) (by norm_num)
      camera prefix sigma time
  apply
    (NativeCarryGeometry.Bracket.Curvature.balancedRadialCurvature_eq_zero_iff
      camera hprime hodd hsigma hcenter).1
  aesop

end

end NativeCarryGeometry.External
