import NativeCarryGeometry.External.CanonicalVerticalReconstruction
import NativeCarryGeometry.Operator.BoundaryOperator
import NativeCarryGeometry.Bracket.RadialCurvature
import NativeCarryGeometry.Equivalence.ComplexCoordinates

/-!
# Lossless vertical transport of the radial samples

This file keeps the order of construction explicit:

1. each positive-integer radial sample is stored in the finitely supported core;
2. the canonical inclusion sends that core coordinate-for-coordinate into ell squared;
3. the transported TFVD identity reconstructs the same vertical vector;
4. only then is the finite carry camera applied.

The resulting finite camera readout is exactly the complex-coordinate packaging
of the existing real radial resultant.  At the boundary this transports raw
cancellation to convergence of the reconstructed camera readout.

The last implication, from that zero readout to vanishing of the local radial
curvature, is named explicitly as a detector-faithfulness hypothesis.  The
lossless vertical bijection does not silently assume that additional
global-to-local implication.
-/

open scoped Topology BigOperators

namespace NativeCarryGeometry.External

open Filter

noncomputable section

/-- Store the first positive-integer radial samples before camera compression.
Core coordinate index represents the positive integer index + 1. -/
noncomputable def radialSamplePrefixCore
    (prefixSize : ℕ) (sigma time : ℝ) : NativeVerticalCore :=
  Finsupp.onFinset (Finset.range prefixSize)
    (fun index =>
      if index < prefixSize then
        NativeCarryGeometry.Equivalence.complexCoordinates
          (NativeCarryGeometry.Operator.radialDeformationState
            sigma time (((index + 1 : ℕ) : ℤ)))
      else 0)
    (by
      intro index hindex
      by_contra hmem
      have hnot : ¬ index < prefixSize := by
        simpa only [Finset.mem_range, not_false_eq_true] using hmem
      simp [hnot] at hindex)

/-- Every active core coordinate is literally its positive-integer radial
sample in faithful complex coordinates. -/
@[simp] theorem radialSamplePrefixCore_apply_of_lt
    (prefixSize : ℕ) (sigma time : ℝ)
    (index : ℕ) (hindex : index < prefixSize) :
    radialSamplePrefixCore prefixSize sigma time index =
      NativeCarryGeometry.Equivalence.complexCoordinates
        (NativeCarryGeometry.Operator.radialDeformationState
          sigma time (((index + 1 : ℕ) : ℤ))) := by
  classical
  simp [radialSamplePrefixCore, hindex]

/-- Read an ell-squared vertical vector as a field on the positive integers. -/
noncomputable def carryVerticalL2PositiveField
    (x : CarryVerticalL2) (n : ℤ) : ℂ :=
  if 0 < n then x (n.toNat - 1) else 0

/-- Inside a stored prefix, the vertical realization recovers the original
radial sample coordinate exactly. -/
@[simp] theorem carryVerticalL2PositiveField_realization_sample_of_bounds
    (prefixSize : ℕ) (sigma time : ℝ) {n : ℤ}
    (hnpos : 0 < n) (hnle : n ≤ (prefixSize : ℤ)) :
    carryVerticalL2PositiveField
        (nativeCanonicalVerticalRealization
          (radialSamplePrefixCore prefixSize sigma time)) n =
      NativeCarryGeometry.Equivalence.complexCoordinates
        (NativeCarryGeometry.Operator.radialDeformationState
          sigma time n) := by
  have hnnonneg : 0 ≤ n := le_of_lt hnpos
  have hcast : ((n.toNat : ℕ) : ℤ) = n :=
    Int.toNat_of_nonneg hnnonneg
  have hnNatPosInt : (0 : ℤ) < (n.toNat : ℤ) := by
    simpa only [hcast] using hnpos
  have hnNatPos : 0 < n.toNat := by
    exact_mod_cast hnNatPosInt
  have hnNatLeInt : (n.toNat : ℤ) ≤ (prefixSize : ℤ) := by
    simpa only [hcast] using hnle
  have hnNatLe : n.toNat ≤ prefixSize := by
    exact_mod_cast hnNatLeInt
  have hindex : n.toNat - 1 < prefixSize := by omega
  have hsucc : n.toNat - 1 + 1 = n.toNat := by omega
  rw [carryVerticalL2PositiveField, if_pos hnpos,
    nativeCanonicalVerticalRealization_apply,
    radialSamplePrefixCore_apply_of_lt
      prefixSize sigma time (n.toNat - 1) hindex,
    hsucc, hcast]

/-- Number of positive samples needed by the finite odd-prime carry camera. -/
def finiteRadialCameraSampleCount
    (camera cutoff : ℕ) : ℕ :=
  camera * cutoff +
    NativeCarryGeometry.Internal.Genuine.Cp.halfRange camera

/-- Apply the existing finite carry camera only after reading a vertical
ell-squared vector back on the positive integers. -/
noncomputable def verticalFiniteRadialCameraReadout
    (camera cutoff : ℕ) (x : CarryVerticalL2) : ℂ :=
  NativeCarryGeometry.Operator.finiteSaturatedBracketOperator
    camera cutoff (carryVerticalL2PositiveField x)

/-- The camera applied after lossless vertical storage is exactly the faithful
complex-coordinate form of the existing finite real radial resultant. -/
theorem verticalFiniteRadialCameraReadout_realization_eq
    (camera cutoff : ℕ)
    (hprime : Nat.Prime camera) (hodd : Odd camera)
    (sigma time : ℝ) :
    verticalFiniteRadialCameraReadout camera cutoff
        (nativeCanonicalVerticalRealization
          (radialSamplePrefixCore
            (finiteRadialCameraSampleCount camera cutoff)
            sigma time)) =
      NativeCarryGeometry.Equivalence.complexCoordinates
        (NativeCarryGeometry.Operator.finiteRadialDeformation
          camera cutoff sigma time) := by
  rw [NativeCarryGeometry.Equivalence.complexCoordinates_finiteOperator]
  change
    NativeCarryGeometry.Internal.Analytic.Cp.nativeCarryFiniteSaturatedChart
        camera cutoff
        (carryVerticalL2PositiveField
          (nativeCanonicalVerticalRealization
            (radialSamplePrefixCore
              (finiteRadialCameraSampleCount camera cutoff)
              sigma time))) =
      NativeCarryGeometry.Internal.Analytic.Cp.nativeCarryFiniteSaturatedChart
        camera cutoff
        (fun n =>
          NativeCarryGeometry.Equivalence.complexCoordinates
            (NativeCarryGeometry.Operator.realCarryState sigma time n))
  rw [
    NativeCarryGeometry.Internal.Analytic.Cp.nativeCarryFiniteSaturatedChart_eq_finiteChart
      camera cutoff hprime hodd
      (carryVerticalL2PositiveField
        (nativeCanonicalVerticalRealization
          (radialSamplePrefixCore
            (finiteRadialCameraSampleCount camera cutoff)
            sigma time)))]
  rw [
    NativeCarryGeometry.Internal.Analytic.Cp.nativeCarryFiniteSaturatedChart_eq_finiteChart
      camera cutoff hprime hodd
      (fun n =>
        NativeCarryGeometry.Equivalence.complexCoordinates
          (NativeCarryGeometry.Operator.realCarryState sigma time n))]
  rw [
    NativeCarryGeometry.Internal.Genuine.Cp.finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum
      camera hprime hodd cutoff
      (carryVerticalL2PositiveField
        (nativeCanonicalVerticalRealization
          (radialSamplePrefixCore
            (finiteRadialCameraSampleCount camera cutoff)
            sigma time)))]
  rw [
    NativeCarryGeometry.Internal.Genuine.Cp.finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum
      camera hprime hodd cutoff
      (fun n =>
        NativeCarryGeometry.Equivalence.complexCoordinates
          (NativeCarryGeometry.Operator.realCarryState sigma time n))]
  have hprefix :
      (∑ n ∈ Finset.Icc (1 : ℤ)
          ((camera : ℤ) * (cutoff : ℤ) +
            (NativeCarryGeometry.Internal.Genuine.Cp.halfRange camera : ℤ)),
        carryVerticalL2PositiveField
          (nativeCanonicalVerticalRealization
            (radialSamplePrefixCore
              (finiteRadialCameraSampleCount camera cutoff)
              sigma time)) n) =
        ∑ n ∈ Finset.Icc (1 : ℤ)
          ((camera : ℤ) * (cutoff : ℤ) +
            (NativeCarryGeometry.Internal.Genuine.Cp.halfRange camera : ℤ)),
          NativeCarryGeometry.Equivalence.complexCoordinates
            (NativeCarryGeometry.Operator.realCarryState sigma time n) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hbounds := Finset.mem_Icc.mp hn
    apply carryVerticalL2PositiveField_realization_sample_of_bounds
      (finiteRadialCameraSampleCount camera cutoff) sigma time hbounds.1
    simpa [finiteRadialCameraSampleCount] using hbounds.2
  have hcenters :
      (∑ k ∈ Finset.range cutoff,
        carryVerticalL2PositiveField
          (nativeCanonicalVerticalRealization
            (radialSamplePrefixCore
              (finiteRadialCameraSampleCount camera cutoff)
              sigma time))
          (NativeCarryGeometry.Internal.Genuine.Cp.alignedCenter camera k)) =
        ∑ k ∈ Finset.range cutoff,
          NativeCarryGeometry.Equivalence.complexCoordinates
            (NativeCarryGeometry.Operator.realCarryState sigma time
              (NativeCarryGeometry.Internal.Genuine.Cp.alignedCenter
                camera k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < cutoff := Finset.mem_range.mp hk
    have hcameraPos : 0 < camera := hprime.pos
    have hcameraInt : (0 : ℤ) < (camera : ℤ) := by
      exact_mod_cast hcameraPos
    have hkInt : (0 : ℤ) < ((k + 1 : ℕ) : ℤ) := by positivity
    have hcenterPos :
        (0 : ℤ) <
          NativeCarryGeometry.Internal.Genuine.Cp.alignedCenter
            camera k := by
      unfold NativeCarryGeometry.Internal.Genuine.Cp.alignedCenter
      exact mul_pos hcameraInt hkInt
    have hk1 : k + 1 ≤ cutoff := by omega
    have hmul :
        camera * (k + 1) ≤ camera * cutoff :=
      Nat.mul_le_mul_left camera hk1
    have hboundNat :
        camera * (k + 1) ≤
          finiteRadialCameraSampleCount camera cutoff := by
      unfold finiteRadialCameraSampleCount
      omega
    have hcenterLe :
        NativeCarryGeometry.Internal.Genuine.Cp.alignedCenter camera k ≤
          (finiteRadialCameraSampleCount camera cutoff : ℤ) := by
      unfold NativeCarryGeometry.Internal.Genuine.Cp.alignedCenter
      exact_mod_cast hboundNat
    exact carryVerticalL2PositiveField_realization_sample_of_bounds
      (finiteRadialCameraSampleCount camera cutoff) sigma time
      hcenterPos hcenterLe
  rw [hprefix, hcenters]

/-- The transported TFVD machinery reconstructs the whole stored sample
prefix without losing a coordinate. -/
theorem radialSamplePrefixCore_vertical_reconstruction
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (prefixSize : ℕ) (sigma time : ℝ) :
    carryVerticalL2WeightedGreen q
          (carryWeightedVerticalCenteredBracket q
            (nativeCanonicalVerticalRealization
              (radialSamplePrefixCore prefixSize sigma time))) +
        carryWeightedVerticalReturn q hqpos.le hq1
          (carryWeightedVerticalTrace q
            (nativeCanonicalVerticalRealization
              (radialSamplePrefixCore prefixSize sigma time))) =
      nativeCanonicalVerticalRealization
        (radialSamplePrefixCore prefixSize sigma time) :=
  nativeCanonicalTfvd_vertical_reconstruction
    q hqpos hq1 (radialSamplePrefixCore prefixSize sigma time)

/-- Coordinate form of the preceding theorem: reconstruction returns the
individual integer sample, not merely the camera resultant. -/
theorem radialSamplePrefixCore_coordinate_reconstruction
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (prefixSize : ℕ) (sigma time : ℝ)
    (index : ℕ) (hindex : index < prefixSize) :
    (carryVerticalL2WeightedGreen q
          (carryWeightedVerticalCenteredBracket q
            (nativeCanonicalVerticalRealization
              (radialSamplePrefixCore prefixSize sigma time))) +
        carryWeightedVerticalReturn q hqpos.le hq1
          (carryWeightedVerticalTrace q
            (nativeCanonicalVerticalRealization
              (radialSamplePrefixCore prefixSize sigma time)))) index =
      NativeCarryGeometry.Equivalence.complexCoordinates
        (NativeCarryGeometry.Operator.radialDeformationState
          sigma time (((index + 1 : ℕ) : ℤ))) := by
  rw [radialSamplePrefixCore_vertical_reconstruction
    q hqpos hq1 prefixSize sigma time]
  exact radialSamplePrefixCore_apply_of_lt
    prefixSize sigma time index hindex

/-- Applying the camera after the exact vertical reconstruction gives the
same finite radial resultant. -/
theorem verticalFiniteRadialCameraReadout_after_reconstruction
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (camera cutoff : ℕ)
    (hprime : Nat.Prime camera) (hodd : Odd camera)
    (sigma time : ℝ) :
    verticalFiniteRadialCameraReadout camera cutoff
        (carryVerticalL2WeightedGreen q
            (carryWeightedVerticalCenteredBracket q
              (nativeCanonicalVerticalRealization
                (radialSamplePrefixCore
                  (finiteRadialCameraSampleCount camera cutoff)
                  sigma time))) +
          carryWeightedVerticalReturn q hqpos.le hq1
            (carryWeightedVerticalTrace q
              (nativeCanonicalVerticalRealization
                (radialSamplePrefixCore
                  (finiteRadialCameraSampleCount camera cutoff)
                  sigma time)))) =
      NativeCarryGeometry.Equivalence.complexCoordinates
        (NativeCarryGeometry.Operator.finiteRadialDeformation
          camera cutoff sigma time) := by
  rw [radialSamplePrefixCore_vertical_reconstruction
    q hqpos hq1
      (finiteRadialCameraSampleCount camera cutoff) sigma time]
  exact verticalFiniteRadialCameraReadout_realization_eq
    camera cutoff hprime hodd sigma time

/-- Raw boundary cancellation is transported exactly to convergence to zero
of the camera readout of the reconstructed vertical sample cores. -/
theorem radialChartCancelsAt_tendsto_reconstructed_readout_zero
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (camera : ℕ) (hprime : Nat.Prime camera) (hodd : Odd camera)
    {sigma time : ℝ}
    (hzero :
      NativeCarryGeometry.Operator.RadialChartCancelsAt
        camera sigma time) :
    Tendsto
      (fun cutoff : ℕ =>
        verticalFiniteRadialCameraReadout camera cutoff
          (carryVerticalL2WeightedGreen q
              (carryWeightedVerticalCenteredBracket q
                (nativeCanonicalVerticalRealization
                  (radialSamplePrefixCore
                    (finiteRadialCameraSampleCount camera cutoff)
                    sigma time))) +
            carryWeightedVerticalReturn q hqpos.le hq1
              (carryWeightedVerticalTrace q
                (nativeCanonicalVerticalRealization
                  (radialSamplePrefixCore
                    (finiteRadialCameraSampleCount camera cutoff)
                    sigma time)))))
      atTop (nhds 0) := by
  have hcontinuous :
      Continuous
        (fun u : NativeCarryGeometry.Operator.RealCarryPlane =>
          NativeCarryGeometry.Equivalence.complexCoordinates u) := by
    change Continuous (fun u : ℝ × ℝ =>
      Complex.equivRealProdCLM.symm u)
    exact Complex.equivRealProdCLM.symm.continuous
  have hpacked :
      Tendsto
        (fun cutoff : ℕ =>
          NativeCarryGeometry.Equivalence.complexCoordinates
            (NativeCarryGeometry.Operator.finiteRadialDeformation
              camera cutoff sigma time))
        atTop (nhds 0) := by
    have hmap := hcontinuous.continuousAt.tendsto.comp hzero
    simpa only [Function.comp_def, map_zero] using hmap
  have heq :
      (fun cutoff : ℕ =>
        verticalFiniteRadialCameraReadout camera cutoff
          (carryVerticalL2WeightedGreen q
              (carryWeightedVerticalCenteredBracket q
                (nativeCanonicalVerticalRealization
                  (radialSamplePrefixCore
                    (finiteRadialCameraSampleCount camera cutoff)
                    sigma time))) +
            carryWeightedVerticalReturn q hqpos.le hq1
              (carryWeightedVerticalTrace q
                (nativeCanonicalVerticalRealization
                  (radialSamplePrefixCore
                    (finiteRadialCameraSampleCount camera cutoff)
                    sigma time))))) =
        (fun cutoff : ℕ =>
          NativeCarryGeometry.Equivalence.complexCoordinates
            (NativeCarryGeometry.Operator.finiteRadialDeformation
              camera cutoff sigma time)) := by
    funext cutoff
    exact verticalFiniteRadialCameraReadout_after_reconstruction
      q hqpos hq1 camera cutoff hprime hodd sigma time
  rw [heq]
  exact hpacked

/-- The precise remaining global-to-local statement.  It says that a zero
limit of the reconstructed camera readout is detected by the local radial
curvature.  It is deliberately separate from lossless vertical
reconstruction. -/
def ReconstructedReadoutDetectsRadialDeviationAt
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (camera : ℕ) (sigma time center : ℝ) : Prop :=
  Tendsto
      (fun cutoff : ℕ =>
        verticalFiniteRadialCameraReadout camera cutoff
          (carryVerticalL2WeightedGreen q
              (carryWeightedVerticalCenteredBracket q
                (nativeCanonicalVerticalRealization
                  (radialSamplePrefixCore
                    (finiteRadialCameraSampleCount camera cutoff)
                    sigma time))) +
            carryWeightedVerticalReturn q hqpos.le hq1
              (carryWeightedVerticalTrace q
                (nativeCanonicalVerticalRealization
                  (radialSamplePrefixCore
                    (finiteRadialCameraSampleCount camera cutoff)
                    sigma time)))))
      atTop (nhds 0) →
    NativeCarryGeometry.Bracket.Curvature.balancedRadialCurvatureAtSigma
      camera sigma center = 0

/-- Conditional confinement theorem.  Everything before the detector
faithfulness assumption is supplied by the checked-in definitions and exact
vertical reconstruction; the assumption is exactly the missing
global-to-local implication. -/
theorem radialChartCancelsAt_sigma_eq_half_of_reconstructed_detection
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (camera : ℕ) (hprime : Nat.Prime camera) (hodd : Odd camera)
    {sigma time center : ℝ} (hsigma : 0 < sigma)
    (hcenter :
      (NativeCarryGeometry.Internal.Genuine.Cp.halfRange camera : ℝ) <
        center)
    (hdetect :
      ReconstructedReadoutDetectsRadialDeviationAt
        q hqpos hq1 camera sigma time center)
    (hzero :
      NativeCarryGeometry.Operator.RadialChartCancelsAt
        camera sigma time) :
    sigma = (1 : ℝ) / 2 := by
  apply
    (NativeCarryGeometry.Bracket.Curvature.balancedRadialCurvature_eq_zero_iff
      camera hprime hodd hsigma hcenter).1
  apply hdetect
  exact radialChartCancelsAt_tendsto_reconstructed_readout_zero
    q hqpos hq1 camera hprime hodd hzero

end

end NativeCarryGeometry.External
