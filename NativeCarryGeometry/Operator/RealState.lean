import NativeCarryGeometry.Measure.QuadraticAmplitude
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace NativeCarryGeometry.Internal.Analytic.Cp

noncomputable section

abbrev NativeCarryRealPlane := ℝ × ℝ

/-- Euclidean quadratic energy of a real carrier vector. -/
def nativeCarryRealPlaneEnergy (u : NativeCarryRealPlane) : ℝ :=
  u.1 ^ 2 + u.2 ^ 2

/-- Real unit direction at angle `theta`. -/
def nativeCarryRealDirection (theta : ℝ) : NativeCarryRealPlane :=
  (Real.cos theta, Real.sin theta)

/-- The real rotating direction has unit quadratic energy. -/
@[simp] theorem nativeCarryRealPlaneEnergy_direction (theta : ℝ) :
    nativeCarryRealPlaneEnergy (nativeCarryRealDirection theta) = 1 := by
  unfold nativeCarryRealPlaneEnergy nativeCarryRealDirection
  rw [add_comm, Real.sin_sq_add_cos_sq]

/--
Native real-plane sample.  Its amplitude is read directly from the
carry-measure tower; there is no free radial exponent in the native state.
The nonpositive branch only makes the field total on `Z`.
-/
def nativeCarryRealPlaneSample
    (t : ℝ) (n : ℤ) : NativeCarryRealPlane :=
  if 0 < n then
    let amplitude := NativeCarryGeometry.Measure.nativeTowerAmplitude n
    let angle := -t * Real.log (n : ℝ)
    (amplitude * Real.cos angle, amplitude * Real.sin angle)
  else
    0

/--
Secondary radial deformation of the native tower.  The parameter `sigma` is a
comparison coordinate; it is not part of the native operator's input data.
-/
def nativeCarryRealPlaneRadialDeformation
    (sigma t : ℝ) (n : ℤ) : NativeCarryRealPlane :=
  if 0 < n then
    let amplitude := (n : ℝ) ^ (-sigma)
    let angle := -t * Real.log (n : ℝ)
    (amplitude * Real.cos angle, amplitude * Real.sin angle)
  else
    0

/-- Compatibility name for the arbitrary radial deformation. -/
abbrev nativeCarryRealPlaneSampleAt
    (sigma t : ℝ) (n : ℤ) : NativeCarryRealPlane :=
  nativeCarryRealPlaneRadialDeformation sigma t n

/-- The carry-built native state is the half-exponent deformation chart. -/
theorem nativeCarryRealPlaneSample_eq_sampleAt_half
    (t : ℝ) (n : ℤ) :
    nativeCarryRealPlaneSample t n =
      nativeCarryRealPlaneSampleAt ((1 : ℝ) / 2) t n := by
  by_cases hn : 0 < n
  · have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
      have hnat : (n.toNat : ℤ) = n :=
        Int.toNat_of_nonneg (le_of_lt hn)
      exact_mod_cast hnat
    have hamp :
        NativeCarryGeometry.Measure.nativeTowerAmplitude n =
          (n : ℝ) ^ (-((1 : ℝ) / 2)) := by
      simp only [NativeCarryGeometry.Measure.nativeTowerAmplitude, if_pos hn]
      unfold NativeCarryGeometry.Measure.criticalAmplitude
        NativeCarryGeometry.Internal.Carry.Cp.criticalAmplitude
      rw [hcast]
      congr 1
      norm_num
    rw [nativeCarryRealPlaneSample,
      nativeCarryRealPlaneSampleAt,
      nativeCarryRealPlaneRadialDeformation]
    simp only [if_pos hn]
    rw [hamp]
  · simp [nativeCarryRealPlaneSample, nativeCarryRealPlaneSampleAt,
      nativeCarryRealPlaneRadialDeformation, hn]

@[simp] theorem nativeCarryRealPlaneSampleAt_of_pos
    (sigma t : ℝ) {n : ℤ} (hn : 0 < n) :
    nativeCarryRealPlaneSampleAt sigma t n =
      let amplitude := (n : ℝ) ^ (-sigma)
      let angle := -t * Real.log (n : ℝ)
      (amplitude * Real.cos angle, amplitude * Real.sin angle) := by
  simp [nativeCarryRealPlaneSampleAt,
    nativeCarryRealPlaneRadialDeformation, hn]

@[simp] theorem nativeCarryRealPlaneSampleAt_of_nonpos
    (sigma t : ℝ) {n : ℤ} (hn : n ≤ 0) :
    nativeCarryRealPlaneSampleAt sigma t n = 0 := by
  simp [nativeCarryRealPlaneSampleAt,
    nativeCarryRealPlaneRadialDeformation, not_lt.mpr hn]

/--
The quadratic energy of a positive sample is the square of its radial
amplitude and is independent of the real rotation time.
-/
theorem nativeCarryRealPlaneEnergy_sampleAt
    (sigma t : ℝ) {n : ℤ} (hn : 0 < n) :
    nativeCarryRealPlaneEnergy
        (nativeCarryRealPlaneSampleAt sigma t n) =
      (n : ℝ) ^ (-2 * sigma) := by
  have hnR : 0 ≤ (n : ℝ) := by
    exact_mod_cast (le_of_lt hn)
  rw [nativeCarryRealPlaneSampleAt_of_pos sigma t hn]
  unfold nativeCarryRealPlaneEnergy
  dsimp only
  let angle : ℝ := -t * Real.log (n : ℝ)
  calc
    (((n : ℝ) ^ (-sigma)) * Real.cos angle) ^ 2 +
          (((n : ℝ) ^ (-sigma)) * Real.sin angle) ^ 2 =
        (((n : ℝ) ^ (-sigma)) ^ 2) *
          (Real.cos angle ^ 2 + Real.sin angle ^ 2) := by
      ring
    _ = (((n : ℝ) ^ (-sigma)) ^ 2) := by
      rw [add_comm, Real.sin_sq_add_cos_sq, mul_one]
    _ = (n : ℝ) ^ (-2 * sigma) := by
      rw [← Real.rpow_mul_natCast hnR (-sigma) 2]
      congr 1
      ring

/--
The carry-built native sample has exactly inverse-integer energy.
-/
theorem nativeCarryRealPlaneEnergy_sample
    (t : ℝ) {n : ℤ} (hn : 0 < n) :
    nativeCarryRealPlaneEnergy (nativeCarryRealPlaneSample t n) =
      ((n : ℝ))⁻¹ := by
  rw [nativeCarryRealPlaneSample_eq_sampleAt_half,
    nativeCarryRealPlaneEnergy_sampleAt ((1 : ℝ) / 2) t hn]
  norm_num [Real.rpow_neg_one]

/--
An exponent belongs to the native real-vector domain when every positive
integer above the degenerate base `1` carries exactly the inverse quadratic
mass.
-/
def NativeCarryRealPlaneMassCompatible
    (sigma t : ℝ) : Prop :=
  ∀ n : ℤ, 1 < n →
    nativeCarryRealPlaneEnergy
        (nativeCarryRealPlaneSampleAt sigma t n) =
      ((n : ℝ))⁻¹

/--
The native real-vector domain has exactly one radial exponent.  The phase time
is arbitrary and does not participate in the rigidity.
-/
theorem nativeCarryRealPlaneMassCompatible_iff
    (sigma t : ℝ) :
    NativeCarryRealPlaneMassCompatible sigma t ↔
      sigma = (1 : ℝ) / 2 := by
  constructor
  · intro hcompatible
    have htwo := hcompatible 2 (by norm_num)
    rw [nativeCarryRealPlaneEnergy_sampleAt sigma t (by norm_num)] at htwo
    have hpow :
        (2 : ℝ) ^ (-2 * sigma) =
          (2 : ℝ) ^ (-1 : ℝ) := by
      simpa [Real.rpow_neg_one] using htwo
    have hexponent : -2 * sigma = (-1 : ℝ) :=
      (Real.rpow_right_inj (by norm_num) (by norm_num)).mp hpow
    linarith
  · intro hsigma
    subst sigma
    intro n hn
    rw [← nativeCarryRealPlaneSample_eq_sampleAt_half]
    exact nativeCarryRealPlaneEnergy_sample
      t (lt_trans (by norm_num) hn)

end
end NativeCarryGeometry.Internal.Analytic.Cp

namespace NativeCarryGeometry.Operator

noncomputable section

abbrev RealCarryPlane := ℝ × ℝ

abbrev quadraticEnergy (u : RealCarryPlane) : ℝ :=
  Internal.Analytic.Cp.nativeCarryRealPlaneEnergy u

abbrev rotationDirection (theta : ℝ) : RealCarryPlane :=
  Internal.Analytic.Cp.nativeCarryRealDirection theta

/-- The native state, already assembled from the carry-mass tower. -/
abbrev nativeRealCarryState
    (time : ℝ) (n : ℤ) : RealCarryPlane :=
  Internal.Analytic.Cp.nativeCarryRealPlaneSample time n

/-- A secondary radial deformation used to compare exponents. -/
abbrev radialDeformationState
    (sigma time : ℝ) (n : ℤ) : RealCarryPlane :=
  Internal.Analytic.Cp.nativeCarryRealPlaneSampleAt sigma time n

/-- Compatibility alias: this name denotes the radial deformation family. -/
abbrev realCarryState
    (sigma time : ℝ) (n : ℤ) : RealCarryPlane :=
  radialDeformationState sigma time n

/-- Compatibility alias for the carry-built native state. -/
abbrev criticalRealCarryState
    (time : ℝ) (n : ℤ) : RealCarryPlane :=
  nativeRealCarryState time n

/-- The deformation represents the native carry mass exactly. -/
abbrev RadialDeformationRepresentsNativeMass
    (sigma time : ℝ) : Prop :=
  Internal.Analytic.Cp.NativeCarryRealPlaneMassCompatible sigma time

/-- Compatibility alias for radial-presentation mass compatibility. -/
abbrev RealCarryEnergyCompatible
    (sigma time : ℝ) : Prop :=
  RadialDeformationRepresentsNativeMass sigma time

/-- NCG-REA-001: Real Rotation Unit-Energy Theorem. -/
@[simp] theorem quadraticEnergy_rotationDirection (theta : ℝ) :
    quadraticEnergy (rotationDirection theta) = 1 :=
  Internal.Analytic.Cp.nativeCarryRealPlaneEnergy_direction theta

/-- NCG-REA-002: Radial-Deformation Energy Invariance. -/
theorem quadraticEnergy_realCarryState
    (sigma time : ℝ) {n : ℤ} (hn : 0 < n) :
    quadraticEnergy (realCarryState sigma time n) =
      (n : ℝ) ^ (-2 * sigma) :=
  Internal.Analytic.Cp.nativeCarryRealPlaneEnergy_sampleAt
    sigma time hn

/-- NCG-REA-004: Native State Inverse-Mass Energy.

The native state carries inverse-integer energy by construction. -/
theorem quadraticEnergy_nativeRealCarryState
    (time : ℝ) {n : ℤ} (hn : 0 < n) :
    quadraticEnergy (nativeRealCarryState time n) =
      ((n : ℝ))⁻¹ :=
  Internal.Analytic.Cp.nativeCarryRealPlaneEnergy_sample time hn

/-- NCG-REA-003: Radial-Deformation Mass Rigidity. -/
theorem realCarryEnergyCompatible_iff
    (sigma time : ℝ) :
    RealCarryEnergyCompatible sigma time ↔
      sigma = (1 : ℝ) / 2 :=
  Internal.Analytic.Cp.nativeCarryRealPlaneMassCompatible_iff
    sigma time

end
end NativeCarryGeometry.Operator
