import NativeCarryGeometry.Bracket.BalancedCamera
import NativeCarryGeometry.Operator.RealState
import Mathlib.Tactic

open scoped BigOperators

namespace NativeCarryGeometry.Internal.Analytic.Cp

noncomputable section

def nativeCarryFiniteSaturatedChart
    {A : Type*} [AddCommGroup A]
    (p M : ℕ) (f : ℤ → A) : A :=
  (∑ n ∈ Finset.Icc (1 : ℤ)
      (NativeCarryGeometry.Internal.Genuine.Cp.halfRange p : ℤ), f n) +
    ∑ k ∈ Finset.range M,
      NativeCarryGeometry.Internal.saturatedBracket
        (NativeCarryGeometry.Internal.Genuine.Cp.halfRange p) f
        (NativeCarryGeometry.Internal.Genuine.Cp.alignedCenter p k)

/-- Additive maps commute exactly with the finite saturated camera. -/
theorem map_nativeCarryFiniteSaturatedChart
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (g : A →+ B) (p M : ℕ) (f : ℤ → A) :
    g (nativeCarryFiniteSaturatedChart p M f) =
      nativeCarryFiniteSaturatedChart p M (fun n => g (f n)) := by
  classical
  simp [nativeCarryFiniteSaturatedChart, NativeCarryGeometry.Internal.saturatedBracket,
    NativeCarryGeometry.Internal.centeredSecondDifference]

/--
For an odd prime camera, the additive saturated camera is literally the
legacy finite balanced-bracket chart.  Primality is used only for the identification
of the balanced-offset presentation with the symmetric radii presentation.
-/
theorem nativeCarryFiniteSaturatedChart_eq_finiteChart
    {R : Type*} [CommRing R]
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (f : ℤ → R) :
    nativeCarryFiniteSaturatedChart p M f =
      NativeCarryGeometry.Internal.Genuine.Cp.finiteChart p M f := by
  classical
  unfold nativeCarryFiniteSaturatedChart
    NativeCarryGeometry.Internal.Genuine.Cp.finiteChart
    NativeCarryGeometry.Internal.Genuine.Cp.seedSum
  simp_rw [
    NativeCarryGeometry.Internal.Genuine.Cp.bracket_eq_saturatedBracket
      p hp hpodd]
def nativeCarryRealPlaneFiniteChartAt
    (p M : ℕ) (sigma t : ℝ) : NativeCarryRealPlane :=
  nativeCarryFiniteSaturatedChart p M
    (nativeCarryRealPlaneSampleAt sigma t)

/-- Finite primitive camera, entirely valued in the real plane. -/
def nativeCarryRealPlaneFiniteChart
    (p M : ℕ) (t : ℝ) : NativeCarryRealPlane :=
  nativeCarryFiniteSaturatedChart p M
    (nativeCarryRealPlaneSample t)

/-- The native finite chart is the half-exponent radial chart, extensionally. -/
theorem nativeCarryRealPlaneFiniteChart_eq_chartAt_half
    (p M : ℕ) (t : ℝ) :
    nativeCarryRealPlaneFiniteChart p M t =
      nativeCarryRealPlaneFiniteChartAt p M ((1 : ℝ) / 2) t := by
  unfold nativeCarryRealPlaneFiniteChart
    nativeCarryRealPlaneFiniteChartAt
  apply congrArg (nativeCarryFiniteSaturatedChart p M)
  funext n
  exact nativeCarryRealPlaneSample_eq_sampleAt_half t n

/--
For an odd prime width, the real primitive camera is the existing generic
legacy balanced-bracket chart instantiated in the real product ring.
-/
theorem nativeCarryRealPlaneFiniteChart_eq_finiteChart
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (t : ℝ) :
    nativeCarryRealPlaneFiniteChart p M t =
      NativeCarryGeometry.Internal.Genuine.Cp.finiteChart p M
        (nativeCarryRealPlaneSample t) := by
  unfold nativeCarryRealPlaneFiniteChart
  exact nativeCarryFiniteSaturatedChart_eq_finiteChart
    p M hp hpodd (nativeCarryRealPlaneSample t)

/-- Euclidean energy is nonnegative. -/
theorem nativeCarryRealPlaneEnergy_nonneg
    (u : NativeCarryRealPlane) :
    0 ≤ nativeCarryRealPlaneEnergy u := by
  exact add_nonneg (sq_nonneg u.1) (sq_nonneg u.2)

/-- Euclidean energy detects the zero vector exactly. -/
theorem nativeCarryRealPlaneEnergy_eq_zero_iff
    (u : NativeCarryRealPlane) :
    nativeCarryRealPlaneEnergy u = 0 ↔ u = 0 := by
  rcases u with ⟨x, y⟩
  change x ^ 2 + y ^ 2 = 0 ↔ (x, y) = (0, 0)
  constructor
  · intro h
    have hx2 : x ^ 2 = 0 := by
      nlinarith [sq_nonneg y]
    have hy2 : y ^ 2 = 0 := by
      nlinarith [sq_nonneg x]
    have hx : x = 0 := by
      have hxmul : x * x = 0 := by simpa [pow_two] using hx2
      rcases mul_eq_zero.mp hxmul with hx | hx
      · exact hx
      · exact hx
    have hy : y = 0 := by
      have hymul : y * y = 0 := by simpa [pow_two] using hy2
      rcases mul_eq_zero.mp hymul with hy | hy
      · exact hy
      · exact hy
    rw [hx, hy]
  · intro h
    have hx : x = 0 := congrArg Prod.fst h
    have hy : y = 0 := congrArg Prod.snd h
    rw [hx, hy]
    norm_num

/--
The primitive scanner's raw visible energy vanishes exactly when its real
resultant vanishes.  No scalar outside the real plane is needed to state or
detect the resultant's zero locus.
-/
theorem nativeCarryRealPlaneFiniteChart_energy_eq_zero_iff
    (p M : ℕ) (t : ℝ) :
    nativeCarryRealPlaneEnergy
        (nativeCarryRealPlaneFiniteChart p M t) = 0 ↔
      nativeCarryRealPlaneFiniteChart p M t = 0 :=
  nativeCarryRealPlaneEnergy_eq_zero_iff _

/--
An ambient radial chart represents a point of the finite native zero locus when it preserves the
upstream carry mass and its bracket resultant vanishes.  This is a chart
representation predicate, not a separate finite operator-zero predicate.
-/
def RadialChartRepresentsFiniteNativeZero
    (p M : ℕ) (sigma t : ℝ) : Prop :=
  NativeCarryRealPlaneMassCompatible sigma t ∧
    nativeCarryRealPlaneEnergy
      (nativeCarryRealPlaneFiniteChartAt p M sigma t) = 0

/-- Legacy compatibility alias for the radial-chart representation predicate. -/
abbrev NativeCarryRealPlaneAdmissibleFiniteZero
    (p M : ℕ) (sigma t : ℝ) : Prop :=
  RadialChartRepresentsFiniteNativeZero p M sigma t

/--
Exact radial-chart factorization: a finite deformation presents a point of the
native zero locus exactly at the half exponent and at a zero of the mass-built
native camera.
The carry mass was fixed before either camera was evaluated.
-/
theorem nativeCarryRealPlaneAdmissibleFiniteZero_iff
    (p M : ℕ) (sigma t : ℝ) :
    NativeCarryRealPlaneAdmissibleFiniteZero p M sigma t ↔
      sigma = (1 : ℝ) / 2 ∧
        nativeCarryRealPlaneEnergy
          (nativeCarryRealPlaneFiniteChart p M t) = 0 := by
  constructor
  · rintro ⟨hcompatible, hzero⟩
    have hsigma :=
      (nativeCarryRealPlaneMassCompatible_iff sigma t).1 hcompatible
    subst sigma
    rw [← nativeCarryRealPlaneFiniteChart_eq_chartAt_half] at hzero
    exact ⟨rfl, hzero⟩
  · rintro ⟨hsigma, hzero⟩
    subst sigma
    rw [nativeCarryRealPlaneFiniteChart_eq_chartAt_half] at hzero
    exact ⟨
      (nativeCarryRealPlaneMassCompatible_iff ((1 : ℝ) / 2) t).2 rfl,
      hzero⟩

end
end NativeCarryGeometry.Internal.Analytic.Cp

namespace NativeCarryGeometry.Operator

noncomputable section

abbrev finiteSaturatedBracketOperator
    {A : Type*} [AddCommGroup A]
    (camera cutoff : ℕ) (f : ℤ → A) : A :=
  Internal.Analytic.Cp.nativeCarryFiniteSaturatedChart
    camera cutoff f

/-- Native finite operator, already assembled from the carry-mass state. -/
abbrev finiteNativeRealCarryOperator
    (camera cutoff : ℕ) (time : ℝ) : RealCarryPlane :=
  Internal.Analytic.Cp.nativeCarryRealPlaneFiniteChart
    camera cutoff time

/-- Finite camera applied to the ambient radial-deformation state; at one half it equals the native finite operator. -/
abbrev finiteRadialDeformation
    (camera cutoff : ℕ) (sigma time : ℝ) : RealCarryPlane :=
  Internal.Analytic.Cp.nativeCarryRealPlaneFiniteChartAt
    camera cutoff sigma time

/-- Compatibility alias: this is the radial deformation family. -/
abbrev finiteRealCarryOperator
    (camera cutoff : ℕ) (sigma time : ℝ) : RealCarryPlane :=
  finiteRadialDeformation camera cutoff sigma time

/-- Compatibility alias for the native finite operator. -/
abbrev criticalFiniteRealCarryOperator
    (camera cutoff : ℕ) (time : ℝ) : RealCarryPlane :=
  finiteNativeRealCarryOperator camera cutoff time

abbrev visibleEnergy (u : RealCarryPlane) : ℝ :=
  quadraticEnergy u

/-- NCG-OPR-001: Additive Naturality of the Finite Operator. -/
theorem map_finiteSaturatedBracketOperator
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (g : A →+ B) (camera cutoff : ℕ) (f : ℤ → A) :
    g (finiteSaturatedBracketOperator camera cutoff f) =
      finiteSaturatedBracketOperator camera cutoff
        (fun n => g (f n)) :=
  Internal.Analytic.Cp.map_nativeCarryFiniteSaturatedChart
    g camera cutoff f

/-- NCG-OPR-002: Faithfulness of Visible Energy. -/
theorem quadraticEnergy_eq_zero_iff
    (u : RealCarryPlane) :
    quadraticEnergy u = 0 ↔ u = 0 :=
  Internal.Analytic.Cp.nativeCarryRealPlaneEnergy_eq_zero_iff u

/--
Canonical finite operator-zero predicate for the already weighted native
operator.
-/
abbrev IsFiniteNativeCarryOperatorZero
    (camera cutoff : ℕ) (time : ℝ) : Prop :=
  quadraticEnergy
      (finiteNativeRealCarryOperator camera cutoff time) = 0

/--
Legacy coordinate-labelled alias for the same finite native operator-zero
predicate.
-/
abbrev IsFiniteNativeRealCarryOperatorZero
    (camera cutoff : ℕ) (time : ℝ) : Prop :=
  IsFiniteNativeCarryOperatorZero camera cutoff time

/--
The ambient radial chart represents a point of the finite native zero locus.
-/
abbrev RadialChartRepresentsFiniteNativeZero
    (camera cutoff : ℕ) (sigma time : ℝ) : Prop :=
  Internal.Analytic.Cp.RadialChartRepresentsFiniteNativeZero
    camera cutoff sigma time

/--
Legacy compatibility alias; this is a representation predicate, not another
operator-zero definition.
-/
abbrev IsFiniteRealCarryOperatorZero
    (camera cutoff : ℕ) (sigma time : ℝ) : Prop :=
  RadialChartRepresentsFiniteNativeZero camera cutoff sigma time

/-- NCG-OPR-003: Legacy Finite Radial-Chart Native-Representation Factorization. -/
theorem isFiniteRealCarryOperatorZero_iff
    (camera cutoff : ℕ) (sigma time : ℝ) :
    IsFiniteRealCarryOperatorZero camera cutoff sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        quadraticEnergy
          (criticalFiniteRealCarryOperator camera cutoff time) = 0 :=
  Internal.Analytic.Cp.nativeCarryRealPlaneAdmissibleFiniteZero_iff
    camera cutoff sigma time

/--
NCG-OPR-008: Canonical Finite Radial-Chart Representation Factorization.
-/
theorem radialChartRepresentsFiniteNativeZero_iff
    (camera cutoff : ℕ) (sigma time : ℝ) :
    RadialChartRepresentsFiniteNativeZero camera cutoff sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsFiniteNativeCarryOperatorZero camera cutoff time := by
  simpa [RadialChartRepresentsFiniteNativeZero,
    IsFiniteNativeCarryOperatorZero,
    criticalFiniteRealCarryOperator] using
    (isFiniteRealCarryOperatorZero_iff
      camera cutoff sigma time)

end
end NativeCarryGeometry.Operator
