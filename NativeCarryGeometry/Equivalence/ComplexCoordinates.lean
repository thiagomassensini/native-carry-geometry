import NativeCarryGeometry.Operator.FiniteRealOperator
import NativeCarryGeometry.Analytic.FiniteBracketChart
import Mathlib.Data.Complex.Basic

/-!
# Optional complex packaging of the native real-plane camera

The primitive camera, its quadratic energy, and its zero predicate were defined
in `CpNativeCarryRealPlaneBracket` using only real pairs and additive centered
differences.

This module proves that storing a real pair `(x,y)` in the two fields of a
complex number is an injective additive encoding.  The encoding commutes with
every finite saturated camera, preserves quadratic energy through `normSq`, and
therefore preserves zeros exactly.

The historical additive homomorphism is retained internally because the exact
real-to-analytic boundary proof consumes it.  The public API below strengthens
that coordinate container to an additive equivalence.
-/

namespace NativeCarryGeometry.Internal.Analytic.Cp

noncomputable section

/-- Store a real-plane vector in the real and imaginary coordinate fields. -/
def nativeCarryRealPlaneComplexPackaging :
    NativeCarryRealPlane →+ ℂ where
  toFun u := ⟨u.1, u.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem nativeCarryRealPlaneComplexPackaging_re
    (u : NativeCarryRealPlane) :
    (nativeCarryRealPlaneComplexPackaging u).re = u.1 := rfl

@[simp] theorem nativeCarryRealPlaneComplexPackaging_im
    (u : NativeCarryRealPlane) :
    (nativeCarryRealPlaneComplexPackaging u).im = u.2 := rfl

/-- The coordinate packaging is injective. -/
theorem nativeCarryRealPlaneComplexPackaging_injective :
    Function.Injective nativeCarryRealPlaneComplexPackaging := by
  intro u v huv
  apply Prod.ext
  · exact congrArg Complex.re huv
  · exact congrArg Complex.im huv

/-- Complex squared norm is exactly the previously defined real energy. -/
@[simp] theorem normSq_nativeCarryRealPlaneComplexPackaging
    (u : NativeCarryRealPlane) :
    Complex.normSq (nativeCarryRealPlaneComplexPackaging u) =
      nativeCarryRealPlaneEnergy u := by
  simp [Complex.normSq, nativeCarryRealPlaneComplexPackaging,
    nativeCarryRealPlaneEnergy, pow_two]

/--
Packaging commutes with the whole finite real camera.  This is a direct
instance of the additive naturality theorem; no analytic identity is involved.
-/
theorem nativeCarryRealPlaneComplexPackaging_finiteChartAt
    (p M : ℕ) (sigma t : ℝ) :
    nativeCarryRealPlaneComplexPackaging
        (nativeCarryRealPlaneFiniteChartAt p M sigma t) =
      nativeCarryFiniteSaturatedChart p M
        (fun n =>
          nativeCarryRealPlaneComplexPackaging
            (nativeCarryRealPlaneSampleAt sigma t n)) := by
  exact map_nativeCarryFiniteSaturatedChart
    nativeCarryRealPlaneComplexPackaging p M
    (nativeCarryRealPlaneSampleAt sigma t)

/--
For every camera width, prime or composite, packaging preserves the zero
predicate of an arbitrary real-plane input field.
-/
theorem nativeCarryFiniteSaturatedChart_zero_iff_packaged_zero
    (p M : ℕ) (f : ℤ → NativeCarryRealPlane) :
    nativeCarryFiniteSaturatedChart p M f = 0 ↔
      nativeCarryFiniteSaturatedChart p M
        (fun n => nativeCarryRealPlaneComplexPackaging (f n)) = 0 := by
  constructor
  · intro hreal
    have hpack :=
      map_nativeCarryFiniteSaturatedChart
        nativeCarryRealPlaneComplexPackaging p M f
    rw [hreal] at hpack
    simpa using hpack.symm
  · intro hpackaged
    apply nativeCarryRealPlaneComplexPackaging_injective
    rw [map_zero]
    calc
      nativeCarryRealPlaneComplexPackaging
          (nativeCarryFiniteSaturatedChart p M f) =
          nativeCarryFiniteSaturatedChart p M
            (fun n => nativeCarryRealPlaneComplexPackaging (f n)) :=
        map_nativeCarryFiniteSaturatedChart
          nativeCarryRealPlaneComplexPackaging p M f
      _ = 0 := hpackaged

/--
For every camera width, packaging also preserves the quadratic energy of the
resultant.
-/
theorem normSq_packaged_nativeCarryFiniteSaturatedChart
    (p M : ℕ) (f : ℤ → NativeCarryRealPlane) :
    Complex.normSq
        (nativeCarryFiniteSaturatedChart p M
          (fun n => nativeCarryRealPlaneComplexPackaging (f n))) =
      nativeCarryRealPlaneEnergy
        (nativeCarryFiniteSaturatedChart p M f) := by
  rw [← map_nativeCarryFiniteSaturatedChart
    nativeCarryRealPlaneComplexPackaging p M f]
  exact normSq_nativeCarryRealPlaneComplexPackaging _

/--
For an odd prime camera, the packaged real resultant is literally the generic
finite Genuine chart evaluated on the packaged real samples.
-/
theorem nativeCarryRealPlaneComplexPackaging_eq_finiteChart
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (sigma t : ℝ) :
    nativeCarryRealPlaneComplexPackaging
        (nativeCarryRealPlaneFiniteChartAt p M sigma t) =
      NativeCarryGeometry.Internal.Genuine.Cp.finiteChart p M
        (fun n =>
          nativeCarryRealPlaneComplexPackaging
            (nativeCarryRealPlaneSampleAt sigma t n)) := by
  calc
    nativeCarryRealPlaneComplexPackaging
          (nativeCarryRealPlaneFiniteChartAt p M sigma t) =
        nativeCarryFiniteSaturatedChart p M
          (fun n =>
            nativeCarryRealPlaneComplexPackaging
              (nativeCarryRealPlaneSampleAt sigma t n)) :=
      nativeCarryRealPlaneComplexPackaging_finiteChartAt
        p M sigma t
    _ = NativeCarryGeometry.Internal.Genuine.Cp.finiteChart p M
          (fun n =>
            nativeCarryRealPlaneComplexPackaging
              (nativeCarryRealPlaneSampleAt sigma t n)) :=
      nativeCarryFiniteSaturatedChart_eq_finiteChart
        p M hp hpodd _

/--
The real camera and its packaged finite Genuine chart have exactly the same
zero predicate.
-/
theorem nativeCarryRealPlaneFiniteChartAt_zero_iff_packaged_zero
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (sigma t : ℝ) :
    nativeCarryRealPlaneFiniteChartAt p M sigma t = 0 ↔
      NativeCarryGeometry.Internal.Genuine.Cp.finiteChart p M
        (fun n =>
          nativeCarryRealPlaneComplexPackaging
            (nativeCarryRealPlaneSampleAt sigma t n)) = 0 := by
  constructor
  · intro hreal
    have hpack :=
      nativeCarryRealPlaneComplexPackaging_eq_finiteChart
        p M hp hpodd sigma t
    rw [hreal] at hpack
    simpa using hpack.symm
  · intro hpackaged
    apply nativeCarryRealPlaneComplexPackaging_injective
    rw [map_zero]
    calc
      nativeCarryRealPlaneComplexPackaging
          (nativeCarryRealPlaneFiniteChartAt p M sigma t) =
          NativeCarryGeometry.Internal.Genuine.Cp.finiteChart p M
            (fun n =>
              nativeCarryRealPlaneComplexPackaging
                (nativeCarryRealPlaneSampleAt sigma t n)) :=
        nativeCarryRealPlaneComplexPackaging_eq_finiteChart
          p M hp hpodd sigma t
      _ = 0 := hpackaged

/--
Packaging preserves the visible energy of the whole camera resultant.
-/
theorem normSq_packaged_finiteChart_eq_realEnergy
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (sigma t : ℝ) :
    Complex.normSq
        (NativeCarryGeometry.Internal.Genuine.Cp.finiteChart p M
          (fun n =>
            nativeCarryRealPlaneComplexPackaging
              (nativeCarryRealPlaneSampleAt sigma t n))) =
      nativeCarryRealPlaneEnergy
        (nativeCarryRealPlaneFiniteChartAt p M sigma t) := by
  rw [← nativeCarryRealPlaneComplexPackaging_eq_finiteChart
    p M hp hpodd sigma t]
  exact normSq_nativeCarryRealPlaneComplexPackaging _

end

end NativeCarryGeometry.Internal.Analytic.Cp

namespace NativeCarryGeometry.Equivalence

noncomputable section

/-- Additive coordinate equivalence `(x,y) ↔ x + iy`. -/
def complexCoordinates : Operator.RealCarryPlane ≃+ ℂ where
  toFun u := ⟨u.1, u.2⟩
  invFun z := (z.re, z.im)
  left_inv _ := rfl
  right_inv _ := by
    apply Complex.ext
    · rfl
    · rfl
  map_add' _ _ := rfl

@[simp] private theorem complexCoordinates_re
    (u : Operator.RealCarryPlane) :
    (complexCoordinates u).re = u.1 := rfl

@[simp] private theorem complexCoordinates_im
    (u : Operator.RealCarryPlane) :
    (complexCoordinates u).im = u.2 := rfl

/-- NCG-EQV-001: Faithful Complex Coordinate Encoding. -/
theorem complexCoordinates_injective :
    Function.Injective complexCoordinates :=
  complexCoordinates.injective

/-- NCG-EQV-002: Energy Preservation under Encoding. -/
@[simp] theorem normSq_complexCoordinates
    (u : Operator.RealCarryPlane) :
    Complex.normSq (complexCoordinates u) =
      Operator.quadraticEnergy u := by
  simp [Complex.normSq, complexCoordinates,
    Operator.quadraticEnergy,
    NativeCarryGeometry.Internal.Analytic.Cp.nativeCarryRealPlaneEnergy,
    pow_two]

/-- NCG-EQV-003: Finite-Operator Naturality. -/
theorem complexCoordinates_finiteOperator
    (camera cutoff : ℕ) (sigma time : ℝ) :
    complexCoordinates
        (Operator.finiteRealCarryOperator
          camera cutoff sigma time) =
      Operator.finiteSaturatedBracketOperator camera cutoff
        (fun n => complexCoordinates
          (Operator.realCarryState sigma time n)) := by
  exact Operator.map_finiteSaturatedBracketOperator
    complexCoordinates.toAddMonoidHom camera cutoff
    (Operator.realCarryState sigma time)

/-- NCG-EQV-004: Finite Zero-Set Equivalence. -/
theorem finiteOperator_eq_zero_iff_complexCoordinates_eq_zero
    (camera cutoff : ℕ) (sigma time : ℝ) :
    Operator.finiteRealCarryOperator
        camera cutoff sigma time = 0 ↔
      complexCoordinates
        (Operator.finiteRealCarryOperator
          camera cutoff sigma time) = 0 := by
  constructor
  · intro hzero
    simp [hzero]
  · intro hzero
    apply complexCoordinates_injective
    simpa using hzero

end
end NativeCarryGeometry.Equivalence
