import NativeCarryGeometry.Analytic.CanonicalContinuation
import NativeCarryGeometry.Operator.ZeroSetFactorization
import NativeCarryGeometry.Equivalence.ComplexCoordinates

/-!
# Genuine zero to the primitive real boundary

This module connects the scalar Genuine chart to the primitive camera before
any quadratic-domain conclusion is used.

For `s = sigma + time * I`, the complex packaging of the real rotating sample
at `(sigma,time)` is exactly the Dirichlet monomial `n^(-s)`.  Additive
naturality then identifies every finite primitive resultant with the finite
Genuine chart.  Passing to the limit proves that every Genuine zero in the
open strip closes the raw primitive real boundary.

No external classical identification, Green relation, or Cayley transform
occurs in this crosswalk.  The native specialization below restricts the
ambient radial chart to the carry-built tower; the registered conjunction is
retained only as a compatibility theorem for arbitrary radial parameters.
-/

open scoped BigOperators Topology

namespace NativeCarryGeometry.Internal.Analytic.Cp

open Filter

noncomputable section

/-- The parameter with real radial exponent `sigma` and real phase time
`time`. -/
def nativeCarryRealPlaneParameter (sigma time : ℝ) : ℂ :=
  ⟨sigma, time⟩

@[simp] theorem nativeCarryRealPlaneParameter_re (sigma time : ℝ) :
    (nativeCarryRealPlaneParameter sigma time).re = sigma := rfl

@[simp] theorem nativeCarryRealPlaneParameter_im (sigma time : ℝ) :
    (nativeCarryRealPlaneParameter sigma time).im = time := rfl

/-- Packaging the primitive real sample does not change the Dirichlet
monomial; it only stores its two real coordinates in `ℂ`. -/
theorem nativeCarryRealPlaneComplexPackaging_sampleAt_eq_dirichletTerm
    (sigma time : ℝ) {n : ℤ} (hn : 0 < n) :
    nativeCarryRealPlaneComplexPackaging
        (nativeCarryRealPlaneSampleAt sigma time n) =
      dirichletTerm (nativeCarryRealPlaneParameter sigma time) n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hn)
  have hlog :
      Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) :=
    (Complex.ofReal_log hnR.le).symm
  rw [nativeCarryRealPlaneSampleAt_of_pos sigma time hn]
  unfold dirichletTerm nativeCarryRealPlaneParameter
  rw [Complex.cpow_def_of_ne_zero hnC, hlog]
  apply Complex.ext
  · rw [nativeCarryRealPlaneComplexPackaging_re, Complex.exp_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, Complex.neg_im, zero_mul,
      add_zero, sub_zero]
    rw [← Real.rpow_def_of_pos hnR]
    congr 1
    ring_nf
  · rw [nativeCarryRealPlaneComplexPackaging_im, Complex.exp_im]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, Complex.neg_im, zero_mul,
      add_zero, sub_zero]
    rw [← Real.rpow_def_of_pos hnR]
    congr 1
    ring_nf

/-- The packaged finite primitive resultant is the finite Dirichlet Genuine
chart at the same `(sigma,time)` parameter. -/
theorem nativeCarryRealPlaneComplexPackaging_finiteChartAt_eq_dirichlet
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (sigma time : ℝ) :
    nativeCarryRealPlaneComplexPackaging
        (nativeCarryRealPlaneFiniteChartAt p M sigma time) =
      NativeCarryGeometry.Internal.Genuine.Cp.finiteChart p M
        (dirichletTerm (nativeCarryRealPlaneParameter sigma time)) := by
  calc
    nativeCarryRealPlaneComplexPackaging
          (nativeCarryRealPlaneFiniteChartAt p M sigma time) =
        NativeCarryGeometry.Internal.Genuine.Cp.finiteChart p M
          (fun n =>
            nativeCarryRealPlaneComplexPackaging
              (nativeCarryRealPlaneSampleAt sigma time n)) :=
      nativeCarryRealPlaneComplexPackaging_eq_finiteChart
        p M hp hpodd sigma time
    _ = NativeCarryGeometry.Internal.Genuine.Cp.finiteChart p M
          (dirichletTerm
            (nativeCarryRealPlaneParameter sigma time)) := by
      rw [
        NativeCarryGeometry.Internal.Genuine.Cp.finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum
          p hp hpodd,
        NativeCarryGeometry.Internal.Genuine.Cp.finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum
          p hp hpodd]
      have hprefix :
          (∑ n ∈ Finset.Icc (1 : ℤ)
              ((p : ℤ) * (M : ℤ) +
                (NativeCarryGeometry.Internal.Genuine.Cp.halfRange p : ℤ)),
              nativeCarryRealPlaneComplexPackaging
                (nativeCarryRealPlaneSampleAt sigma time n)) =
            ∑ n ∈ Finset.Icc (1 : ℤ)
              ((p : ℤ) * (M : ℤ) +
                (NativeCarryGeometry.Internal.Genuine.Cp.halfRange p : ℤ)),
              dirichletTerm
                (nativeCarryRealPlaneParameter sigma time) n := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnpos : 0 < n := by
          have hnleft := (Finset.mem_Icc.mp hn).1
          omega
        exact
          nativeCarryRealPlaneComplexPackaging_sampleAt_eq_dirichletTerm
            sigma time hnpos
      have hcenters :
          (∑ k ∈ Finset.range M,
              nativeCarryRealPlaneComplexPackaging
                (nativeCarryRealPlaneSampleAt sigma time
                  (NativeCarryGeometry.Internal.Genuine.Cp.alignedCenter p k))) =
            ∑ k ∈ Finset.range M,
              dirichletTerm
                (nativeCarryRealPlaneParameter sigma time)
                (NativeCarryGeometry.Internal.Genuine.Cp.alignedCenter p k) := by
        apply Finset.sum_congr rfl
        intro k _hk
        apply
          nativeCarryRealPlaneComplexPackaging_sampleAt_eq_dirichletTerm
        unfold NativeCarryGeometry.Internal.Genuine.Cp.alignedCenter
        have hpZ : (0 : ℤ) < (p : ℤ) := by
          exact_mod_cast hp.pos
        have hkZ : (0 : ℤ) < ((k + 1 : ℕ) : ℤ) := by
          exact_mod_cast Nat.succ_pos k
        exact mul_pos hpZ hkZ
      rw [hprefix, hcenters]

/-- A Genuine zero closes the raw primitive real camera at the same radial
and phase coordinates. -/
theorem genuineContinuation_zero_to_nativeCarryRealBoundaryClosure
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    NativeCarryGeometry.Operator.BoundaryConvergesToZero 3 s.re s.im := by
  have hhalf : -1 < s.re := by
    linarith [hs.1]
  have hcomplex :
      Tendsto
        (fun M : ℕ =>
          NativeCarryGeometry.Internal.Genuine.Cp.finiteChart 3 M (dirichletTerm s))
        atTop (nhds 0) := by
    have hlimit :=
      finiteChart_dirichlet_tendsto_bracketedDirichletChart
        3 (by norm_num) (by norm_num) hhalf
    have hchart :
        bracketedDirichletChart 3 s = 0 :=
      (bracketedDirichletChart_zero_iff_genuineContinuation_zero
        3 (by norm_num) (by norm_num) hs).2 hzero
    simpa [hchart] using hlimit
  have hpackaged :
      Tendsto
        (fun M : ℕ =>
          nativeCarryRealPlaneComplexPackaging
            (nativeCarryRealPlaneFiniteChartAt 3 M s.re s.im))
        atTop (nhds 0) := by
    have hfinite :
        (fun M : ℕ =>
          nativeCarryRealPlaneComplexPackaging
            (nativeCarryRealPlaneFiniteChartAt 3 M s.re s.im)) =
          (fun M : ℕ =>
            NativeCarryGeometry.Internal.Genuine.Cp.finiteChart 3 M (dirichletTerm s)) := by
      funext M
      simpa [nativeCarryRealPlaneParameter] using
        (nativeCarryRealPlaneComplexPackaging_finiteChartAt_eq_dirichlet
          3 M (by norm_num) (by norm_num) s.re s.im)
    rw [hfinite]
    exact hcomplex
  have hre :
      Tendsto
        (fun M : ℕ =>
          (nativeCarryRealPlaneFiniteChartAt 3 M s.re s.im).1)
        atTop (nhds 0) := by
    have h :=
      Complex.continuous_re.continuousAt.tendsto.comp hpackaged
    change
      Tendsto
        (fun M : ℕ =>
          (nativeCarryRealPlaneComplexPackaging
            (nativeCarryRealPlaneFiniteChartAt 3 M s.re s.im)).re)
        atTop (nhds 0) at h
    simpa only [nativeCarryRealPlaneComplexPackaging_re] using h
  have him :
      Tendsto
        (fun M : ℕ =>
          (nativeCarryRealPlaneFiniteChartAt 3 M s.re s.im).2)
        atTop (nhds 0) := by
    have h :=
      Complex.continuous_im.continuousAt.tendsto.comp hpackaged
    change
      Tendsto
        (fun M : ℕ =>
          (nativeCarryRealPlaneComplexPackaging
            (nativeCarryRealPlaneFiniteChartAt 3 M s.re s.im)).im)
        atTop (nhds 0) at h
    simpa only [nativeCarryRealPlaneComplexPackaging_im] using h
  unfold NativeCarryGeometry.Operator.BoundaryConvergesToZero
  exact hre.prodMk_nhds him

/-- Conversely, a closing primitive real boundary packages to a closing
Dirichlet chart and therefore is a Genuine zero. -/
theorem nativeCarryRealBoundaryClosure_to_genuineContinuation_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hclose :
      NativeCarryGeometry.Operator.BoundaryConvergesToZero 3 s.re s.im) :
    genuineContinuation s = 0 := by
  have hre :
      Tendsto
        (fun M : ℕ =>
          (nativeCarryRealPlaneFiniteChartAt 3 M s.re s.im).1)
        atTop (nhds 0) := by
    exact continuous_fst.continuousAt.tendsto.comp hclose
  have him :
      Tendsto
        (fun M : ℕ =>
          (nativeCarryRealPlaneFiniteChartAt 3 M s.re s.im).2)
        atTop (nhds 0) := by
    exact continuous_snd.continuousAt.tendsto.comp hclose
  have hpackaged :
      Tendsto
        (fun M : ℕ =>
          nativeCarryRealPlaneComplexPackaging
            (nativeCarryRealPlaneFiniteChartAt 3 M s.re s.im))
        atTop (nhds 0) := by
    have hcomplex := hre.ofReal.add (him.ofReal.mul_const Complex.I)
    have hfun :
        (fun M : ℕ =>
          nativeCarryRealPlaneComplexPackaging
            (nativeCarryRealPlaneFiniteChartAt 3 M s.re s.im)) =
          (fun M : ℕ =>
            ((nativeCarryRealPlaneFiniteChartAt 3 M s.re s.im).1 : ℂ) +
              ((nativeCarryRealPlaneFiniteChartAt 3 M s.re s.im).2 : ℂ) *
                Complex.I) := by
      funext M
      apply Complex.ext <;>
        simp [nativeCarryRealPlaneComplexPackaging]
    rw [hfun]
    simpa using hcomplex
  have hdirichlet :
      Tendsto
        (fun M : ℕ =>
          NativeCarryGeometry.Internal.Genuine.Cp.finiteChart 3 M (dirichletTerm s))
        atTop (nhds 0) := by
    have hfinite :
        (fun M : ℕ =>
          nativeCarryRealPlaneComplexPackaging
            (nativeCarryRealPlaneFiniteChartAt 3 M s.re s.im)) =
          (fun M : ℕ =>
            NativeCarryGeometry.Internal.Genuine.Cp.finiteChart 3 M (dirichletTerm s)) := by
      funext M
      simpa [nativeCarryRealPlaneParameter] using
        (nativeCarryRealPlaneComplexPackaging_finiteChartAt_eq_dirichlet
          3 M (by norm_num) (by norm_num) s.re s.im)
    rw [← hfinite]
    exact hpackaged
  have hhalf : -1 < s.re := by
    linarith [hs.1]
  have hlimit :=
    finiteChart_dirichlet_tendsto_bracketedDirichletChart
      3 (by norm_num) (by norm_num) hhalf
  have hchart : bracketedDirichletChart 3 s = 0 :=
    tendsto_nhds_unique hlimit hdirichlet
  exact
    (bracketedDirichletChart_zero_iff_genuineContinuation_zero
      3 (by norm_num) (by norm_num) hs).1 hchart

/-- The scalar Genuine and the primitive real-plane camera have exactly the
same zero set in the open strip; complex notation only packages two real
coordinates. -/
theorem nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    NativeCarryGeometry.Operator.BoundaryConvergesToZero 3 s.re s.im ↔
      genuineContinuation s = 0 := by
  constructor
  · exact nativeCarryRealBoundaryClosure_to_genuineContinuation_zero hs
  · exact genuineContinuation_zero_to_nativeCarryRealBoundaryClosure hs

end

end NativeCarryGeometry.Internal.Analytic.Cp

namespace NativeCarryGeometry.Equivalence

open Filter

noncomputable section

/-- Complex parameter whose coordinates are the radial exponent and phase. -/
def canonicalParameter (sigma time : ℝ) : ℂ :=
  ⟨sigma, time⟩

/-- Complex coordinate of the already weighted native tower. -/
def nativeCanonicalParameter (time : ℝ) : ℂ :=
  canonicalParameter ((1 : ℝ) / 2) time

/-- Analytic readout of the native operator; only phase time is free. -/
def nativeCarryAnalyticReadout (time : ℝ) : ℂ :=
  Analytic.canonicalCarryContinuation (nativeCanonicalParameter time)

@[simp] private theorem canonicalParameter_re (sigma time : ℝ) :
    (canonicalParameter sigma time).re = sigma := rfl

@[simp] private theorem canonicalParameter_im (sigma time : ℝ) :
    (canonicalParameter sigma time).im = time := rfl

/-- NCG-EQV-005: Real-State/Power-Monomial Coordinate Identity. -/
theorem complexCoordinates_realCarryState_eq_powerMonomial
    (sigma time : ℝ) {n : ℤ} (hn : 0 < n) :
    complexCoordinates (Operator.realCarryState sigma time n) =
      Analytic.powerMonomial (canonicalParameter sigma time) n := by
  change
    Internal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
        (Internal.Analytic.Cp.nativeCarryRealPlaneSampleAt sigma time n) =
      Internal.Analytic.Cp.dirichletTerm
        (Internal.Analytic.Cp.nativeCarryRealPlaneParameter sigma time) n
  exact
    Internal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging_sampleAt_eq_dirichletTerm
      sigma time hn

/--
NCG-EQV-016: Complex Power-Monomial Quadratic-Norm Identity.

Writing the radial deformation as `n^(-s)` changes no mathematics: the real
coordinate `s.re = sigma` is exactly the exponent in the already proved
quadratic norm `n^(-2*sigma)`.
-/
@[simp] theorem normSq_powerMonomial_canonicalParameter
    (sigma time : ℝ) {n : ℤ} (hn : 0 < n) :
    Complex.normSq
        (Analytic.powerMonomial
          (canonicalParameter sigma time) n) =
      (n : ℝ) ^ (-2 * sigma) := by
  rw [← complexCoordinates_realCarryState_eq_powerMonomial
    sigma time hn]
  exact normSq_complexCoordinates_radialDeformationState
    sigma time hn

/-- The native real state and its complex form are exactly coordinate images. -/
theorem complexCoordinates_nativeRealCarryState_eq_powerMonomial
    (time : ℝ) {n : ℤ} (hn : 0 < n) :
    complexCoordinates (Operator.nativeRealCarryState time n) =
      Analytic.powerMonomial (nativeCanonicalParameter time) n := by
  calc
    complexCoordinates (Operator.nativeRealCarryState time n) =
        complexCoordinates
          (Operator.realCarryState ((1 : ℝ) / 2) time n) := by
      apply congrArg complexCoordinates
      exact
        Internal.Analytic.Cp.nativeCarryRealPlaneSample_eq_sampleAt_half
          time n
    _ = Analytic.powerMonomial
          (canonicalParameter ((1 : ℝ) / 2) time) n :=
      complexCoordinates_realCarryState_eq_powerMonomial
        ((1 : ℝ) / 2) time hn
    _ = Analytic.powerMonomial (nativeCanonicalParameter time) n := rfl

/-- NCG-EQV-006: Finite Real/Analytic Operator Identity. -/
theorem complexCoordinates_finiteRealOperator_eq_finiteBracketChart
    (camera cutoff : ℕ)
    (hprime : Nat.Prime camera) (hodd : Odd camera)
    (sigma time : ℝ) :
    complexCoordinates
        (Operator.finiteRealCarryOperator
          camera cutoff sigma time) =
      Bracket.Balanced.finiteBracketChart camera cutoff
        (Analytic.powerMonomial (canonicalParameter sigma time)) := by
  change
    Internal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
        (Internal.Analytic.Cp.nativeCarryRealPlaneFiniteChartAt
          camera cutoff sigma time) =
      Internal.Genuine.Cp.finiteChart camera cutoff
        (Internal.Analytic.Cp.dirichletTerm
          (Internal.Analytic.Cp.nativeCarryRealPlaneParameter sigma time))
  exact
    Internal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging_finiteChartAt_eq_dirichlet
      camera cutoff hprime hodd sigma time

/-- Exact finite identity for the mass-built native operator. -/
theorem complexCoordinates_finiteNativeOperator_eq_finiteBracketChart
    (camera cutoff : ℕ)
    (hprime : Nat.Prime camera) (hodd : Odd camera)
    (time : ℝ) :
    complexCoordinates
        (Operator.finiteNativeRealCarryOperator camera cutoff time) =
      Bracket.Balanced.finiteBracketChart camera cutoff
        (Analytic.powerMonomial (nativeCanonicalParameter time)) := by
  calc
    complexCoordinates
        (Operator.finiteNativeRealCarryOperator camera cutoff time) =
      complexCoordinates
        (Operator.finiteRealCarryOperator camera cutoff
          ((1 : ℝ) / 2) time) := by
      apply congrArg complexCoordinates
      exact
        Internal.Analytic.Cp.nativeCarryRealPlaneFiniteChart_eq_chartAt_half
          camera cutoff time
    _ = Bracket.Balanced.finiteBracketChart camera cutoff
        (Analytic.powerMonomial
          (canonicalParameter ((1 : ℝ) / 2) time)) :=
      complexCoordinates_finiteRealOperator_eq_finiteBracketChart
        camera cutoff hprime hodd ((1 : ℝ) / 2) time
    _ = Bracket.Balanced.finiteBracketChart camera cutoff
        (Analytic.powerMonomial (nativeCanonicalParameter time)) := rfl

/--
NCG-EQV-007: Camera-Three Boundary/Continuation Zero Equivalence.

The camera specialization and the open-strip premise are part of the theorem;
neither may be erased when this result is cited.
-/
theorem boundaryConvergesToZero_iff_canonicalCarryContinuation_eq_zero
    {s : ℂ} (hs : s ∈ Analytic.canonicalStrip) :
    Operator.BoundaryConvergesToZero 3 s.re s.im ↔
      Analytic.canonicalCarryContinuation s = 0 :=
  Internal.Analytic.Cp.nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero
    hs

/--
NCG-EQV-011: Native Boundary/Analytic Readout Zero Identity.

The native real boundary and native analytic readout have exactly the same
zeros.  No additional mass predicate appears because both sides already use
the carry-built tower.
-/
theorem nativeBoundaryConvergesToZero_iff_nativeCarryAnalyticReadout_eq_zero
    (time : ℝ) :
    Operator.NativeBoundaryConvergesToZero 3 time ↔
      nativeCarryAnalyticReadout time = 0 := by
  have hs : nativeCanonicalParameter time ∈ Analytic.canonicalStrip := by
    change 0 < (1 : ℝ) / 2 ∧ (1 : ℝ) / 2 < 1
    constructor <;> norm_num
  have hradial :=
    boundaryConvergesToZero_iff_canonicalCarryContinuation_eq_zero hs
  rw [← Operator.radialDeformationBoundary_half_iff_native 3 time]
  simpa [nativeCarryAnalyticReadout, nativeCanonicalParameter,
    canonicalParameter] using hradial

/--
NCG-EQV-017: One Native Operator Zero, Analytic Coordinate Form.

This is the principal zero theorem.  The left side is the unique zero predicate
of the mass-built operator; the right side is its complex-coordinate readout.
-/
theorem isNativeCarryOperatorZero_iff_analyticReadout_eq_zero
    (time : ℝ) :
    Operator.IsNativeCarryOperatorZero 3 time ↔
      nativeCarryAnalyticReadout time = 0 :=
  nativeBoundaryConvergesToZero_iff_nativeCarryAnalyticReadout_eq_zero time

/-- Native analytic zero: zero of the readout of the already weighted tower. -/
abbrev IsNativeCanonicalCarryOperatorZero (time : ℝ) : Prop :=
  nativeCarryAnalyticReadout time = 0

/-- NCG-EQV-012: Native Real/Analytic Operator Zero Identity.

Native real and analytic zero predicates are literally equivalent. -/
theorem isNativeRealCarryOperatorZero_iff_isNativeCanonicalCarryOperatorZero
    (time : ℝ) :
    Operator.IsNativeRealCarryOperatorZero 3 time ↔
      IsNativeCanonicalCarryOperatorZero time :=
  nativeBoundaryConvergesToZero_iff_nativeCarryAnalyticReadout_eq_zero time

/--
The ambient analytic chart represents a native zero when its radial coordinate
preserves the upstream mass and its analytic resultant cancels.  This is a
representation predicate, not a second kind of operator zero.
-/
def AnalyticChartRepresentsNativeZero (s : ℂ) : Prop :=
  Operator.RealCarryEnergyCompatible s.re s.im ∧
    Analytic.canonicalCarryContinuation s = 0

/--
Legacy compatibility alias for `AnalyticChartRepresentsNativeZero`.
-/
abbrev IsCanonicalCarryOperatorZero (s : ℂ) : Prop :=
  AnalyticChartRepresentsNativeZero s

/--
NCG-EQV-018: Analytic-Chart Representation Factorization.

The complex radial coordinate represents the native mass exactly at one half;
the remaining conjunct is cancellation of the ambient analytic chart.
-/
theorem analyticChartRepresentsNativeZero_iff
    (s : ℂ) :
    AnalyticChartRepresentsNativeZero s ↔
      s.re = (1 : ℝ) / 2 ∧
        Analytic.canonicalCarryContinuation s = 0 := by
  unfold AnalyticChartRepresentsNativeZero
  rw [Operator.realCarryEnergyCompatible_iff]

/--
NCG-EQV-008: Real/Analytic Radial-Presentation Identity.

Inside the canonical strip, the real and analytic radial presentations are
exactly the same proposition.
-/
theorem isRealCarryOperatorZero_iff_isCanonicalCarryOperatorZero
    {s : ℂ} (hs : s ∈ Analytic.canonicalStrip) :
    Operator.IsRealCarryOperatorZero 3 s.re s.im ↔
      IsCanonicalCarryOperatorZero s := by
  unfold Operator.IsRealCarryOperatorZero
    IsCanonicalCarryOperatorZero
  exact and_congr Iff.rfl
    (boundaryConvergesToZero_iff_canonicalCarryContinuation_eq_zero hs)

/--
NCG-EQV-009: Canonical Analytic Radial-Presentation Uniqueness.

This is uniqueness of the ambient radial presentation, not a mass condition
added to the native operator and not a statement about arbitrary scalar zeros.
-/
theorem canonicalCarryOperatorZero_re_eq_half
    {s : ℂ} (hs : s ∈ Analytic.canonicalStrip)
    (hzero : IsCanonicalCarryOperatorZero s) :
    s.re = (1 : ℝ) / 2 := by
  have hreal :
      Operator.IsRealCarryOperatorZero 3 s.re s.im :=
    (isRealCarryOperatorZero_iff_isCanonicalCarryOperatorZero hs).2 hzero
  exact Operator.realCarryOperatorZero_sigma_eq_half hreal

/--
NCG-EQV-019: Analytic-Chart Native Representation Uniqueness.

No strip hypothesis is needed for this representation statement: preserving
the carry-built quadratic norm itself forces the radial coordinate to one half.
-/
theorem analyticChartRepresentsNativeZero_re_eq_half
    {s : ℂ} (hrep : AnalyticChartRepresentsNativeZero s) :
    s.re = (1 : ℝ) / 2 :=
  ((analyticChartRepresentsNativeZero_iff s).1 hrep).1

/--
Canonical-name form of the real/analytic representation crosswalk.  It says
that two coordinate charts represent the same native zero.
-/
theorem radialChartRepresentsNativeZero_iff_analyticChartRepresentsNativeZero
    {s : ℂ} (hs : s ∈ Analytic.canonicalStrip) :
    Operator.RadialChartRepresentsNativeZero 3 s.re s.im ↔
      AnalyticChartRepresentsNativeZero s := by
  simpa [Operator.IsRealCarryOperatorZero,
    IsCanonicalCarryOperatorZero] using
    (isRealCarryOperatorZero_iff_isCanonicalCarryOperatorZero hs)

end
end NativeCarryGeometry.Equivalence
