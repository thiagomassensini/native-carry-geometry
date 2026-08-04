# One Native Operator-Zero Predicate and Radial-Chart Representation

## 1. Canonical native operator-zero predicate

The native boundary is:

```lean
def NativeBoundaryConvergesToZero
    (camera : ℕ) (time : ℝ) : Prop :=
  Tendsto
    (fun cutoff =>
      finiteNativeRealCarryOperator camera cutoff time)
    atTop (nhds 0)
```

The one native operator-zero predicate is definitionally that boundary:

```lean
abbrev IsNativeCarryOperatorZero
    (camera : ℕ) (time : ℝ) : Prop :=
  NativeBoundaryConvergesToZero camera time
```

`IsBoundaryResonance` and `IsNativeRealCarryOperatorZero` are historical
aliases for the same proposition. Their names do not introduce additional
operator-zero predicates.

## 2. The ambient radial chart

The comparison family changes the amplitude from $n^{-1/2}$ to
$n^{-\sigma}$. Its boundary cancellation is:

```lean
RadialChartCancelsAt camera sigma time
```

This proposition alone describes an ambient chart cancellation. It is not an
operator-zero predicate.

The relation saying that the chart represents a point of the native
operator-zero locus is:

```lean
def RadialChartRepresentsNativeZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  RadialDeformationRepresentsNativeMass sigma time ∧
    RadialChartCancelsAt camera sigma time
```

The first conjunct is not mass added after the operator. It checks whether the
ambient chart retained the mass already constructed upstream.

## 3. Canonical factorization

`NCG-OPR-007` is the public factorization:

```lean
theorem radialChartRepresentsNativeZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    RadialChartRepresentsNativeZero camera sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsNativeCarryOperatorZero camera time
```

For each camera, the graph of native representations is therefore:

$
\left\{\frac12\right\}
\times
\left\{t\mid
  \operatorname{IsNativeCarryOperatorZero}(\mathit{camera},t)
\right\}.
$

This is not a classification of multiple zero predicates. It says exactly
when a point of the larger radial chart represents a point of the native
operator-zero locus.

## 4. Why the factorization is structurally forced after mass rigidity

The proof chain is:

1. the chart represents native mass;
2. quadratic rigidity gives $\sigma=1/2$;
3. at one half, the radial state is extensionally the native state;
4. the finite resultants and boundary limits are therefore the same;
5. chart cancellation lies in the native operator-zero locus.

Conversely:

1. start with $\sigma=1/2$ and the native operator-zero predicate;
2. the half-exponent chart preserves native mass;
3. the half-chart identity transports the boundary;
4. the radial chart represents the same zero-locus point.

Nothing arbitrary is selected when the operator-zero predicate is evaluated. The half exponent was already
forced by amplitude squared equalling carry mass.

## 5. Finite form

The finite representation relation is:

```lean
RadialChartRepresentsFiniteNativeZero
    camera cutoff sigma time
```

and `NCG-OPR-008` proves:

```lean
RadialChartRepresentsFiniteNativeZero
    camera cutoff sigma time ↔
  sigma = (1 : ℝ) / 2 ∧
    IsFiniteNativeCarryOperatorZero
      camera cutoff time
```

Again there is one finite native operator-zero predicate and a relation
describing which ambient chart points represent its zero locus.

## 6. Analytic-coordinate form

The ambient analytic representation relation is:

```lean
AnalyticChartRepresentsNativeZero s
```

`NCG-EQV-018` proves, without a strip premise:

```lean
AnalyticChartRepresentsNativeZero s ↔
  s.re = (1 : ℝ) / 2 ∧
    canonicalCarryContinuation s = 0
```

The native operator-zero predicate and its analytic readout define the same
zero locus by
`NCG-EQV-017`:

$
\operatorname{IsNativeCarryOperatorZero}(3,t)
\iff
\operatorname{nativeCarryAnalyticReadout}(t)=0.
$

The complex number stores the same two real coordinates. It cannot change the
zero locus.

## 7. Historical aliases (legacy compatibility)

The following names remain only to avoid breaking downstream source:

```text
IsFiniteRealCarryOperatorZero
IsRadialDeformationPresentationZero
IsRealCarryOperatorZero
IsNativeRealCarryOperatorZero
IsNativeCanonicalCarryOperatorZero
IsCanonicalCarryOperatorZero
BoundaryConvergesToZero
```

Their canonical replacements are, respectively, finite/native representation
relations, the native operator-zero predicate, or ambient chart cancellation. They are not
used to define the public ontology.

## 8. Camera scope

`NCG-OPR-007` is quantified over every natural camera, including total
degenerate instances. This means the mass-preserving radial coordinate is
camera-independent.

It does not assert:

- that different cameras have identical temporal resonance sets;
- that a resonance exists for every camera;
- that every natural camera is nondegenerate;
- that all raw finite sums are definitionally equal.

The camera-three analytic crosswalk retains its explicit canonical-strip
premise.

## 9. Independence from later routes

The factorization and native zero-locus identity do not depend on:

- Green or flux identities;
- a completed operator;
- spectral pencils;
- a self-adjoint realization;
- curvature-to-boundary promotion;
- an external classical analytic function;
- an equation or hypothesis about such an external function.

Curvature and tilt in this repository are auxiliary detectors of radial
deformation. Their null loci do not define additional operator-zero predicates.
