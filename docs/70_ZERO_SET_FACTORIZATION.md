# Raw Zero Loci and Native-Representation Factorization

## 1. Why the distinction matters

A definition of zero must answer whether a supplied resultant vanishes.  A
mass-compatibility condition answers a different question: whether that point
represents the fixed carry-built native member.  Combining the two inside a
predicate named `Zero` makes an off-half nonzero theorem true by definition and
therefore gives no information about the actual off-half resultant.

Lean verifies derivability from definitions.  It cannot decide that a chosen
definition has silently answered the wrong mathematical question.

## 2. Correct raw predicates

Boundary level:

```lean
IsRealCarryOperatorZero camera sigma time :=
  RadialChartCancelsAt camera sigma time
```

Finite level:

```lean
IsFiniteRealCarryOperatorZero camera cutoff sigma time :=
  quadraticEnergy
    (finiteRadialDeformation camera cutoff sigma time) = 0
```

Analytic coordinates:

```lean
IsCanonicalCarryOperatorZero s :=
  canonicalCarryContinuation s = 0
```

Each predicate records raw vanishing at the supplied coordinate.  None
contains `sigma = 1/2`.

## 3. Fixed native predicate

```lean
IsNativeCarryOperatorZero camera time :=
  NativeBoundaryConvergesToZero camera time
```

The native state was already built from the quadratic-root carry amplitude.
At one half, `NCG-OPR-005` proves

```lean
IsRealCarryOperatorZero camera (1 / 2) time ↔
  IsNativeCarryOperatorZero camera time.
```

## 4. Representation predicates

```lean
RadialChartRepresentsNativeZero camera sigma time :=
  RadialDeformationRepresentsNativeMass sigma time ∧
    IsRealCarryOperatorZero camera sigma time
```

The analytic and finite relations have the same structure.  `NCG-OPR-006`
and `NCG-EQV-009` expose this separation directly.

The factorization

```lean
RadialChartRepresentsNativeZero camera sigma time ↔
  sigma = 1 / 2 ∧ IsNativeCarryOperatorZero camera time
```

is valid because native-mass compatibility is equivalent to `sigma = 1/2`.
It classifies representations, not raw zeros.

## 5. Removed circular corollaries

The following declarations were removed:

```text
realCarryOperatorZero_sigma_eq_half
not_realCarryOperatorZero_of_sigma_ne_half
canonicalCarryOperatorZero_re_eq_half
```

Under the old aliases, each conclusion followed by unpacking a predicate that
had already conjoined mass compatibility with cancellation.  They did not
prove that raw cancellation was impossible away from one half.

They were replaced by:

```text
realCarryOperatorZero_half_iff_native
radialChartRepresentsNativeZero_iff_massCompatible_and_zero
analyticChartRepresentsNativeZero_iff_massCompatible_and_zero
```

These replacements state the actual relationships without deciding the
unresolved off-half zero question by nomenclature.

## 6. Logical consequences

The repository now supports the following valid implications:

```text
native representation  ⇒ sigma = 1/2
native representation  ⇒ raw radial zero
raw radial zero at 1/2 ⇔ fixed native zero
raw real zero          ⇔ raw analytic zero   (camera 3, canonical strip)
```

It deliberately does **not** contain

```text
raw radial zero ⇒ sigma = 1/2.
```

Therefore, if a raw zero occurs at `sigma ≠ 1/2`, it remains a zero of the
radial operator family.  Such a point would refute any separately stated
critical-line classification theorem for that full family.

## 7. External transfer

This repository does not identify its canonical continuation with the
classical Riemann zeta function.  Any conclusion about the Riemann hypothesis
requires a separate transfer theorem whose hypotheses, domain, and two-way
zero-locus preservation are independently audited.
