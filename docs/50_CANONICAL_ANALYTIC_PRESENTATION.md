# Canonical Analytic Presentation

## 1. Coordinate purpose

The analytic layer stores the same rotating real samples as complex numbers.
For `s = sigma + i t`,

```text
n^(-s) = n^(-sigma) (cos(-t log n) + i sin(-t log n)).
```

Thus the real coordinate of `s` is the radial amplitude exponent.  Complex
notation does not supply mass or alter resultant vanishing.

## 2. Bracket series and canonical strip

The finite bracket chart, bracket-series convergence, holomorphy, camera
factor, and odd-prime camera normalization are registered as `NCG-ANL-001`
through `NCG-ANL-008`.  The real/analytic boundary crosswalk uses

```lean
canonicalStrip = {s : ℂ | 0 < s.re ∧ s.re < 1}
```

and camera `3` as the normalized representative.

## 3. Raw analytic zero

The canonical analytic radial operator zero is

```lean
IsCanonicalCarryOperatorZero s
```

and abbreviates exactly

```lean
canonicalCarryContinuation s = 0
```

No native-mass condition occurs in this predicate.  `NCG-ANL-008` and
`NCG-EQV-008` transport this raw cancellation locus through camera
normalization and faithful real/complex coordinates.

## 4. Native analytic readout

The fixed native member is obtained by restriction:

```lean
nativeCarryAnalyticReadout time :=
  canonicalCarryContinuation ⟨1 / 2, time⟩
```

`NCG-EQV-017` identifies its zeros with
`IsNativeCarryOperatorZero 3 time`.

## 5. Analytic native representation

The separate relation

```lean
AnalyticChartRepresentsNativeZero s
```

means native-mass compatibility together with
`IsCanonicalCarryOperatorZero s`.  `NCG-EQV-009` exposes this conjunction,
and `NCG-EQV-018` factors it as

```lean
s.re = 1 / 2 ∧ canonicalCarryContinuation s = 0.
```

This factorization classifies native representations.  It is not a theorem
that every raw analytic zero has real part one half.

## 6. Scope

An off-half zero of `canonicalCarryContinuation`, if found, remains a zero of
the canonical analytic radial family.  Whether a separately transferred
classical function has the same full zero locus requires its own audited
transfer theorem and is outside this repository.
