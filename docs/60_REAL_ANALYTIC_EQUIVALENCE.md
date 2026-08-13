# Real–Analytic Identity of the Same Resultants

## 1. Faithful coordinates

```lean
complexCoordinates : Operator.RealCarryPlane ≃+ ℂ
```

is an injective additive equivalence.  It preserves norm square, commutes with
the finite bracket, and preserves finite resultant zeros in both directions.
There is no separate “real zero” and “complex zero” of one resultant.

## 2. Radial norm coordinate

For positive `n`, `NCG-EQV-013` and `NCG-EQV-016` prove

```text
normSq(n^(-(sigma+i t))) = n^(-2 sigma).
```

The coordinate `sigma` controls radial amplitude and quadratic norm.  Native
mass compatibility occurs exactly at one half, but that compatibility is not
part of the raw zero equation.

## 3. Full radial zero-locus identity

Inside the canonical strip, `NCG-EQV-008` states

```lean
Operator.IsRealCarryOperatorZero 3 s.re s.im ↔
  IsCanonicalCarryOperatorZero s
```

The left side is raw real boundary cancellation.  The right side is
`canonicalCarryContinuation s = 0`.  The theorem transports every zero in the
stated domain, including any possible off-half zero.

## 4. Fixed native zero-locus identity

Restricting to the native member gives `NCG-EQV-017`:

```lean
Operator.IsNativeCarryOperatorZero 3 time ↔
  nativeCarryAnalyticReadout time = 0
```

This is the one-half specialization of the larger radial family, not a proof
that the larger family has no other zeros.

## 5. Representation crosswalk

The real and analytic native-representation relations share the same mass
predicate and equivalent raw zero predicates.  Consequently

```lean
RadialChartRepresentsNativeZero 3 s.re s.im ↔
  AnalyticChartRepresentsNativeZero s
```

in the canonical strip.  Their half-shell conclusions arise from mass
compatibility alone.

## 6. Vocabulary

| Concept | Public name | Meaning |
|---|---|---|
| Fixed native zero | `IsNativeCarryOperatorZero` | zero of the carry-built one-half member |
| Raw real radial zero | `IsRealCarryOperatorZero` | boundary cancellation at supplied `(sigma,time)` |
| Raw analytic radial zero | `IsCanonicalCarryOperatorZero` | `canonicalCarryContinuation s = 0` |
| Native representation | `RadialChartRepresentsNativeZero` / `AnalyticChartRepresentsNativeZero` | native-mass compatibility plus raw zero |

The first three rows are zero predicates.  The fourth is a representation
relation.  Conflating the fourth with either radial zero predicate is the
semantic error corrected after `v0.4.0`.
