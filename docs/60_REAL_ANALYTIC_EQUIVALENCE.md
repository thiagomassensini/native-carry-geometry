# Real–Analytic Identity of the Same Operator

## 1. The identity, not an analogy

The map

$
J:\mathbb{R}^{2}\simeq\mathbb{C},
\qquad J(x,y)=x+iy.
$

is implemented as an additive equivalence:

```lean
complexCoordinates : Operator.RealCarryPlane ≃+ ℂ
```

It is a coordinate change. It is not a new dynamical operation, a completed
operator, or an external analytic identification.

Lean proves:

- injectivity of $J$ (`NCG-EQV-001`);
- $\operatorname{normSq}(J(u))=E(u)$ (`NCG-EQV-002`);
- naturality through the complete finite bracket (`NCG-EQV-003`);
- preservation of finite resultant zeros in both directions
  (`NCG-EQV-004` and `NCG-EQV-010`).

Hence:

$
R=0\iff J(R)=0.
$

There is no “real zero” and “complex zero” to compare. There is one resultant,
one zero locus, and two faithful coordinate records.

## 2. Sigma is the quadratic-norm coordinate

For positive `n`, the ambient radial sample is:

$
u_{\sigma,t}(n)
=
n^{-\sigma}
\bigl(\cos(-t\log n),\sin(-t\log n)\bigr).
$

Its complex coordinate is exactly:

$
J\bigl(u_{\sigma,t}(n)\bigr)=n^{-(\sigma+it)}.
$

This is `NCG-EQV-005`. The norm identities are now named directly:

```lean
-- NCG-EQV-013
Complex.normSq
    (complexCoordinates
      (radialDeformationState sigma time n)) =
  (n : ℝ) ^ (-2 * sigma)

-- NCG-EQV-016
Complex.normSq
    (powerMonomial (canonicalParameter sigma time) n) =
  (n : ℝ) ^ (-2 * sigma)
```

Thus varying `sigma = Re(s)` in the complex plane is exactly
varying the amplitude $n^{-\sigma}$ and its quadratic norm
$n^{-2\sigma}$. It is a change of radial chart, not a change of operator.

## 3. Native mass in both coordinates

The mass-built state has:

$
E\bigl(u_t(n)\bigr)=n^{-1}.
$

By `NCG-EQV-014`:

$
\operatorname{normSq}\bigl(J(u_t(n))\bigr)=n^{-1}.
$

The ambient complex radial chart preserves this native mass for all
nondegenerate positive inputs exactly at one half:

```lean
-- NCG-EQV-015
(∀ n : ℤ, 1 < n →
  Complex.normSq
      (complexCoordinates
        (radialDeformationState sigma time n)) =
    (n : ℝ)⁻¹) ↔
  sigma = (1 : ℝ) / 2
```

This is the coordinate form of the same quadratic rigidity already proved from
carry mass. Complex notation neither creates nor selects the mass.

## 4. Complete finite operator identity

For every camera and cutoff, additive naturality gives:

```lean
complexCoordinates
    (finiteNativeRealCarryOperator camera cutoff time) =
  finiteSaturatedBracketOperator camera cutoff
    (fun n => complexCoordinates
      (nativeRealCarryState time n))
```

For odd prime cameras, the right-hand side is also the finite analytic bracket
chart evaluated at the same samples. This is an equality of complete
resultants, not merely equality of norms or zero sets.

## 5. The native operator-zero predicate

The native analytic readout is:

```lean
nativeCarryAnalyticReadout time :=
  canonicalCarryContinuation ⟨1 / 2, time⟩
```

The canonical zero predicate is:

```lean
Operator.IsNativeCarryOperatorZero camera time
```

The principal theorem is:

```lean
-- NCG-EQV-017
Operator.IsNativeCarryOperatorZero 3 time ↔
  nativeCarryAnalyticReadout time = 0
```

Both sides already use the mass-built native tower. No additional mass premise
is attached to the zero, and no second zero object is introduced.

The older theorem `NCG-EQV-012` uses the coordinate-labelled aliases
`IsNativeRealCarryOperatorZero` and
`IsNativeCanonicalCarryOperatorZero`. It is a compatibility spelling of this
same identity.

## 6. Ambient chart cancellation

For an arbitrary point $s=\sigma+it$ of the canonical strip, the wider chart
crosswalk is:

```lean
radialChartCancelsAt_iff_canonicalChartCancelsAt
```

with type:

```lean
Operator.RadialChartCancelsAt 3 s.re s.im ↔
  Analytic.canonicalCarryContinuation s = 0
```

This relates cancellation in two coordinate descriptions of the ambient radial
chart. It is deliberately not named `OperatorZero`.

The restrictions are part of the theorem:

- camera is exactly `3`;
- `s ∈ canonicalStrip`;
- `canonicalStrip = {s | 0 < s.re ∧ s.re < 1}`.

## 7. When the ambient chart represents the native operator

The real and analytic representation relations are:

```lean
Operator.RadialChartRepresentsNativeZero camera sigma time
AnalyticChartRepresentsNativeZero s
```

Inside the camera-three crosswalk, Lean proves that these two relations are
equivalent. Independently of the strip, the analytic factorization is:

```lean
-- NCG-EQV-018
AnalyticChartRepresentsNativeZero s ↔
  s.re = (1 : ℝ) / 2 ∧
    canonicalCarryContinuation s = 0
```

and the uniqueness corollary is:

```lean
-- NCG-EQV-019
AnalyticChartRepresentsNativeZero s →
  s.re = (1 : ℝ) / 2
```

The reason is exactly quadratic mass preservation, not a second boundary,
curvature, Green, or external-function argument.

## 8. Vocabulary enforced by the audit

| Concept | Canonical name | Meaning |
|---|---|---|
| Native operator-zero predicate | `IsNativeCarryOperatorZero` | boundary-zero locus of the mass-built tower |
| Real coordinate encoding | `complexCoordinates` | additive equivalence $\mathbb{R}^{2}\simeq\mathbb{C}$ |
| Ambient radial cancellation | `RadialChartCancelsAt` | cancellation of a comparison chart |
| Analytic ambient cancellation | `canonicalCarryContinuation s = 0` | same chart cancellation in complex coordinates |
| Native representation relation | `RadialChartRepresentsNativeZero` / `AnalyticChartRepresentsNativeZero` | mass preservation plus chart cancellation |

Legacy aliases remain source compatible, but public documentation and new
theorems use this vocabulary.
