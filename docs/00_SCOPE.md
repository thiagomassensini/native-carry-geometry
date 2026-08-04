# Formal Scope and Semantic Contract

## 1. Authority

The audit root is `NativeCarryGeometry.lean`. Elaborated Lean types are the
formal authority. This document fixes how those types are named and cited so
that an auxiliary chart is never mistaken for a second operator.

The core dependency direction is:

```text
positional QR → carry depth → carry mass → quadratic amplitude
→ native tower → native state → bracket operator
→ real/complex coordinate equivalence
```

Mass and amplitude are upstream data. The zero predicate does not manufacture
or append them later.

## 2. Two independent parameters

- A positional base `b` is used for quotient–residue decomposition, maximal
  base-power depth, carry probability, mass, and amplitude.
- A camera width `camera` is used for the finite centered-bracket observation
  rule and its boundary limit.

No theorem silently identifies base and camera.

## 3. Upstream mass and amplitude

For `b > 1` and depth `k`:

[
operatorname{carryMass}(b,k)=b^{-k},
qquad
operatorname{carryAmplitude}(b,k)=b^{-k/2}.
]

The native integer tower is assembled in the measure layer:

```lean
nativeTowerMass n
nativeTowerAmplitude n
```

with:

```lean
-- NCG-MAS-003
(nativeTowerAmplitude n) ^ 2 = nativeTowerMass n
```

For positive `n`, this is the inverse-integer mass (n^{-1}) and its
quadratic root (n^{-1/2}). The native state reads this amplitude; the
operator never receives a later mass condition.

## 4. Native state and radial comparison chart

The native state has phase time as its free parameter:

[
u_t(n)=n^{-1/2}
(cos(-tlog n),sin(-tlog n)).
]

Lean names it:

```lean
nativeRealCarryState time n
```

The ambient radial comparison chart replaces only the amplitude:

[
u_{sigma,t}(n)=n^{-sigma}
(cos(-tlog n),sin(-tlog n)).
]

Lean names it:

```lean
radialDeformationState sigma time n
```

Its quadratic energy is:

[
|u_{sigma,t}(n)|^2=n^{-2sigma}.
]

The exact public results are:

```lean
-- NCG-REA-005
quadraticEnergy (radialDeformationState sigma time n) =
  (n : ℝ) ^ (-2 * sigma)

-- NCG-REA-006
RadialDeformationRepresentsNativeMass sigma time ↔
  sigma = (1 : ℝ) / 2
```

Thus `sigma` is not an additional native-operator input. It is the coordinate
that varies amplitude and quadratic norm in the ambient chart.

## 5. One operator and one zero

The unique native zero predicate is:

```lean
abbrev IsNativeCarryOperatorZero
    (camera : ℕ) (time : ℝ) : Prop :=
  NativeBoundaryConvergesToZero camera time
```

It applies to the tower already carrying its mass.

The names `IsNativeRealCarryOperatorZero` and
`IsNativeCanonicalCarryOperatorZero` are legacy coordinate-labelled aliases.
They do not define two zero species.

The principal theorem is:

```lean
-- NCG-EQV-017
Operator.IsNativeCarryOperatorZero 3 time ↔
  nativeCarryAnalyticReadout time = 0
```

This is one operator zero in real and analytic coordinates.

## 6. Complex coordinates preserve the construction

The additive equivalence

[
J:mathbb R^2simeqmathbb C,qquad J(x,y)=x+iy
]

is `complexCoordinates`. Lean proves that it is injective, preserves norm
square, commutes with the finite bracket, and preserves finite zeros.

For positive `n`:

```lean
-- NCG-EQV-013
Complex.normSq
    (complexCoordinates
      (radialDeformationState sigma time n)) =
  (n : ℝ) ^ (-2 * sigma)

-- NCG-EQV-014
Complex.normSq
    (complexCoordinates
      (nativeRealCarryState time n)) =
  (n : ℝ)⁻¹
```

The power monomial at (s=sigma+it) is the same real rotating sample stored
in complex coordinates. Complex notation contributes no new mass, algebra, or
zero.

## 7. Ambient chart cancellation and native representation

Raw cancellation of the comparison family is named:

```lean
RadialChartCancelsAt camera sigma time
```

The corresponding analytic equation is
`canonicalCarryContinuation s = 0`. These are chart-cancellation statements,
not definitions of another operator zero.

A chart represents the native operator only if it also preserves the upstream
mass:

```lean
RadialChartRepresentsNativeZero camera sigma time
AnalyticChartRepresentsNativeZero s
```

Their factorizations are:

```lean
-- NCG-OPR-007
RadialChartRepresentsNativeZero camera sigma time ↔
  sigma = (1 : ℝ) / 2 ∧
    IsNativeCarryOperatorZero camera time

-- NCG-EQV-018
AnalyticChartRepresentsNativeZero s ↔
  s.re = (1 : ℝ) / 2 ∧
    canonicalCarryContinuation s = 0
```

The first coordinate is therefore representation data. Once the chart
represents the native tower, it is definitionally on the native shell and its
cancellation is the one native zero.

Historical names such as `IsRealCarryOperatorZero`,
`IsFiniteRealCarryOperatorZero`, and
`IsCanonicalCarryOperatorZero` remain aliases for compatibility. New
documentation and theorem labels use verbs such as `RepresentsNativeZero`
rather than introducing a second zero noun.

## 8. Exact principal claims

This repository proves:

1. canonical quotient–residue decomposition at every depth;
2. unique maximal-depth factorization for every positive integer and every
   base `b > 1`, including composite bases;
3. uniform probability of the distinguished zero-residue carry event;
4. carry mass and its quadratic-root amplitude;
5. local and global multibase quadratic rigidity;
6. construction of the native integer tower before the operator;
7. energy invariance under real logarithmic rotation;
8. additive naturality of the centered bracket;
9. faithful (mathbb R^2simeqmathbb C) coordinate encoding;
10. exact finite native real/complex identity;
11. exact native boundary/analytic-readout identity for camera `3`;
12. explicit complex norm law (n^{-2sigma});
13. uniqueness of the mass-preserving radial representation.

## 9. Exact restrictions

### 9.1. Camera-three analytic crosswalk

The boundary/analytic chart crosswalk is restricted to camera `3` and:

```lean
s ∈ Analytic.canonicalStrip
```

where `canonicalStrip = {s | 0 < s.re ∧ s.re < 1}`.

### 9.2. Odd-prime hypotheses

Balanced-residue equivalences, normalized analytic-camera compatibility, and
certain finite chart identities retain explicit `Nat.Prime` and `Odd`
hypotheses. These do not propagate to multibase quadratic rigidity.

### 9.3. Total degenerate cameras

The generic family uses:

```lean
halfRange camera = (camera - 1) / 2
```

so `camera = 0, 1, 2` are degenerate generic cases. The binary adjacent-center
arithmetic is nondegenerate but separate.

## 10. Nonclaims

This release does not claim:

- that the native operator has a free `sigma` input;
- that raw ambient chart cancellation alone forces `sigma = 1/2`;
- that raw chart cancellation is an operator zero;
- that internal energy vanishes whenever a sum of nonzero terms cancels;
- that a finite cutoff must vanish for boundary convergence;
- that every camera has the same temporal resonance set;
- that every natural camera is a nondegenerate residue system;
- that mass is supplied by the operator or its zero predicate;
- that primality causes the half exponent;
- that curvature, Green, a completed operator, an external analytic
  identification, or any hypothesis about such an external function is a
  premise of the native result.

These restrictions do not weaken the native statement. They keep the one
operator, one mass-built state, and one zero distinct from a larger ambient
comparison chart.
