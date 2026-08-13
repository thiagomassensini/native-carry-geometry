# Formal Scope and Semantic Contract

## 1. Authority

`NativeCarryGeometry.lean` is the audit root, and elaborated Lean types are the
formal authority.  This document fixes the intended semantics of those types.
Kernel acceptance proves that a declaration follows from its definitions and
premises; it does not make a circular definition informative.  The public
contract therefore keeps raw vanishing and native-mass representation in
separate propositions.

## 2. Upstream carry mass

For positional base `b > 1` and depth `k`,

```text
carryMass(b,k)      = b^(-k)
carryAmplitude(b,k) = b^(-k/2)
```

The native tower is constructed before any camera is evaluated:

```lean
nativeTowerMass n
nativeTowerAmplitude n
```

with `NCG-MAS-003`:

```lean
(nativeTowerAmplitude n) ^ 2 = nativeTowerMass n
```

The fixed native state therefore has amplitude `n^(-1/2)` by construction.

## 3. The radial operator family

The comparison family replaces the fixed amplitude by `n^(-sigma)`:

```lean
radialDeformationState sigma time n
```

and `NCG-REA-005` proves

```lean
quadraticEnergy (radialDeformationState sigma time n) =
  (n : ℝ) ^ (-2 * sigma)
```

The parameter `sigma` changes amplitude and quadratic norm.  The theorem

```lean
RadialDeformationRepresentsNativeMass sigma time ↔
  sigma = (1 : ℝ) / 2
```

classifies mass compatibility with the fixed native state.  It is not a
definition of zero.

## 4. Zero predicates

The fixed native operator has

```lean
IsNativeCarryOperatorZero camera time
```

The full real radial family has

```lean
IsRealCarryOperatorZero camera sigma time
```

which is definitionally the raw boundary cancellation
`RadialChartCancelsAt camera sigma time`.  The finite family similarly uses

```lean
IsFiniteRealCarryOperatorZero camera cutoff sigma time
```

for vanishing of the finite radial resultant.  In analytic coordinates,

```lean
IsCanonicalCarryOperatorZero s
```

means exactly `canonicalCarryContinuation s = 0`.

None of these raw zero predicates contains `sigma = 1/2` or a mass premise.
A raw zero outside one half is still a zero of the supplied operator family.

## 5. Native specialization

At the native amplitude, the radial family and fixed native operator agree:

```lean
-- NCG-OPR-005
IsRealCarryOperatorZero camera (1 / 2) time ↔
  IsNativeCarryOperatorZero camera time
```

This is an extensional specialization theorem.  It does not classify the
radial zero locus away from one half.

## 6. Representation relations

The propositions

```lean
RadialChartRepresentsNativeZero camera sigma time
RadialChartRepresentsFiniteNativeZero camera cutoff sigma time
AnalyticChartRepresentsNativeZero s
```

conjoin two independent facts:

1. the radial coordinate preserves the upstream native mass;
2. the corresponding radial resultant is zero.

The separation is exposed by `NCG-OPR-006` and `NCG-EQV-009`.  The resulting
factorizations are `NCG-OPR-007`, `NCG-OPR-008`, and `NCG-EQV-018`.
Their one-half conclusion belongs to the **representation** relation, not to
raw vanishing.

## 7. Real and analytic coordinates

`complexCoordinates : RealCarryPlane ≃+ ℂ` is an injective additive
equivalence preserving norm square and finite resultants.  In the canonical
strip, `NCG-EQV-008` identifies the raw real and analytic radial zero loci:

```lean
IsRealCarryOperatorZero 3 s.re s.im ↔
  IsCanonicalCarryOperatorZero s
```

The coordinate change neither creates nor deletes an off-half zero.

## 8. Exact claims

This repository proves:

1. positional decomposition, carry depth, carry mass, and quadratic amplitude;
2. construction of the fixed native state before the operator;
3. the radial quadratic-norm law;
4. finite and boundary zero predicates defined by raw resultant vanishing;
5. equality of radial and native zero predicates at `sigma = 1/2`;
6. faithful real/analytic zero-locus transport in the stated camera and strip;
7. factorization of native-representation relations through mass compatibility.

## 9. Exact nonclaims

This repository does not prove:

- that every raw radial zero has `sigma = 1/2`;
- that `IsRealCarryOperatorZero` or `IsCanonicalCarryOperatorZero` includes
  mass compatibility;
- that an off-half cancellation may be discarded as “not a zero”;
- that every camera has the same temporal resonance set;
- that finite vanishing is required for boundary convergence;
- that the native results alone identify a classical external function;
- that a theorem about the Riemann zeta function follows without a separate
  transfer proof.

The previous off-shell nonzero corollaries were removed because their
conclusion came from a mass condition embedded in the predicate called zero.
The corrected API leaves the substantive off-half question open to proof or
counterexample.
