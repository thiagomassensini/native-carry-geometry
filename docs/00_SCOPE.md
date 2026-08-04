# Formal Scope

## 1. Purpose

This repository formalizes an intrinsic chain from positional carry geometry
to a mass-built real operator and then to faithful complex/analytic
coordinates. The audit root is `NativeCarryGeometry.lean`.

The formalization is organized around two independent natural parameters:

- a **positional base** `b`, used for quotient–residue decomposition, maximal
  base-power depth, carry probability, mass, and amplitude;
- a **camera width** `camera`, used for a finite centered-bracket observation
  rule and its limit.

No theorem silently identifies these parameters.

## 2. Core objects

For `b > 1` and depth `k`, the positional carry mass is

$$
\operatorname{carryMass}(b,k)=b^{-k}.
$$

The native vertical tower is constructed in the measure layer:

```lean
nativeTowerMass n
nativeTowerAmplitude n
```

with the proved identity

```lean
(nativeTowerAmplitude n) ^ 2 = nativeTowerMass n
```

The native real state therefore has no radial input:

$$
u_t(n)
=
n^{-1/2}
\bigl(\cos(-t\log n),\sin(-t\log n)\bigr).
$$

For comparison, the secondary radial deformation at positional depth is

$$
\operatorname{deformedAmplitude}(b,\sigma,k)=b^{-k\sigma}.
$$

The corresponding integer-indexed deformation assigns to a positive integer

$$
u_{\sigma,t}(n)
=
n^{-\sigma}
\bigl(\cos(-t\log n),\sin(-t\log n)\bigr)
\in\mathbb R^2.
$$

Its quadratic energy is

$$
\|u_{\sigma,t}(n)\|^2=n^{-2\sigma},
$$

independent of `time`.

For each natural camera and cutoff, the native finite operator applies centered
second differences to `u_t`. Its boundary predicate is convergence of the
resulting vectors to zero as the cutoff tends to infinity. The deformed family
is retained as an auxiliary presentation chart.

## 3. Native and radial-presentation zero predicates

The native real zero predicate is just zero of the already weighted boundary:

```lean
abbrev IsNativeRealCarryOperatorZero
    (camera : ℕ) (time : ℝ) : Prop :=
  NativeBoundaryConvergesToZero camera time
```

There is no mass conjunct here because mass was used to construct the tower.

The legacy two-coordinate public name is retained as a compatibility alias for
the radial-presentation predicate:

```lean
abbrev IsRealCarryOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  RadialDeformationRepresentsNativeMass sigma time ∧
    RadialDeformationBoundaryConvergesToZero camera sigma time
```

Its first conjunct means “this deformation is the native tower”; it is not a
condition injected into the operator.

The native analytic zero is likewise only the zero of the native readout:

```lean
IsNativeCanonicalCarryOperatorZero time
```

The two-coordinate compatibility predicate preserves the radial-chart test:

```lean
def IsCanonicalCarryOperatorZero (s : ℂ) : Prop :=
  Operator.RealCarryEnergyCompatible s.re s.im ∧
    Analytic.canonicalCarryContinuation s = 0
```

Thus `ℝ²` and `ℂ` are two faithful coordinate presentations. Neither changes
the native weights or the zero predicate.

## 4. Exact principal claims

The repository proves:

1. canonical quotient–residue decomposition at every depth;
2. unique factorization at maximal base-power depth for every positive
   integer and every base `b > 1`, including composite bases;
3. the uniform probability of the distinguished carry congruence class;
4. quadratic amplitude rigidity:
   \[
   b^{-2k\sigma}=b^{-k}\iff \sigma=\tfrac12
   \]
   for `b > 1` and `k > 0`;
5. equivalence of the positional mass-compatible domain and the real
   energy-compatible domain;
6. energy invariance under the real logarithmic rotation;
7. additive naturality of the finite bracket operator;
8. native boundary-zero predicate for every `camera : ℕ`;
9. faithful encoding of the real plane by two analytic coordinates;
10. finite real–analytic operator identity for odd prime cameras;
11. boundary equivalence for camera `3` in the canonical open strip;
12. native real–analytic zero-predicate identity for camera `3`;
13. uniqueness of the half-exponent radial presentation.

## 5. Exact restrictions

### 5.1. Positional base is not camera width

The quadratic-domain crosswalk is downstream of the tower and proves an
equivalence of radial-presentation conditions. It does not define mass, and it
does not prove

$$
b^{-k}=n^{-1}
$$

for individual samples, and it does not assert `b = camera`.

### 5.2. Camera universality is radial

`NCG-OPR-004` is universally quantified over `camera : ℕ`; every camera obeys
the same radial-presentation uniqueness law. The theorem does not assert:

- definitional equality of distinct raw camera sums;
- equality of every pair of temporal resonance sets;
- existence, infinitude, or enumeration of resonance times;
- a convergence rate uniform in the camera.

### 5.3. Analytic boundary crosswalk

`NCG-EQV-007` and `NCG-EQV-008` are explicitly restricted to:

- camera `3`;
- `s ∈ Analytic.canonicalStrip`;
- `Analytic.canonicalStrip = {s | 0 < s.re ∧ s.re < 1}`.

These premises are part of the statements and must be preserved in citations.

### 5.4. Odd-prime camera lemmas

Balanced-residue equivalences, finite bracket-chart identities, bracket-series
factorizations, and normalized camera comparison retain their `Nat.Prime` and
`Odd` hypotheses. These local hypotheses do not propagate to positional
quadratic rigidity or the universal real zero-set theorem.

### 5.5. Degenerate total cameras

The generic camera uses

```lean
halfRange camera = (camera - 1) / 2
```

with natural-number subtraction and division. Hence:

| `camera` | `halfRange camera` | Generic status |
|---:|---:|---|
| `0` | `0` | degenerate |
| `1` | `0` | degenerate |
| `2` | `0` | degenerate |
| odd `camera ≥ 3` | `(camera - 1)/2` | symmetric full-width window |
| even `camera ≥ 4` | `camera/2 - 1` | valid additive detector of width `camera - 1` |

The arithmetic binary-center construction is nondegenerate, but it is not
definitionally the generic finite camera at width `2`.

## 6. Nonclaims

This release does not claim:

- that the native operator has a free `sigma` input;
- that raw deformation-boundary closure alone forces `sigma = 1/2`;
- that internal energy vanishes when the vector resultant vanishes;
- that finite cutoff zeros are required for boundary closure;
- that the critical infinite state is an ordinary square-summable vector;
- that every natural camera is a complete positional residue system;
- that mass is supplied by the operator or by its zero predicate;
- that prime bases cause the quadratic exponent;
- that the curvature route is a premise of the terminal factorization;
- that any excluded historical extension is false.

The authoritative statement of every result is its elaborated Lean type.
