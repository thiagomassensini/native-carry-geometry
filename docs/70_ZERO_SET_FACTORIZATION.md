# Real Carry Operator Zero-Set Factorization

## 1. Definitions

Boundary closure is:

```lean
def BoundaryConvergesToZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  Tendsto
    (fun cutoff =>
      finiteRealCarryOperator camera cutoff sigma time)
    atTop (nhds 0)
```

Resonance is boundary closure on the quadratic carry shell:

```lean
def IsBoundaryResonance
    (camera : ℕ) (time : ℝ) : Prop :=
  BoundaryConvergesToZero camera (1 / 2) time
```

The complete real zero predicate retains both domain and closure:

```lean
def IsRealCarryOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  RealCarryEnergyCompatible sigma time ∧
    BoundaryConvergesToZero camera sigma time
```

## 2. Terminal theorem

`NCG-OPR-004`, the **Real Carry Operator Zero-Set Factorization Theorem**, is:

```lean
theorem isRealCarryOperatorZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    IsRealCarryOperatorZero camera sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsBoundaryResonance camera time
```

Equivalently, for each natural camera,

$$
Z_c
=
\left\{\frac12\right\}\times\mathcal R_c,
$$

where

$$
\mathcal R_c
=
\left\{
t\in\mathbb R:
\operatorname{BoundaryConvergesToZero}
\left(c,\frac12,t\right)
\right\}.
$$

## 3. Proof dependency

The forward direction:

1. opens the complete zero into energy compatibility and boundary closure;
2. uses `NCG-AMP-006` at positional base `2` to recover positional mass
   compatibility;
3. applies `NCG-AMP-003` to obtain `sigma = 1/2`;
4. substitutes the exponent;
5. recognizes the remaining boundary closure as resonance.

The reverse direction:

1. receives `sigma = 1/2` and a resonance;
2. constructs positional mass compatibility with `NCG-AMP-003`;
3. transports it to real energy compatibility with `NCG-AMP-006`;
4. pairs that domain proof with the same boundary closure.

Using positional base `2` in this proof supplies one valid witness to a
base-independent domain. It does not identify base `2` with the arbitrary
camera parameter.

## 4. Corollaries

`NCG-OPR-005`, **Radial Confinement**, states:

```lean
IsRealCarryOperatorZero camera sigma time →
  sigma = 1 / 2
```

`NCG-OPR-006`, **Off-Shell Nonvanishing**, states:

```lean
sigma ≠ 1 / 2 →
  ¬ IsRealCarryOperatorZero camera sigma time
```

Neither corollary assumes primality, parity, nondegeneracy, or existence of a
resonance.

## 5. Meaning of global camera scope

The theorem has one universally quantified statement:

```text
for every camera : ℕ
```

Therefore the radial admissibility law is global across:

- odd and even cameras;
- prime and composite cameras;
- total degenerate cameras.

This means that camera width does not alter the radial shell of a complete
operator zero. It does not mean:

- `BoundaryConvergesToZero c` is definitionally equal to
  `BoundaryConvergesToZero d`;
- `IsBoundaryResonance c` and `IsBoundaryResonance d` have identical temporal
  extension;
- a resonance exists for every camera;
- the theorem classifies or enumerates resonance times.

The temporal component is isolated, not left as a hidden radial obligation.

## 6. Degenerate cameras

Because the generic half-range is `(camera - 1) / 2`, cameras `0`, `1`, and
`2` are degenerate in the generic finite family. The theorem remains correct
for them because all definitions are total.

An auditor must not cite the generic `camera = 2` instance as the
nondegenerate binary adjacent-center construction. The latter is formalized
separately in `Arithmetic/BinaryCenter.lean`.

## 7. Independence from alternative proof routes

The proof of `NCG-OPR-004` does not use:

- a completed boundary-flow operator;
- a global energy reconstruction;
- a trace reconstruction;
- a source-state realization;
- a self-adjoint realization;
- spectral pencils;
- a second curvature-based confinement proof.

Those constructions may answer stronger or different questions. They are not
retroactive premises of this theorem.

## 8. Analytic consequence

Within the canonical strip, `NCG-EQV-008` identifies the full camera-three real
zero predicate with the full canonical analytic zero predicate. Consequently,
`NCG-EQV-009` transports radial confinement:

$$
\operatorname{IsCanonicalCarryOperatorZero}(s)
\Longrightarrow
\operatorname{Re}(s)=\frac12.
$$

This consequence retains both the camera-three and canonical-strip scope of
the crosswalk.
