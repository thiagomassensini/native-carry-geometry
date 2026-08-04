# Native Zeros and Radial-Presentation Factorization

## 1. Definitions

Native boundary closure is:

```lean
def NativeBoundaryConvergesToZero
    (camera : ℕ) (time : ℝ) : Prop :=
  Tendsto
    (fun cutoff =>
      finiteNativeRealCarryOperator camera cutoff time)
    atTop (nhds 0)
```

Resonance and the native operator zero are this same predicate:

```lean
def IsBoundaryResonance
    (camera : ℕ) (time : ℝ) : Prop :=
  NativeBoundaryConvergesToZero camera time

abbrev IsNativeRealCarryOperatorZero
    (camera : ℕ) (time : ℝ) : Prop :=
  NativeBoundaryConvergesToZero camera time
```

The auxiliary radial deformation has its own closure predicate. The old public
name `IsRealCarryOperatorZero` is retained as an alias for the proposition that
the deformation both represents the native mass and closes to zero:

```lean
def IsRadialDeformationPresentationZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  RadialDeformationRepresentsNativeMass sigma time ∧
    RadialDeformationBoundaryConvergesToZero camera sigma time
```

This conjunction is about representation in a larger chart. It is not the
definition of the native operator and does not inject mass into it.

## 2. Terminal theorem

`NCG-OPR-004`, the **Radial Presentation Factorization Theorem**, is:

```lean
theorem isRealCarryOperatorZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    IsRealCarryOperatorZero camera sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsBoundaryResonance camera time
```

Equivalently, the radial presentations of native zeros form, for each camera,

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
\operatorname{NativeBoundaryConvergesToZero}(c,t)
\right\}.
$$

## 3. Proof dependency

The native object was already constructed before this proof. The forward
direction for its radial presentation:

1. opens the radial-presentation predicate into mass representation and
   deformation boundary closure;
2. uses `NCG-AMP-006` at positional base `2` to recover positional mass
   compatibility;
3. applies `NCG-AMP-003` to obtain `sigma = 1/2`;
4. substitutes the exponent;
5. uses the proved half-chart identity to recognize the native boundary
   resonance.

The reverse direction:

1. receives `sigma = 1/2` and a resonance;
2. constructs positional mass compatibility with `NCG-AMP-003`;
3. transports it to real energy compatibility with `NCG-AMP-006`;
4. transports native boundary closure back to the half-exponent deformation
   chart and pairs the two facts.

Using positional base `2` supplies one witness for radial-chart rigidity. It
does not build the native mass, identify base `2` with camera, or give the
operator a radial input.

## 4. Corollaries

`NCG-OPR-005`, **Radial-Presentation Uniqueness**, states:

```lean
IsRealCarryOperatorZero camera sigma time →
  sigma = 1 / 2
```

`NCG-OPR-006`, **Off-Shell Nonrepresentation**, states:

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

Therefore the radial-presentation law is global across:

- odd and even cameras;
- prime and composite cameras;
- total degenerate cameras.

This means that camera width does not alter which radial chart represents the
native tower. It does not mean:

- `NativeBoundaryConvergesToZero c` is definitionally equal to
  `NativeBoundaryConvergesToZero d`;
- `IsBoundaryResonance c` and `IsBoundaryResonance d` have identical temporal
  extension;
- a resonance exists for every camera;
- the theorem classifies or enumerates resonance times.

The temporal component is isolated in the native resonance predicate.

## 6. Degenerate cameras

Because the generic half-range is `(camera - 1) / 2`, cameras `0`, `1`, and
`2` are degenerate in the generic finite family. The theorem remains correct
for them because all definitions are total.

An auditor must not cite the generic `camera = 2` instance as the
nondegenerate binary adjacent-center construction. The latter is formalized
separately in `Arithmetic/BinaryCenter.lean`.

## 7. Independence from alternative proof routes

The native construction and the proof of `NCG-OPR-004` do not use:

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

The primary native consequence is:

$$
\operatorname{IsNativeRealCarryOperatorZero}(3,t)
\iff
\operatorname{IsNativeCanonicalCarryOperatorZero}(t).
$$

Within the canonical strip, `NCG-EQV-008` additionally identifies the real and
analytic radial-presentation predicates. Consequently, `NCG-EQV-009`
transports presentation uniqueness:

$$
\operatorname{IsCanonicalCarryOperatorZero}(s)
\Longrightarrow
\operatorname{Re}(s)=\frac12.
$$

This last ambient-chart consequence retains both the camera-three and
canonical-strip scope of the crosswalk.
