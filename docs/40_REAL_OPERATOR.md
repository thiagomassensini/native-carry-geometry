# The Native Carry Operator in Real Coordinates

## 1. Real state space

The state space is

```lean
abbrev RealCarryPlane := ℝ × ℝ
```

with quadratic energy

$$
E(x,y)=x^2+y^2.
$$

The unit rotation direction is

$$
d(\theta)=(\cos\theta,\sin\theta).
$$

`NCG-REA-001` proves `E(d(theta)) = 1`.

## 2. Native integer-indexed rotating state

For a positive integer `n`,

$$
u_t(n)
=
n^{-1/2}
\bigl(\cos(-t\log n),\sin(-t\log n)\bigr).
$$

The Lean definition is `nativeRealCarryState time n`. It reads its amplitude
from `Measure.nativeTowerAmplitude`; it is total on `ℤ` and returns zero for
nonpositive inputs.

Its energy is inverse-integer mass by construction:

```lean
quadraticEnergy (nativeRealCarryState time n) = (n : ℝ)⁻¹
```

## 3. Secondary radial deformation

For norm and rigidity comparisons, the repository also exposes

$$
u_{\sigma,t}(n)
=n^{-\sigma}
\bigl(\cos(-t\log n),\sin(-t\log n)\bigr)
$$

as `radialDeformationState sigma time n`. The old public name
`realCarryState` is retained as a compatibility alias for this deformation.

`NCG-REA-005` states, under `0 < n`,

$$
E(u_{\sigma,t}(n))=n^{-2\sigma}.
$$

The time parameter rotates direction and does not alter energy.

`RadialDeformationRepresentsNativeMass sigma time` asks whether the ambient
deformation reproduces the mass already fixed by the native tower for all
`n > 1`.

The index `n=1` is excluded because its energy is one for every `sigma`.

`NCG-REA-006` proves:

```lean
RadialDeformationRepresentsNativeMass sigma time ↔
  sigma = (1 : ℝ) / 2
```

No hypothesis on `time` occurs in this presentation rigidity. This theorem
does not select mass for the native state; the native state was already built
from that mass.

## 4. Native finite camera

Let

$$
h_c=\left\lfloor\frac{c-1}{2}\right\rfloor,
\qquad
q_{c,j}=c(j+1).
$$

For a state function `f`, the generic finite operator is

$$
\begin{aligned}
\operatorname{FiniteOp}_{c,M}(f)
&=
\sum_{n=1}^{h_c}f(n)\\
&\quad+
\sum_{j=0}^{M-1}\sum_{r=1}^{h_c}
\left[
f(q_{c,j}-r)-2f(q_{c,j})+f(q_{c,j}+r)
\right].
\end{aligned}
$$

`finiteNativeRealCarryOperator camera cutoff time` applies this construction
to `nativeRealCarryState time`. It has no `sigma` argument.

`finiteRadialDeformation camera cutoff sigma time` is the secondary family;
`finiteRealCarryOperator` remains its compatibility alias.

`NCG-OPR-001` proves that every additive map commutes with the finite operator.
This is the formal naturality used by the coordinate equivalence.

## 5. Visible energy and finite zeros

Visible energy is the norm square of the final vector resultant:

$$
E_{\mathrm{vis}}(R)=R_1^2+R_2^2.
$$

`NCG-OPR-002` proves:

```lean
quadraticEnergy u = 0 ↔ u = 0
```

The canonical finite native zero is:

```lean
IsFiniteNativeCarryOperatorZero camera cutoff time
```

The ambient relation is
`RadialChartRepresentsFiniteNativeZero camera cutoff sigma time`.
`NCG-OPR-008` factors that representation as:

```lean
RadialChartRepresentsFiniteNativeZero camera cutoff sigma time ↔
  sigma = 1 / 2 ∧
    IsFiniteNativeCarryOperatorZero camera cutoff time
```

Visible energy must not be confused with the sum of energies of the individual
terms. A vector sum may vanish while its summands remain nonzero.

## 6. Native boundary closure

The infinite operator is represented by a convergence predicate:

```lean
def NativeBoundaryConvergesToZero
    (camera : ℕ) (time : ℝ) : Prop :=
  Tendsto
    (fun cutoff =>
      finiteNativeRealCarryOperator camera cutoff time)
    atTop (nhds 0)
```

No finite cutoff is required to be exactly zero.

The canonical operator-zero predicate is literally this native boundary:

```lean
abbrev IsNativeCarryOperatorZero
    (camera : ℕ) (time : ℝ) : Prop :=
  NativeBoundaryConvergesToZero camera time
```

`IsBoundaryResonance` and the older coordinate-labelled
`IsNativeRealCarryOperatorZero` are definitionally equal legacy-compatibility aliases.

The ambient deformation has only a cancellation predicate,
`RadialChartCancelsAt camera sigma time`. At `sigma = 1/2`, Lean proves
that chart cancellation is equivalent to the native boundary. Away from the
mass-preserving shell it is not classified as an operator zero.

## 7. Camera cases

The finite operator is total for all natural cameras.

- `camera = 0, 1, 2`: `halfRange = 0`, so the generic camera is degenerate.
- odd `camera ≥ 3`: the window has exactly `camera` positions around each
  aligned center when the center is included.
- even `camera ≥ 4`: the bracket uses `camera - 1` positions.
- odd prime cameras additionally admit the balanced-residue and finite-prefix
  identities used by the analytic layer.

The universal radial-chart representation theorem includes the degenerate cases because
its camera parameter is unrestricted. This totality must not be read as a claim
that every natural width supplies a nondegenerate physical observation rule.

## 8. No hidden operator object

The phrase “real carry operator” denotes real coordinates for the mass-built
native state, its finite resultants, and its one boundary zero. Complex
coordinates describe the same object. The radial deformation is a tool for
varying amplitude and quadratic norm, not an input of another operator. The release does not
claim a separately constructed total linear map whose value is an
already-evaluated infinite limit.
