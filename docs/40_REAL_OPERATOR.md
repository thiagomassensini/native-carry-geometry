# The Real Carry Operator

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

## 2. Integer-indexed rotating state

For a positive integer `n`,

$$
u_{\sigma,t}(n)
=
n^{-\sigma}
\bigl(\cos(-t\log n),\sin(-t\log n)\bigr).
$$

The Lean function is total on `ℤ`; it returns zero for nonpositive inputs.

`NCG-REA-002` states, under `0 < n`,

$$
E(u_{\sigma,t}(n))=n^{-2\sigma}.
$$

The time parameter rotates direction and does not alter energy.

## 3. Real energy-compatible domain

`RealCarryEnergyCompatible sigma time` requires:

$$
E(u_{\sigma,t}(n))=n^{-1}
\qquad\text{for every integer }n>1.
$$

The index `n=1` is excluded because its energy is one for every `sigma`.

`NCG-REA-003` proves:

```lean
RealCarryEnergyCompatible sigma time ↔
  sigma = (1 : ℝ) / 2
```

No hypothesis on `time` occurs in this radial selection.

## 4. Generic finite camera

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

`finiteRealCarryOperator camera cutoff sigma time` applies this construction
to `realCarryState sigma time`.

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

The admissible finite zero includes both energy compatibility and a zero
resultant. `NCG-OPR-003` factors it as:

```lean
IsFiniteRealCarryOperatorZero camera cutoff sigma time ↔
  sigma = 1 / 2 ∧
    quadraticEnergy
      (criticalFiniteRealCarryOperator camera cutoff time) = 0
```

Visible energy must not be confused with the sum of energies of the individual
terms. A vector sum may vanish while its summands remain nonzero.

## 6. Boundary closure

The infinite operator is represented by a convergence predicate:

```lean
def BoundaryConvergesToZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  Tendsto
    (fun cutoff =>
      finiteRealCarryOperator camera cutoff sigma time)
    atTop (nhds 0)
```

No finite cutoff is required to be exactly zero.

A boundary resonance fixes the radial exponent:

```lean
def IsBoundaryResonance
    (camera : ℕ) (time : ℝ) : Prop :=
  BoundaryConvergesToZero camera (1 / 2) time
```

The complete zero predicate is:

```lean
def IsRealCarryOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  RealCarryEnergyCompatible sigma time ∧
    BoundaryConvergesToZero camera sigma time
```

The distinction is semantic and formal: boundary closure is one component;
the operator zero retains its domain.

## 7. Camera cases

The finite operator is total for all natural cameras.

- `camera = 0, 1, 2`: `halfRange = 0`, so the generic camera is degenerate.
- odd `camera ≥ 3`: the window has exactly `camera` positions around each
  aligned center when the center is included.
- even `camera ≥ 4`: the bracket uses `camera - 1` positions.
- odd prime cameras additionally admit the balanced-residue and finite-prefix
  identities used by the analytic layer.

The universal zero-set theorem includes the degenerate cases because its
camera parameter is unrestricted. This totality must not be read as a claim
that every natural width supplies a nondegenerate physical observation rule.

## 8. No hidden operator object

The phrase “real carry operator” denotes the structured family consisting of
states, finite resultants, a boundary limit, an admissible domain, resonances,
and the complete zero predicate. The release does not claim a separately
constructed total linear map whose value is an already-evaluated infinite
limit.
