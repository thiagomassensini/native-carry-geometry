# Centered Brackets and Radial Curvature

## 1. Centered second difference

For a function from integers to an additive commutative group,

$$
\Delta_r^2 f(c)
=
f(c-r)-2f(c)+f(c+r).
$$

The implementation is polymorphic:

```lean
def centeredSecondDifference
    (f : ℤ → A) (center radius : ℤ) : A :=
  f (center - radius) - (2 • f center) + f (center + radius)
```

The public algebraic laws are:

| ID | Declaration | Content |
|---|---|---|
| `NCG-BRK-001` | `centeredSecondDifference_neg_radius` | invariance under `r ↦ -r` |
| `NCG-BRK-002` | `centeredSecondDifference_add` | additivity in the observed function |

## 2. Saturated bracket

For half-width `h`,

$$
\mathcal B_h f(c)
=
\sum_{r=1}^{h}\Delta_r^2 f(c).
$$

This is `Bracket.saturatedBracket`. It is defined for any natural half-width
and any additive commutative-group target.

For an odd prime camera, the balanced residue bracket is exactly this
symmetric-radius sum:

```lean
theorem balancedBracket_eq_saturatedBracket
    (camera : ℕ) (hprime : Nat.Prime camera) (hodd : Odd camera) ...
```

This is `NCG-BRK-003`. Its prime and oddness hypotheses belong to the
identification of the balanced residue presentation with the symmetric
presentation; they are not required to define the generic saturated bracket.

## 3. Finite camera identities

`NCG-BRK-004`, `finiteBracketCancellation`, is a finite ring identity:

```text
direct channel − bracket channel = surviving center channel.
```

It is algebraic and does not require a limit, an analytic parameter, or an
operator-zero hypothesis.

For an odd prime camera, `NCG-BRK-005` gives the interval-prefix form:

$$
\operatorname{finiteBracketChart}_{c,M}(f)
=
\sum_{n=1}^{cM+h_c}f(n)
-
c\sum_{j=0}^{M-1}f(c(j+1)).
$$

Here

$$
h_c=\left\lfloor\frac{c-1}{2}\right\rfloor.
$$

## 4. Radial curvature

The curvature layer applies the balanced second-difference mechanism to a
radial deformation. It records a local sign test independent of the native chart-representation proof.

| ID | Declaration | Exact scope |
|---|---|---|
| `NCG-CUR-001` | `balancedRadialCurvature_eq_half_pairSum` | odd camera |
| `NCG-CUR-002` | `balancedRadialCurvature_pos_of_pos` | odd prime camera, positive displacement, center outside the half-range |
| `NCG-CUR-003` | `balancedRadialCurvature_neg_of_neg` | odd prime camera, `-1 < delta < 0`, admissible center |
| `NCG-CUR-004` | `balancedRadialCurvature_eq_zero_iff` | odd prime camera, `0 < sigma`, admissible center |

The final detector-rigidity statement is

$$
\operatorname{balancedRadialCurvatureAtSigma}(c,\sigma,x)=0
\iff
\sigma=\frac12
$$

under its stated hypotheses.

## 5. Logical status

Curvature confirms the same mass-preserving radial coordinate by a sign
argument, but its vanishing is the null locus of an auxiliary detector, not an
operator zero. It is not a premise of `NCG-OPR-007`.

The native chart-representation factorization uses upstream quadratic mass
rigidity and the half-chart identity directly. No implication from boundary
cancellation to curvature is required for the one-operator theorem.
