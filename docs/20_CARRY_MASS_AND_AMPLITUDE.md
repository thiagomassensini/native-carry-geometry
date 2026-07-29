# Carry Mass and Quadratic Amplitude

## 1. Uniform carry probability

At depth `k` in a positive base `b`, the residue space has `b^k` elements. The
formal event `uniformCarryEvent (b^k)` is the distinguished singleton
congruence class. Its finite uniform probability is

$$
\frac{1}{b^k}=b^{-k}.
$$

Lean proves:

```lean
theorem uniformCarryEvent_probability
    (b k : ℕ) (hb : 0 < b) :
    uniformFiniteProbability
        (uniformCarryEvent (b ^ k) (pow_pos hb k)) =
      carryMass b k
```

This is `NCG-PRB-001`. It uses positivity of the base, not primality.

The theorem is a cardinality statement about one specified residue class. The
interpretation of zero residue as the depth-`k` carry event is supplied by:

```lean
residueAtDepth b k n = 0 ↔ b ^ k ∣ n
```

## 2. Mass and critical amplitude

The public quantities are:

$$
\begin{aligned}
\operatorname{carryMass}(b,k)&=b^{-k},\\
\operatorname{criticalAmplitude}(b,k)&=b^{-k/2},\\
\operatorname{deformedAmplitude}(b,\sigma,k)&=b^{-k\sigma}.
\end{aligned}
$$

`NCG-MAS-001` proves the local amplitude–mass identity:

```lean
(criticalAmplitude b k) ^ 2 = carryMass b k
```

`NCG-MAS-002` transports carry mass across the equality between effective
depth and canonical-center depth for the odd-prime balanced incidence
geometry.

## 3. Local quadratic rigidity

The square of the deformed amplitude is the mass weight of the deformed
branch:

```lean
theorem deformedAmplitude_sq_eq_massWeight ...
```

This is `NCG-AMP-001`.

For `1 < b` and `0 < k`, comparison with carry mass is rigid:

```lean
theorem deformedAmplitude_sq_eq_carryMass_iff
    (b k : ℕ) (hb : 1 < b) (hk : 0 < k) (sigma : ℝ) :
    (deformedAmplitude b sigma k) ^ 2 = carryMass b k ↔
      sigma = (1 : ℝ) / 2
```

This is `NCG-AMP-002`. Algebraically,

$$
b^{-2k\sigma}=b^{-k}
\iff
\sigma=\frac12.
$$

The positive-depth hypothesis is necessary: at depth zero both sides are one
for every exponent.

## 4. Global positional domain

`PositionalMassCompatible b sigma` requires the local energy–mass identity at
every positive depth. The global rigidity theorem is:

```lean
theorem positionalMassCompatible_iff
    (b : ℕ) (hb : 1 < b) (sigma : ℝ) :
    PositionalMassCompatible b sigma ↔
      sigma = (1 : ℝ) / 2
```

This is `NCG-AMP-003`. It holds for arbitrary natural bases greater than one,
including composite bases.

## 5. Radial branch saturation

The normalized branch energy is

$$
\operatorname{radialBranchEnergy}(b,\sigma)
=
(b-1)\sum_{k\ge0}
\operatorname{massWeight}(b,\sigma,k+1).
$$

Within its positive-`sigma` convergence regime:

| ID | Declaration | Result |
|---|---|---|
| `NCG-AMP-004` | `radialBranchEnergy_eq_one_iff` | saturation equals one iff `sigma = 1/2` |
| `NCG-AMP-005` | `radialBranchSaturation_base_independent` | any two bases `> 1` have the same saturation locus |
| `NCG-AMP-007` | `radialBranchEnergy_half_eq_one` | the critical branch saturates |
| `NCG-AMP-008` | `radialBranchEnergy_half_ne_zero` | the critical branch is nondegenerate |

These are saturation statements. They are not definitions of an operator zero.

## 6. Quadratic-domain crosswalk

The positional description uses depth weights `b⁻ᵏ`. The real state indexed by
an integer uses energy `n^(-2 sigma)` and compares it with `n⁻¹`. These weights
are not identified sample by sample.

The formal bridge is:

```lean
theorem positionalMassCompatible_iff_realEnergyCompatible
    (b : ℕ) (hb : 1 < b) (sigma time : ℝ) :
    PositionalMassCompatible b sigma ↔
      Operator.RealCarryEnergyCompatible sigma time
```

This is `NCG-AMP-006`. Both sides are equivalent to `sigma = 1/2`; their
equivalence is a crosswalk between admissible domains, not an equality of
their indexing schemes.

## 7. Dependency role

The terminal real zero-set theorem deliberately passes through
`NCG-AMP-006`, using base `2` as one valid positional witness. This makes the
carry-to-operator dependency explicit in the proof term. It does not make the
finite camera width equal to base `2`, and it does not give base `2` a causal
privilege: `NCG-AMP-003` holds for every base greater than one.
