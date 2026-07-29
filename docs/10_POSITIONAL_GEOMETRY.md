# Positional Carry Geometry

## 1. Canonical decomposition

For a positive base `b`, a depth `k`, and an integer `n`, Lean's Euclidean
division supplies a unique quotient–residue pair:

$$
n=r+b^kq,
\qquad
0\le r<b^k.
$$

The public theorem is:

```lean
theorem positionalDecompositionAtDepth_existsUnique
    (b k n : ℕ) (hb : 0 < b) :
    ∃! qr : ℕ × ℕ,
      qr.2 + b ^ k * qr.1 = n ∧ qr.2 < b ^ k
```

This is `NCG-POS-001`.

The distinguished carry event at depth `k` is zero residue:

```lean
residueAtDepth b k n = 0 ↔ b ^ k ∣ n
```

This is the Positional Carry-Event Divisibility Criterion,
`NCG-POS-004`.

## 2. Maximal positional depth

For `1 < b` and `0 < n`, `positionalDepth b n` is the maximal exponent for
which `b^k` divides `n`. The two public statements are:

```lean
theorem positionalDepth_factorization_existsUnique
    (b n : ℕ) (hb : 1 < b) (hn : 0 < n) :
    ∃! m : ℕ,
      n = b ^ positionalDepth b n * m ∧ ¬b ∣ m
```

and

```lean
theorem positionalDepth_spec
    (b n : ℕ) (hb : 1 < b) (hn : 0 < n) :
    b ^ positionalDepth b n ∣ n ∧
      ¬b ^ (positionalDepth b n + 1) ∣ n
```

They are `NCG-POS-002` and `NCG-POS-003`. Both remain valid for composite
bases.

## 3. Binary adjacent-center geometry

The binary module studies odd legs `n ≥ 3`. It selects the unique adjacent
center divisible by `4` and proves:

| ID | Declaration | Content |
|---|---|---|
| `NCG-BIN-001` | `four_dvd_binaryCenter` | the selected center is divisible by `4` |
| `NCG-BIN-002` | `binaryCenter_unique` | uniqueness among adjacent centers divisible by `4` |
| `NCG-BIN-003` | `oddLeg_equiv_binaryIncidence` | bijection between odd legs and binary incidences |
| `NCG-BIN-004` | `binaryEffectiveDepth_eq_centerDepth` | effective depth equals the center's `2`-adic depth |

The hypotheses `Odd n` and, where needed, `3 ≤ n` are part of the theorems.

This arithmetic construction must not be confused with the generic finite
camera at width `2`, whose half-range is zero.

## 4. Balanced odd-prime residue geometry

For an odd prime base, the balanced offset set represents all nonzero residue
classes symmetrically. The public statements are:

| ID | Declaration | Principal hypotheses |
|---|---|---|
| `NCG-BAL-001` | `card_balancedOffsets` | `Odd b` |
| `NCG-BAL-002` | `balancedOffset_equiv_nonzeroResidue` | `Nat.Prime b`, `Odd b` |
| `NCG-BAL-003` | `centerOffsetDecomposition_existsUnique` | `Nat.Prime b`, `Odd b`, nonmultiple leg |

The cardinality theorem uses only oddness. The equivalence and global
center–offset decomposition retain primality. No broader hypothesis is claimed
by the public API.

## 5. Carrying offset and center depth

For a nonmultiple of an odd prime base, there is one balanced offset whose
subtraction reaches a divisible center:

```lean
(b : ℤ) ∣ (n.1 - a.1) ↔
  a = canonicalOffset b hb hbodd n
```

This is `NCG-DEP-001`.

The maximum carry depth across all balanced offsets is exactly the depth of
that canonical center:

```lean
effectiveDepth b n.1 =
  centerDepth b hb hbodd n
```

This is `NCG-DEP-002`.

## 6. Logical role

The positional layer determines the vertical coordinate before any real
rotation, bracket, camera cutoff, or boundary limit is introduced. It does not
yet define an operator zero. Its output is the depth used by the mass and
amplitude layer.
