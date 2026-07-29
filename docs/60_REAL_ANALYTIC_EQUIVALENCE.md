# Real–Analytic Presentation Equivalence

## 1. Coordinate equivalence

The map

$$
J:\mathbb R^2\longrightarrow\mathbb C,
\qquad
J(x,y)=x+iy,
$$

is implemented as an additive equivalence:

```lean
def complexCoordinates :
    Operator.RealCarryPlane ≃+ ℂ
```

It is a change of coordinates, not an additional dynamical operation.

The public finite-coordinate results are:

| ID | Declaration | Content |
|---|---|---|
| `NCG-EQV-001` | `complexCoordinates_injective` | faithful encoding |
| `NCG-EQV-002` | `normSq_complexCoordinates` | preservation of quadratic energy |
| `NCG-EQV-003` | `complexCoordinates_finiteOperator` | finite-operator naturality |
| `NCG-EQV-004` | `finiteOperator_eq_zero_iff_complexCoordinates_eq_zero` | finite zero preservation in both directions |

In particular,

$$
R=0\iff J(R)=0.
$$

## 2. State identity

The canonical complex parameter is

```lean
def canonicalParameter (sigma time : ℝ) : ℂ :=
  ⟨sigma, time⟩
```

For every positive integer input, `NCG-EQV-005` proves:

```lean
complexCoordinates (realCarryState sigma time n) =
  powerMonomial (canonicalParameter sigma time) n
```

The hypothesis `0 < n` is explicit. The total real-state definition is zero on
nonpositive integers, while the power-monomial identity is used only on the
positive index set of the camera.

## 3. Finite operator identity

For an odd prime camera, `NCG-EQV-006` proves:

```lean
complexCoordinates
    (finiteRealCarryOperator camera cutoff sigma time) =
  finiteBracketChart camera cutoff
    (powerMonomial (canonicalParameter sigma time))
```

This is an equality of the complete finite resultants. Its prime and oddness
hypotheses arise from the balanced-camera chart identity.

## 4. Boundary representation theorem

The limit crosswalk is:

```lean
theorem boundaryConvergesToZero_iff_canonicalCarryContinuation_eq_zero
    {s : ℂ} (hs : s ∈ Analytic.canonicalStrip) :
    Operator.BoundaryConvergesToZero 3 s.re s.im ↔
      Analytic.canonicalCarryContinuation s = 0
```

This is `NCG-EQV-007`.

Two restrictions are part of the theorem:

1. the real boundary camera is exactly `3`;
2. `s` belongs to the open canonical strip
   `0 < s.re ∧ s.re < 1`.

The theorem is bidirectional. It identifies boundary closure in the real
presentation with scalar cancellation of the canonical analytic
representative in this domain.

## 5. Full zero-predicate identity

The complete analytic predicate is:

```lean
def IsCanonicalCarryOperatorZero (s : ℂ) : Prop :=
  Operator.RealCarryEnergyCompatible s.re s.im ∧
    Analytic.canonicalCarryContinuation s = 0
```

The energy condition is not optional metadata. It is the positional carry
domain transported with the operator.

`NCG-EQV-008` proves:

```lean
theorem isRealCarryOperatorZero_iff_isCanonicalCarryOperatorZero
    {s : ℂ} (hs : s ∈ Analytic.canonicalStrip) :
    Operator.IsRealCarryOperatorZero 3 s.re s.im ↔
      IsCanonicalCarryOperatorZero s
```

The proof is a typed conjunction of:

- identical real energy compatibility on both sides;
- the boundary equivalence `NCG-EQV-007`.

It does not replace a full operator zero by a bare scalar equation.

## 6. Analytic radial confinement

`NCG-EQV-009` states:

```lean
theorem canonicalCarryOperatorZero_re_eq_half
    {s : ℂ} (hs : s ∈ Analytic.canonicalStrip)
    (hzero : IsCanonicalCarryOperatorZero s) :
    s.re = (1 : ℝ) / 2
```

The proof transports the full analytic zero to the real camera-three
predicate using `NCG-EQV-008`, then applies the universal real confinement
corollary `NCG-OPR-005`.

This theorem confines the complete analytic operator predicate. It does not
claim that every unconstrained scalar cancellation outside the predicate is an
operator zero.

## 7. What is and is not camera-independent

The repository proves three different statements:

1. every natural real camera obeys the same radial zero-set factorization;
2. odd prime normalized analytic cameras give the same canonical
   representative in the strip;
3. camera `3` is connected bidirectionally to that representative at the
   boundary.

These statements compose coherently, but they are not an assertion that every
raw finite or boundary formula is definitionally identical for every natural
camera.
