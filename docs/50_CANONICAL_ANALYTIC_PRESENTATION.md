# Canonical Analytic Presentation

## 1. Purpose

The analytic layer is constructed from the same finite centered-bracket
algebra used by the real presentation. It stores the rotating `ℝ²` samples
as complex coordinates and then continues the ambient radial chart. It does
not construct another operator or another zero predicate.

The complex parameter is written

$$
s=\sigma+it,
$$

so that the power monomial at a positive integer is

$$
n^{-s}
=
n^{-\sigma}
\bigl(\cos(-t\log n)+i\sin(-t\log n)\bigr).
$$

## 2. Finite bracket chart

For an odd prime camera `c`, cutoff `M`, and complex parameter `s`,
`NCG-ANL-001` proves:

$$
\begin{aligned}
\operatorname{FiniteBracketChart}_{c,M}(s)
&=
\operatorname{Prefix}_{cM+h_c}(s)\\
&\quad-
c^{1-s}\operatorname{Prefix}_M(s),
\end{aligned}
$$

where

$$
h_c=\frac{c-1}{2}.
$$

The exact Lean statement retains both `Nat.Prime camera` and `Odd camera`.

## 3. Bracket series

The centered second difference gives two orders of local decay. The resulting
bracket series converges in the half-plane

$$
-1<\operatorname{Re}(s).
$$

`NCG-ANL-002` states convergence of finite bracket charts to
`bracketSeries camera s` for an odd prime camera and `-1 < s.re`.

`NCG-ANL-003` proves that the bracket series is analytic on this half-plane.
Its public statement requires primality of the camera.

## 4. Canonical strip

The narrower domain used for camera normalization and the real–analytic
boundary crosswalk is:

```lean
abbrev canonicalStrip : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < 1}
```

This is an open strip. It must not be replaced in citations by an unstated
larger domain.

## 5. Camera normalization

The camera factor is

$$
F_c(s)=1-c^{\,1-s}.
$$

For a prime camera and `s` in the canonical strip, `NCG-ANL-004` proves

$$
F_c(s)\ne0.
$$

The normalized bracket chart is therefore well-defined. For any two odd prime
cameras, `NCG-ANL-005` proves:

$$
\operatorname{NormalizedChart}_{c_1}(s)
=
\operatorname{NormalizedChart}_{c_2}(s)
$$

inside the canonical strip.

This is the exact camera-independence theorem of the analytic atlas. It does
not quantify over arbitrary composite or even cameras.

## 6. Canonical representative

After normalized odd-prime cameras have been proved equal, the implementation
uses camera `3` to name their common representative:

```lean
abbrev canonicalCarryContinuation (s : ℂ) : ℂ := ...
```

Camera `3` is therefore a chosen representative after compatibility, not the
source of the quadratic shell.

The principal theorems are:

| ID | Declaration | Content |
|---|---|---|
| `NCG-ANL-006` | `bracketSeries_eq_factor_mul_canonicalCarryContinuation` | camera bracket series equals the nonzero factor times the canonical representative |
| `NCG-ANL-007` | `analyticOnNhd_canonicalCarryContinuation` | analyticity on the canonical strip |
| `NCG-ANL-008` | `bracketSeries_zero_iff_canonicalCarryContinuation_zero` | any odd prime camera represents the same ambient chart-cancellation locus in the strip |

`NCG-ANL-008` is a statement about cancellation of the ambient bracket chart.
It is not an `OperatorZero` theorem. The native operator readout is obtained
by restricting the same coordinate formula to `s.re = 1/2`, already fixed by
the carry-built tower. `NCG-EQV-017` then proves the exact identity between
the one native zero and its analytic readout.


## 7. Sigma in the analytic coordinate

For (s=sigma+it), the complex sample is exactly the coordinate image of the
real radial sample. The new named theorem `NCG-EQV-016` makes its norm law
explicit:

[
operatorname{normSq}(n^{-s})=n^{-2sigma}.
]

Therefore moving (operatorname{Re}(s)) is precisely moving radial amplitude
and quadratic norm. The complex plane does not add a degree of freedom beyond
that already visible in the radial comparison chart.

## 8. Dependency direction

The logical order is:

```text
centered bracket
→ finite power-sum identity
→ bracket-series convergence
→ holomorphy
→ nonvanishing camera factor
→ normalized camera compatibility
→ canonical analytic representative
```

No theorem in this layer constructs the native mass or is a premise of
`NCG-OPR-004`. The analytic layer provides faithful coordinates after the real
operator has already been assembled.
