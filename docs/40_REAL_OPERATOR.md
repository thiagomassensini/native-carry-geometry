# The Native and Radial Carry Operators in Real Coordinates

## 1. State space and energy

The real state space is `RealCarryPlane := ℝ × ℝ` with

```text
quadraticEnergy(x,y) = x² + y².
```

`NCG-OPR-002` proves that this energy vanishes exactly when the resultant
vector vanishes.

## 2. Fixed native state

The carry-built state is

```text
u_t(n) = n^(-1/2) (cos(-t log n), sin(-t log n)).
```

It is named `nativeRealCarryState time n`.  Its amplitude is read from the
native tower, and `NCG-REA-004` identifies its energy with inverse-integer
carry mass.

The finite and boundary forms are

```lean
finiteNativeRealCarryOperator camera cutoff time
NativeBoundaryConvergesToZero camera time
IsNativeCarryOperatorZero camera time
```

## 3. Radial family

The sigma family is

```text
u_(sigma,t)(n) = n^(-sigma) (cos(-t log n), sin(-t log n)).
```

with public operators

```lean
finiteRadialDeformation camera cutoff sigma time
RadialDeformationBoundaryConvergesToZero camera sigma time
```

and raw zero predicates

```lean
IsFiniteRealCarryOperatorZero camera cutoff sigma time
IsRealCarryOperatorZero camera sigma time
```

A raw zero is exactly vanishing of the supplied resultant.  The predicates do
not test native mass and do not contain a one-half premise.

## 4. Finite zero identity

`NCG-OPR-003` states

```lean
IsFiniteRealCarryOperatorZero camera cutoff sigma time ↔
  finiteRadialDeformation camera cutoff sigma time = 0
```

This is the finite zero locus of the radial operator family for every supplied
`sigma`.

## 5. Native specialization

The radial state at one half is extensionally the fixed native state.  At the
boundary, `NCG-OPR-005` gives

```lean
IsRealCarryOperatorZero camera (1 / 2) time ↔
  IsNativeCarryOperatorZero camera time
```

This identifies the native member of the radial family.  It says nothing about
whether other members can also vanish.

## 6. Mass compatibility and representation

`RadialDeformationRepresentsNativeMass sigma time` is an independent predicate
and is equivalent to `sigma = 1/2`.  It appears only in

```lean
RadialChartRepresentsNativeZero camera sigma time
RadialChartRepresentsFiniteNativeZero camera cutoff sigma time
```

The representation factorization confines native representations to one half.
It does not redefine or erase raw radial zeros elsewhere.

## 7. Boundary convergence

Boundary zero means convergence of finite resultants to the zero vector.  No
finite cutoff is required to vanish exactly.  Visible energy is the energy of
the final vector resultant, not the sum of the energies of its summands.

## 8. Camera scope

The generic finite camera is total for every natural width.  Widths `0`, `1`,
and `2` are degenerate in this generic family; the binary adjacent-center
construction is separate.  Odd-prime hypotheses remain explicit where
balanced-residue and analytic prefix identities require them.
