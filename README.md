# Native Carry Geometry

Native Carry Geometry is a Lean 4 formalization of a positional-carry
construction, its quadratic amplitude law, a real rotating-state operator, and
an intrinsic analytic presentation of the same operator.

This repository is intentionally small and audit-oriented. Its mathematical
dependency chain is

```text
positional decomposition
→ carry depth
→ uniform carry mass
→ quadratic amplitude rigidity
→ real rotating state
→ centered bracket
→ finite camera resultants
→ boundary closure
→ zero-set factorization
→ faithful analytic presentation
```

- Release: `v0.1.0`
- Lean and Mathlib line: `v4.32.0`
- Historical source lock:
[`thiagomassensini/primos@7d8d0b345b329935674edc24e5ac08ad9f7b5804`](https://github.com/thiagomassensini/primos/tree/7d8d0b345b329935674edc24e5ac08ad9f7b5804)

## Principal results

For every natural camera width, the complete real-operator zero predicate
factors into a unique radial shell and a temporal boundary resonance:

```lean
theorem isRealCarryOperatorZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    IsRealCarryOperatorZero camera sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsBoundaryResonance camera time
```

This is theorem `NCG-OPR-004`, the **Real Carry Operator Zero-Set
Factorization Theorem**. Its immediate corollaries are radial confinement
(`NCG-OPR-005`) and off-shell nonvanishing (`NCG-OPR-006`).

The analytic presentation is connected to the real presentation by:

```lean
theorem isRealCarryOperatorZero_iff_isCanonicalCarryOperatorZero
    {s : ℂ} (hs : s ∈ Analytic.canonicalStrip) :
    Operator.IsRealCarryOperatorZero 3 s.re s.im ↔
      IsCanonicalCarryOperatorZero s
```

This is `NCG-EQV-008`. Its scope is exact:

- the real confinement theorem is universal in `camera : ℕ`;
- the boundary-to-analytic crosswalk is specialized to camera `3`;
- the crosswalk assumes `s ∈ canonicalStrip`, i.e.
  `0 < s.re ∧ s.re < 1`;
- `IsCanonicalCarryOperatorZero` retains
  `RealCarryEnergyCompatible s.re s.im`; a scalar cancellation is not promoted
  to a full operator zero after discarding the quadratic domain.

The resulting analytic radial confinement theorem is `NCG-EQV-009`.

## Scope distinctions

### Base and camera are different parameters

A positional base `b` indexes decomposition, carry depth, mass, and amplitude.
A camera `camera` indexes the finite centered-bracket observation rule. The
theorem

```lean
positionalMassCompatible_iff_realEnergyCompatible
```

(`NCG-AMP-006`) identifies their admissible quadratic domains without asserting
`b = camera` and without asserting a pointwise equality between `b⁻ᵏ` and
`n⁻¹`.

### Universal confinement does not identify all resonance sets

`NCG-OPR-004` is one theorem quantified over every natural camera. It does not
assert that two distinct raw camera formulas are definitionally equal, and it
does not assert that their temporal resonance sets are literally equal.

### Total definitions include degenerate cameras

The generic finite camera uses

```lean
halfRange camera = (camera - 1) / 2
```

in natural-number arithmetic. Consequently cameras `0`, `1`, and `2` have
zero half-range in this generic family. The universal theorem includes these
total, degenerate instances. The nondegenerate binary incidence geometry in
`Arithmetic/BinaryCenter.lean` is an arithmetic construction; it is not
definitionally the generic finite camera at width `2`.

### Odd-prime hypotheses remain local

The positional mass and real confinement results do not require primality.
Prime and oddness hypotheses occur only where the implementation identifies a
balanced residue camera with its symmetric bracket chart or compares
normalized analytic camera charts.

## Build

Install the Lean toolchain manager
[`elan`](https://github.com/leanprover/elan), then run:

```bash
git clone https://github.com/thiagomassensini/native-carry-geometry.git
cd native-carry-geometry
lake build --wfail NativeCarryGeometry
```

The repository pins `leanprover/lean4:v4.32.0`; `lake-manifest.json` pins the
resolved Mathlib commit. See [Reproducibility](docs/05_REPRODUCIBILITY.md) for
the complete audit procedure.

## Documentation map

| Document | Subject |
|---|---|
| [Scope](docs/00_SCOPE.md) | Exact claims, parameters, and nonclaims |
| [Reproducibility](docs/05_REPRODUCIBILITY.md) | Toolchain, build, and release audit |
| [Positional geometry](docs/10_POSITIONAL_GEOMETRY.md) | Decomposition, binary center, balanced residues, depth |
| [Carry mass and amplitude](docs/20_CARRY_MASS_AND_AMPLITUDE.md) | Probability, mass, quadratic rigidity, domain crosswalk |
| [Bracket and curvature](docs/30_BRACKET_AND_CURVATURE.md) | Centered differences, cameras, and sign rigidity |
| [Real operator](docs/40_REAL_OPERATOR.md) | Real state, finite resultants, boundary closure |
| [Canonical analytic presentation](docs/50_CANONICAL_ANALYTIC_PRESENTATION.md) | Bracket series and camera normalization |
| [Real–analytic equivalence](docs/60_REAL_ANALYTIC_EQUIVALENCE.md) | Coordinate, finite, boundary, and full-zero identities |
| [Zero-set factorization](docs/70_ZERO_SET_FACTORIZATION.md) | Terminal theorem and exact logical scope |
| [Theorem registry](docs/80_THEOREM_REGISTRY.md) | Stable NCG identifiers and type-digest policy |
| [Source provenance](docs/85_SOURCE_PROVENANCE.md) | Historical lock and selective-port policy |
| [Excluded research routes](docs/88_EXCLUDED_RESEARCH_ROUTES.md) | Valid historical extensions outside this audit root |

## Theorem identifiers and digests

Public audit theorems carry stable semantic identifiers such as
`NCG-OPR-004`. A release registry pairs each identifier with:

- the fully qualified Lean declaration;
- the elaborated theorem type;
- a SHA-256 digest of the versioned signature preimage;
- the proof commit and release;
- the locked historical source declaration.

The preimage is UTF-8 text with newline-terminated fields, in this exact order:
`format=ncg-signature-v1`, the fully qualified `declaration`, `lean=4.32.0`,
the pinned `mathlib` commit, and
`type-repr=<(repr info.type).pretty 1000000>`. Digests are generated only after
kernel elaboration and verified by a second export. They are never guessed or
copied from line numbers. The proof body is fixed separately by the repository
commit, tree, annotated tag, and release manifest.

## Citation and license

Citation metadata is provided in [`CITATION.cff`](CITATION.cff) and
[`.zenodo.json`](.zenodo.json). The repository is licensed under the
[Apache License 2.0](LICENSE).
