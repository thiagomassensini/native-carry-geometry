# Native Carry Geometry

Native Carry Geometry is a Lean 4 formalization of a positional-carry
construction, the mass and quadratic amplitude carried by its integer tower,
the native real operator built from that tower, and faithful complex
coordinates for the same operator.

This repository is audit-oriented. Its public semantics are fixed by the
contract below; theorem types, generated signature digests, and dependency
checks enforce the implementation.

- Development release: `v0.3.0`
- Lean and Mathlib line: `v4.32.0`
- Historical source lock:
  [`thiagomassensini/primos@7d8d0b345b329935674edc24e5ac08ad9f7b5804`](https://github.com/thiagomassensini/primos/tree/7d8d0b345b329935674edc24e5ac08ad9f7b5804)

## Semantic contract

### 1. Mass comes before the operator

Quotient–residue geometry and carry depth determine the carry mass

\[
\operatorname{carryMass}(b,k)=b^{-k}.
\]

in the measure layer. The integer tower then uses

```lean
nativeTowerMass n
nativeTowerAmplitude n
```

and Lean proves:

```lean
(nativeTowerAmplitude n) ^ 2 = nativeTowerMass n
```

This is `NCG-MAS-003`. The operator does not choose, receive, or test a mass
after construction. It consumes the already weighted tower.

### 2. Sigma is a quadratic-norm deformation coordinate

The native state reads amplitude from the tower:

```lean
nativeRealCarryState time n
```

The larger comparison chart replaces only the native amplitude
(n^{-1/2}) by (n^{-sigma}):

```lean
radialDeformationState sigma time n
```

The direction, phase law, bracket algebra, and camera are unchanged. Lean
states the effect of (sigma) directly:

```lean
-- NCG-REA-005
quadraticEnergy (radialDeformationState sigma time n) =
  (n : ℝ) ^ (-2 * sigma)

-- NCG-REA-006
RadialDeformationRepresentsNativeMass sigma time ↔
  sigma = (1 : ℝ) / 2
```

Thus changing the real coordinate `sigma = Re(s)` in complex notation is exactly
changing amplitude and hence quadratic norm. It does not create another
operator.

### 3. Real pairs and complex numbers are coordinates

The map

```lean
complexCoordinates : Operator.RealCarryPlane ≃+ ℂ
```

is an additive equivalence. It is injective, preserves quadratic energy, and
commutes with every finite additive camera. In particular:

```lean
-- NCG-EQV-013
Complex.normSq
    (complexCoordinates
      (radialDeformationState sigma time n)) =
  (n : ℝ) ^ (-2 * sigma)

-- NCG-EQV-014
Complex.normSq
    (complexCoordinates
      (nativeRealCarryState time n)) =
  (n : ℝ)⁻¹
```

The power monomial is literally the same sample in complex coordinates:

```lean
-- NCG-EQV-016
Complex.normSq
    (powerMonomial (canonicalParameter sigma time) n) =
  (n : ℝ) ^ (-2 * sigma)
```

No complex coordinate can add or remove a zero of the underlying resultant.

### 4. There is one operator-zero predicate

The canonical name is:

```lean
IsNativeCarryOperatorZero camera time
```

It abbreviates boundary convergence of the already weighted native operator.
The principal analytic-coordinate theorem is:

```lean
-- NCG-EQV-017
theorem isNativeCarryOperatorZero_iff_analyticReadout_eq_zero
    (time : ℝ) :
    Operator.IsNativeCarryOperatorZero 3 time ↔
      nativeCarryAnalyticReadout time = 0
```

This is one zero seen in two coordinate systems. The legacy names
`IsNativeRealCarryOperatorZero` and
`IsNativeCanonicalCarryOperatorZero` remain compatibility aliases; they do
not denote different kinds of zero.

### 5. Ambient chart cancellation is not another operator zero

The radial family is useful for proving rigidity, so its raw boundary
cancellation remains available as:

```lean
RadialChartCancelsAt camera sigma time
```

The analytic chart has the corresponding cancellation equation
`canonicalCarryContinuation s = 0`. These are statements about an ambient
comparison chart. They become a representation of the native operator only
when the chart preserves the upstream mass:

```lean
RadialChartRepresentsNativeZero camera sigma time
AnalyticChartRepresentsNativeZero s
```

The factorization theorems make this exact:

```lean
-- NCG-OPR-007
RadialChartRepresentsNativeZero camera sigma time ↔
  sigma = (1 : ℝ) / 2 ∧
    IsNativeCarryOperatorZero camera time

-- NCG-EQV-018
AnalyticChartRepresentsNativeZero s ↔
  s.re = (1 : ℝ) / 2 ∧
    canonicalCarryContinuation s = 0
```

Consequently, an off-half radial chart does not represent an operator zero.
The repository does not reclassify a raw chart cancellation as a second zero.

## Dependency chain

```text
quotient–residue decomposition
→ carry depth
→ uniform carry event and carry mass
→ quadratic-root amplitude
→ native integer tower
→ native rotating state
→ centered second difference
→ finite native camera
→ native boundary zero
→ faithful R² ↔ ℂ coordinates
→ analytic readout of the same zero
```

The (sigma)-radial family branches off only as a comparison chart for
amplitude and norm; it is not an extra input to the native operator.

## Exact scope

### Positional base and camera are different parameters

A positional base `b` indexes quotient–residue decomposition, carry depth,
mass, and amplitude. A `camera` indexes the centered-bracket observation
rule. No theorem silently identifies them.

`positionalMassCompatible_iff_radialDeformationRepresentsNativeMass`
shows that positional and integer-indexed radial charts recognize the same
mass-preserving shell. It is downstream of both constructions.

### Camera scope

The radial representation factorization is quantified over every natural
camera. It does not assert equality of temporal resonance sets for distinct
cameras.

The real/analytic boundary crosswalk is specialized to camera `3` and the
open canonical strip:

```lean
0 < s.re ∧ s.re < 1
```

Normalized analytic-camera compatibility is proved for odd prime cameras.
These hypotheses remain visible in the Lean types.

### Degenerate total cameras

The generic finite camera uses

```lean
halfRange camera = (camera - 1) / 2
```

so cameras `0`, `1`, and `2` are degenerate in that generic family. The
binary adjacent-center incidence geometry is a separate, nondegenerate
arithmetic construction; it is not definitionally the generic camera at
width `2`.

### Explicit nonclaim

This repository does not prove that arbitrary ambient chart cancellation
forces (sigma=1/2). It proves that the chart represents the native
mass-built operator exactly at (sigma=1/2). This is the typed distinction
between `RadialChartCancelsAt` and
`RadialChartRepresentsNativeZero`.

## Build

Install [`elan`](https://github.com/leanprover/elan), then run:

```bash
git clone https://github.com/thiagomassensini/native-carry-geometry.git
cd native-carry-geometry
lake build --wfail NativeCarryGeometry
```

The repository pins `leanprover/lean4:v4.32.0`; `lake-manifest.json` pins
the resolved Mathlib commit. See
[Reproducibility](docs/05_REPRODUCIBILITY.md) for the complete audit
procedure.

## Documentation map

| Document | Subject |
|---|---|
| [Scope and semantic contract](docs/00_SCOPE.md) | Exact ontology, claims, parameters, and nonclaims |
| [Reproducibility](docs/05_REPRODUCIBILITY.md) | Toolchain, build, and release audit |
| [Positional geometry](docs/10_POSITIONAL_GEOMETRY.md) | QR decomposition, centers, residues, and depth |
| [Carry mass and amplitude](docs/20_CARRY_MASS_AND_AMPLITUDE.md) | Upstream mass, quadratic amplitude, and multibase rigidity |
| [Bracket and curvature](docs/30_BRACKET_AND_CURVATURE.md) | Centered differences and auxiliary deformation detectors |
| [Real operator](docs/40_REAL_OPERATOR.md) | Native state, finite resultants, and the one boundary zero |
| [Canonical analytic presentation](docs/50_CANONICAL_ANALYTIC_PRESENTATION.md) | Complex chart construction and normalization |
| [Real–analytic identity](docs/60_REAL_ANALYTIC_EQUIVALENCE.md) | Same operator, energy, resultant, and zero in two coordinates |
| [Native zero and chart representation](docs/70_ZERO_SET_FACTORIZATION.md) | One zero and radial-chart factorization |
| [Theorem registry](docs/80_THEOREM_REGISTRY.md) | Stable NCG identifiers and type digests |
| [Source provenance](docs/85_SOURCE_PROVENANCE.md) | Historical lock and selective-port policy |
| [Excluded research routes](docs/88_EXCLUDED_RESEARCH_ROUTES.md) | Extensions outside this audit root |
| [Semantic audit coverage](docs/90_SEMANTIC_AUDIT.md) | File-by-file review policy and enforced vocabulary |

## Audit artifacts

Every registered theorem has a stable NCG identifier, fully qualified Lean
name, elaborated type, SHA-256 signature digest, dependency list, source
provenance, and transitive axiom report. Generated artifacts live under
[`audit/`](audit/).

The repository also runs a semantic-contract checker over every versioned
text file. It prevents legacy aliases from becoming the public ontology and
requires the canonical one-operator vocabulary in the public entry points.

## Citation and license

Citation metadata is provided in [`CITATION.cff`](CITATION.cff) and
[`.zenodo.json`](.zenodo.json). The repository is licensed under the
[Apache License 2.0](LICENSE).
