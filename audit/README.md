# Theorem audit registry

`theorems.tsv` is the single machine-readable registry of citeable NCG
results. Its 59 rows correspond one-to-one with the 59 distinct `NCG-*`
identifiers currently attached to public Lean declarations.

The first three columns are stable:

1. `id`: permanent citation identifier;
2. `declaration`: fully qualified public Lean name;
3. `module`: importable Lean module name, without `.lean`.

The remaining columns record the academic label, declaration kind, migration
classification, historical source declaration and origin commit, public
dependencies used by composed results, elaborated type digest, and audit notes.
Rows are sorted lexicographically by `id`.

## Hash policy

All 59 `type_sha256` values are generated from the elaborated Lean
environment. The exact UTF-8 preimage is:

```text
format=ncg-signature-v1
declaration=<fully qualified Lean declaration>
lean=4.32.0
mathlib=81a5d257c8e410db227a6665ed08f64fea08e997
type-repr=<(repr info.type).pretty 1000000>
```

Every field ends with a line feed, including `type-repr`. The declaration type
is not split into separately serialized universe or binder fields: those are
already present in Lean's `repr` of the elaborated expression. Source-text
hashes, hand-entered values, comments, and proof bodies are not part of this
digest. The proof body is identified separately by the Git commit, tree,
annotated tag, and release manifest.

## Migration classifications

- `renamed_wrapper`: public theorem with an exact historical source result
  under formalized nomenclature.
- `renamed_abbrev`: citeable equivalence exposed as a public abbreviation.
- `reproved_wrapper`: historical mathematical result reproved for a revised
  public representation.
- `reproved_composed`: historical mathematical result reconstructed from the
  registered public chain.
- `composed_new`: new public result obtained by composing registered results;
  no exact historical declaration is claimed.
- `strengthened_new_representation`: historical content is retained through a
  stronger public representation.

The `dependencies` column is authoritative for the new or composition-based
rows. `api:` prefixes identify supporting public definitions rather than
citeable theorem IDs.

## Public API without NCG citation IDs

NCG identifiers are reserved for citeable mathematical results. Public
definitions and supporting structures remain addressable by fully qualified
Lean name, but they are not theorem citations and therefore do not receive
synthetic NCG IDs merely for appearing in the API.

| Module | Public definitions and abbreviations without NCG IDs |
| --- | --- |
| `NativeCarryGeometry.Arithmetic.PositionalDecomposition` | `NativeCarryGeometry.Arithmetic.quotientAtDepth`, `residueAtDepth`, `positionalDepth` |
| `NativeCarryGeometry.Arithmetic.BinaryCenter` | `NativeCarryGeometry.Arithmetic.Binary.binaryCenter`, `OddLeg`, `BinaryIncidence`, `binaryEffectiveDepth` |
| `NativeCarryGeometry.Arithmetic.BalancedResidue` | `NativeCarryGeometry.Arithmetic.Balanced.halfRange`, `balancedOffsets`, `BalancedOffset`, `NonzeroResidue`, `Nonmultiple`, `Incidence` |
| `NativeCarryGeometry.Arithmetic.CarryDepth` | `NativeCarryGeometry.Arithmetic.Balanced.canonicalOffset`, `effectiveDepth`, `centerDepth` |
| `NativeCarryGeometry.Measure.CarryMass` | `NativeCarryGeometry.Measure.carryMass`, `criticalAmplitude`, `deformedAmplitude`, `radialRatio`, `massWeight` |
| `NativeCarryGeometry.Measure.CarryProbability` | `NativeCarryGeometry.Measure.uniformFiniteProbability`, `uniformCarryEvent` |
| `NativeCarryGeometry.Measure.QuadraticAmplitude` | `NativeCarryGeometry.Measure.PositionalMassCompatible`, `radialBranchEnergy` |
| `NativeCarryGeometry.Bracket.CenteredDifference` | `NativeCarryGeometry.Bracket.centeredSecondDifference`, `saturatedBracket` |
| `NativeCarryGeometry.Bracket.BalancedCamera` | `NativeCarryGeometry.Bracket.Balanced.halfRange`, `balancedBracket`, `alignedCenter`, `finiteBracketChart` |
| `NativeCarryGeometry.Bracket.RadialCurvature` | `NativeCarryGeometry.Bracket.Curvature.balancedRadialCurvature`, `balancedRadialCurvatureAtSigma`, `pairedRadialCurvature` |
| `NativeCarryGeometry.Operator.RealState` | `NativeCarryGeometry.Operator.RealCarryPlane`, `quadraticEnergy`, `rotationDirection`, `realCarryState`, `criticalRealCarryState`, `RealCarryEnergyCompatible` |
| `NativeCarryGeometry.Operator.FiniteRealOperator` | `NativeCarryGeometry.Operator.finiteSaturatedBracketOperator`, `finiteRealCarryOperator`, `criticalFiniteRealCarryOperator`, `visibleEnergy`, `IsFiniteRealCarryOperatorZero` |
| `NativeCarryGeometry.Operator.BoundaryOperator` | `NativeCarryGeometry.Operator.BoundaryConvergesToZero`, `IsBoundaryResonance` |
| `NativeCarryGeometry.Operator.ZeroSetFactorization` | `NativeCarryGeometry.Operator.IsRealCarryOperatorZero` |
| `NativeCarryGeometry.Analytic.FiniteBracketChart` | `NativeCarryGeometry.Analytic.powerMonomial`, `positivePowerPrefix`, `convergentPowerSeries` |
| `NativeCarryGeometry.Analytic.BracketSeries` | `NativeCarryGeometry.Analytic.bracketSeries`, `finiteBracketSeries` |
| `NativeCarryGeometry.Analytic.BracketHolomorphy` | `NativeCarryGeometry.Analytic.bracketHalfPlane` |
| `NativeCarryGeometry.Analytic.CanonicalContinuation` | `NativeCarryGeometry.Analytic.cameraNormalizationFactor`, `canonicalStrip`, `normalizedBracketChart`, `canonicalCarryContinuation` |
| `NativeCarryGeometry.Equivalence.ComplexCoordinates` | `NativeCarryGeometry.Equivalence.complexCoordinates` |
| `NativeCarryGeometry.Equivalence.RealAnalyticBoundary` | `NativeCarryGeometry.Equivalence.canonicalParameter`, `IsCanonicalCarryOperatorZero` |

Supporting public lemmas without an `NCG-*` annotation retain their Lean names
but are likewise outside the citeable registry.

## Provenance scope and known asymmetries

`source-lock.json` pins the historical source to
`thiagomassensini/primos@7d8d0b345b329935674edc24e5ac08ad9f7b5804`
and release `v0.52.0`. A source declaration and commit in `theorems.tsv`
assert historical provenance, not byte identity of the new wrapper.

Four deliberate asymmetries are recorded rather than hidden:

1. `NCG-AMP-007` and `NCG-AMP-008` are new registered critical-value
   corollaries and have no exact historical declarations.
2. `NCG-EQV-008` is the new full-zero identity; the historical source proves
   only the boundary/continuation equivalence registered as `NCG-EQV-007`.
3. `NCG-EQV-009` is a new confinement corollary for the full canonical
   analytic predicate, not a statement about arbitrary scalar zeros.
4. `NCG-EQV-004` maps to the closest historical packaged finite-zero theorem,
   while the current proof uses injectivity of the stronger coordinate
   equivalence.
