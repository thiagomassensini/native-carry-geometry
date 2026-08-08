# Theorem and Semantic Audit Registry

`theorems.tsv` is the machine-readable registry of citeable NCG results.
Release `v0.4.0` contains 75 active IDs and therefore exactly 75 elaborated
signature preimages.

The first three columns are stable:

1. `id`: permanent citation identifier;
2. `declaration`: fully qualified public Lean name;
3. `module`: importable Lean module name.

The remaining columns record label, theorem kind, migration class, historical
source, dependency IDs, elaborated type digest, and audit notes. Rows are
sorted lexicographically by ID.

## Canonical semantic surface

The registry is interpreted through five contracts:

| Contract | Canonical API | Principal evidence |
|---|---|---|
| Mass is upstream | `nativeTowerMass`, `nativeTowerAmplitude` | `NCG-MAS-003`, `NCG-REA-004` |
| Sigma varies quadratic norm | `radialEnergyWeight`, `radialDeformationState` | `NCG-REA-005/006`, `NCG-EQV-013/015/016` |
| Real and complex are coordinates | `complexCoordinates` | `NCG-EQV-010/011/014` |
| One native operator-zero predicate | `IsNativeCarryOperatorZero` | `NCG-EQV-017` |
| Ambient cancellation is a chart relation | `RadialChartCancelsAt`, `RadialChartRepresentsNativeZero`, `AnalyticChartRepresentsNativeZero` | `NCG-OPR-007/008`, `NCG-EQV-018/019` |

Older names remain reducible compatibility aliases. Their registered signatures
are retained for citation stability, but they do not define additional zero
objects.

## Hash policy

Every `type_sha256` is generated from the elaborated Lean environment using
this newline-terminated UTF-8 preimage:

```text
format=ncg-signature-v1
declaration=<fully qualified Lean declaration>
lean=4.32.0
mathlib=81a5d257c8e410db227a6665ed08f64fea08e997
type-repr=<(repr info.type).pretty 1000000>
```

Source text, comments, hand-entered values, and proof bodies are not part of
this digest. Proof bodies are fixed separately by the repository commit, tree,
annotated tag, and release manifest.

Generated authorities are:

- `theorem-registry.json`: full theorem metadata and elaborated types;
- `axioms.json`: transitive axiom inventory;
- `preimages/NCG-*.txt`: exact digest preimages;
- `NativeCarryGeometry/Audit/ExportTheoremTypes.lean`: generated Lean driver.

None is edited by hand.

## Migration classifications

- `renamed_wrapper`: historical theorem exposed under public nomenclature;
- `renamed_abbrev`: citeable equivalence exposed as an abbreviation;
- `reproved_wrapper`: historical result reproved for a revised representation;
- `reproved_composed`: historical result reconstructed through public results;
- `composed_new`: new public composition with no claimed exact source theorem;
- `strengthened_new_representation`: historical content retained through a
  stronger representation.

## Public definitions without NCG IDs

NCG IDs are reserved for citeable results. Supporting public definitions keep
their Lean names without synthetic IDs.

| Layer | Canonical supporting definitions |
|---|---|
| Arithmetic | `quotientAtDepth`, `residueAtDepth`, `positionalDepth`, centers, offsets, incidences |
| Measure | `carryMass`, `carryAmplitude`, `radialEnergyWeight`, `nativeTowerMass`, `nativeTowerAmplitude` |
| Bracket | `centeredSecondDifference`, `saturatedBracket`, balanced camera and curvature detectors |
| Native operator | `nativeRealCarryState`, `finiteNativeRealCarryOperator`, `NativeBoundaryConvergesToZero`, `IsNativeCarryOperatorZero` |
| Ambient radial chart | `radialDeformationState`, `finiteRadialDeformation`, `RadialChartCancelsAt`, `RadialChartRepresentsNativeZero` |
| Analytic coordinates | `complexCoordinates`, `canonicalCarryContinuation`, `nativeCarryAnalyticReadout`, `AnalyticChartRepresentsNativeZero` |

Legacy aliases are documented in
[`docs/70_ZERO_SET_FACTORIZATION.md`](../docs/70_ZERO_SET_FACTORIZATION.md).

## Provenance

`source-lock.json` pins the selected historical source tree:

```text
thiagomassensini/primos
release v0.52.0
commit 7d8d0b345b329935674edc24e5ac08ad9f7b5804
```

A source declaration records mathematical provenance, not byte identity. New
canonical wrappers in `v0.3.0` are classified as `composed_new` and cite
their public dependency IDs.

## Continuous checks

The ordinary audit verifies:

1. all 75 IDs are unique, sorted, source-annotated, and elaborated;
2. all 75 hashes are nonempty and match regenerated types;
3. JSON, axiom rows, driver entries, and preimage files have the same count;
4. only the explicit foundational axiom allowlist is used;
5. the source lock reports the current active-ID count;
6. every versioned text file passes the one-operator semantic contract;
7. all project Lean files are reachable from the root and respect dependency
   boundaries.

See [Semantic Audit Coverage](../docs/90_SEMANTIC_AUDIT.md) for the human
file-by-file review.
