# Theorem and Semantic Audit Registry

`theorems.tsv` is the machine-readable registry of citeable NCG results.  The
current audit contains 75 active IDs and 75 elaborated signature preimages.
The tagged `v0.4.0` release is historical; current `main` carries a
post-release correction to the zero-predicate semantics.

## Corrected semantic surface

| Contract | Canonical API | Evidence |
|---|---|---|
| Mass is upstream | `nativeTowerMass`, `nativeTowerAmplitude` | `NCG-MAS-003`, `NCG-REA-004` |
| Sigma varies quadratic norm | `radialDeformationState` | `NCG-REA-005/006`, `NCG-EQV-013/015/016` |
| Raw radial zero is cancellation | `IsFiniteRealCarryOperatorZero`, `IsRealCarryOperatorZero`, `IsCanonicalCarryOperatorZero` | `NCG-OPR-003/004`, `NCG-EQV-008` |
| Native member is the half specialization | `IsNativeCarryOperatorZero` | `NCG-OPR-005`, `NCG-EQV-017` |
| Representation is separate | `RadialChartRepresentsNativeZero`, `AnalyticChartRepresentsNativeZero` | `NCG-OPR-006/007/008`, `NCG-EQV-009/018/019` |

A raw zero remains a zero at the coordinate where the resultant vanishes.
Mass compatibility is used only to decide whether that zero represents the
fixed carry-built native operator.

## Hash policy

Every `type_sha256` is generated from the elaborated Lean environment using
this UTF-8 preimage:

```text
format=ncg-signature-v1
declaration=<fully qualified Lean declaration>
lean=4.32.0
mathlib=81a5d257c8e410db227a6665ed08f64fea08e997
type-repr=<(repr info.type).pretty 1000000>
```

Generated authorities are:

- `theorem-registry.json`;
- `axioms.json`;
- `preimages/NCG-*.txt`;
- `NativeCarryGeometry/Audit/ExportTheoremTypes.lean`.

They are regenerated from Lean rather than edited by hand.

## Migration classes

The registry retains its historical migration classes and adds
`semantic_correction` for declarations whose public type was corrected to
remove mass compatibility from a raw zero predicate.

## Continuous checks

The audit verifies unique sorted IDs, generated hashes, matching JSON and
preimage sets, the explicit axiom allowlist, dependency boundaries, source
provenance, placeholder rejection, and the corrected semantic contract.
