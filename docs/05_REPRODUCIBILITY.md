# Reproducibility and Audit Procedure

## 1. Locked environment

Release `v0.3.0` uses:

| Component | Lock |
|---|---|
| Lean | `leanprover/lean4:v4.32.0` |
| Mathlib input revision | `v4.32.0` |
| Mathlib resolved commit | `81a5d257c8e410db227a6665ed08f64fea08e997` |
| Historical source | `thiagomassensini/primos@7d8d0b345b329935674edc24e5ac08ad9f7b5804` |

The Lean toolchain is fixed by `lean-toolchain`. Package resolution is recorded
in `lake-manifest.json`. An audit must report both the tag and the resolved
commit, because a human-readable tag alone is not a content hash.

## 2. Clean reproduction

Install [`elan`](https://github.com/leanprover/elan), then:

```bash
git clone https://github.com/thiagomassensini/native-carry-geometry.git
cd native-carry-geometry
git checkout v0.3.0
lake build --wfail NativeCarryGeometry
```

The expected result is successful elaboration of the complete audit root with
warnings treated as errors.

For an archival audit, record:

```bash
git rev-parse HEAD
lake --version
lean --version
sha256sum lean-toolchain lake-manifest.json
```

Do not run an unconstrained dependency update and then cite the resulting build
as reproduction of `v0.3.0`.

## 3. Kernel audit

The minimum release audit consists of:

1. elaborating `NativeCarryGeometry`;
2. rejecting active `sorry`, `admit`, or project-declared axioms;
3. checking that every project Lean file is reachable from the audit root;
4. checking dependency boundaries;
5. exporting all public NCG theorem types;
6. computing and comparing canonical type digests;
7. recording the axioms reported for every public theorem;
8. checking every versioned text file against the semantic contract;
9. failing if generated registry files differ from committed release data.

For the principal one-zero theorem, an auditor should inspect:

```lean
#check NativeCarryGeometry.Equivalence.isNativeCarryOperatorZero_iff_analyticReadout_eq_zero
#print axioms NativeCarryGeometry.Equivalence.isNativeCarryOperatorZero_iff_analyticReadout_eq_zero
```

The audit distinguishes ordinary Lean/Mathlib foundations from any axiom
introduced by this project. Project policy is to introduce no axioms.

## 4. Dependency boundaries

The intended layer boundaries are:

| Layer | May depend on | Must not depend on |
|---|---|---|
| Arithmetic | finite arithmetic, divisibility, valuations | complex analysis, infinite operator limits |
| Measure | real powers, finite probability, geometric sums | analytic presentation |
| Bracket | additive or ring algebra | boundary or analytic zero predicates |
| Real operator | real topology and limits | analytic continuation modules |
| Analytic presentation | complex analysis and bracket modules | excluded historical operator routes |
| Equivalence | real and analytic public APIs | misclassified ambient chart cancellations |

The real terminal theorem must remain provable without importing the analytic
presentation.

## 5. Semantic identifiers and type digests

Each public audit theorem has a stable identifier of the form:

```text
NCG-<FAMILY>-<NUMBER>
```

For example, `NCG-EQV-017` identifies:

```text
NativeCarryGeometry.Equivalence.isNativeCarryOperatorZero_iff_analyticReadout_eq_zero
```

A `type-sha256` digest is computed from the UTF-8 bytes of this exact,
newline-terminated preimage:

```text
format=ncg-signature-v1
declaration=<fully qualified Lean declaration>
lean=4.32.0
mathlib=81a5d257c8e410db227a6665ed08f64fea08e997
type-repr=<(repr info.type).pretty 1000000>
```

Every line, including the final `type-repr` line, ends with LF. Universe and
binder information are contained inside Lean's elaborated expression
representation; they are not serialized as additional fields.

The proof body and transitive axiom list are not part of `type-sha256`. The
repository commit, tree, annotated tag, and release manifest identify the proof
body; `audit/axioms.json` records axioms independently. All committed digests
were generated after successful kernel elaboration and are rechecked by CI.

## 6. Source audit

The selective port is locked to:

```text
repository: thiagomassensini/primos
commit: 7d8d0b345b329935674edc24e5ac08ad9f7b5804
```

An audit entry for a ported theorem should contain:

- stable NCG identifier;
- new fully qualified declaration;
- historical module and declaration;
- locked source commit;
- whether the change is a rename, namespace move, proof simplification,
  composition, or genuinely new statement;
- release and proof commit;
- elaborated type digest.

Line numbers may be supplied as navigation aids, but they are not stable
identifiers.

## 7. Scope-sensitive checks

Before approving a release, verify mechanically or by source inspection that:

- no theorem asserts a pointwise equality between `b⁻ᵏ` and `n⁻¹`;
- `b` and `camera` are not silently identified;
- `NCG-OPR-007` remains universally quantified over `camera : ℕ`;
- `NCG-EQV-007` retains camera `3` and the canonical-strip premise;
- `IsNativeCarryOperatorZero` has no radial parameter or post-hoc mass
  conjunct;
- `RadialChartCancelsAt` is never documented as an operator zero;
- `RadialChartRepresentsNativeZero` and
  `AnalyticChartRepresentsNativeZero` are documented as representation
  relations;
- odd-prime hypotheses remain present on the camera-specific analytic
  theorems;
- generic camera `2` is not documented as the nondegenerate binary camera;
- no excluded historical route enters the proof dependency of
  `NCG-OPR-007`.

## 8. Citation record

An auditable citation has the form:

```text
Theorem NCG-EQV-017,
type-sha256 <digest>,
Native Carry Geometry v0.3.0,
proof commit <commit>.
```

The theorem registry is the release crosswalk from this citation to a Lean
declaration. See [Theorem Registry](80_THEOREM_REGISTRY.md).
