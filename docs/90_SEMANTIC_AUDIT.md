# Repository-Wide Semantic Audit

## 1. Audit objective

Release `v0.3.0` was reviewed against one repository-wide contract:

1. quotient–residue and carry depth precede measure;
2. carry mass belongs to the integers/tower before the operator;
3. amplitude is the proved quadratic root of that mass;
4. `sigma` belongs to an ambient radial chart and varies amplitude/norm;
5. `ℝ²` and `ℂ` are faithful coordinates of the same additive operator;
6. `IsNativeCarryOperatorZero` is the one native operator-zero predicate;
7. ambient chart cancellation is not renamed as an additional operator-zero predicate.

The review covered every versioned text file. Semantic-bearing files received
source review; generated and mechanical files are covered by deterministic
checksums, registry generation, dependency checks, and
`scripts/check_semantic_contract.py`.

## 2. Lean source coverage

| File | Semantic role | Result |
|---|---|---|
| `NativeCarryGeometry.lean` | public import root | verified causal import order |
| `Arithmetic/PositionalDecomposition.lean` | quotient–residue decomposition | verified; zero means residual event only |
| `Arithmetic/BinaryCenter.lean` | binary incidence and depth | comments corrected; no operator vocabulary |
| `Arithmetic/BalancedResidue.lean` | balanced modular incidence | legacy namespace documented as finite arithmetic |
| `Arithmetic/CarryDepth.lean` | effective/center depth identity | separated from later mass transport |
| `Measure/CarryProbability.lean` | zero-residue event probability | theorem wording restricted to its exact event |
| `Measure/CarryMass.lean` | carry mass and integer tower | canonical `radialEnergyWeight` added |
| `Measure/QuadraticAmplitude.lean` | amplitude/norm rigidity | detector null loci separated from operator zeros |
| `Bracket/CenteredDifference.lean` | additive second difference | verified unchanged |
| `Bracket/BalancedCamera.lean` | finite camera algebra | legacy `Genuine` namespace documented |
| `Bracket/RadialCurvature.lean` | auxiliary radial detector | detector null locus explicitly non-operator |
| `Operator/RealState.lean` | native state and radial chart | canonical sigma/norm theorems added |
| `Operator/QuadraticDomain.lean` | mass-domain crosswalk | canonical representation name added |
| `Operator/FiniteRealOperator.lean` | finite native resultants | one finite native operator-zero predicate plus chart-representation relation |
| `Operator/BoundaryOperator.lean` | native boundary and ambient cancellation | `RadialChartCancelsAt` made canonical |
| `Operator/ZeroSetFactorization.lean` | native operator-zero predicate and representation factorization | `IsNativeCarryOperatorZero` made canonical |
| `Analytic/FiniteBracketChart.lean` | finite power chart | verified; no operator-zero definition |
| `Analytic/BracketSeries.lean` | bracket convergence | verified; no operator-zero definition |
| `Analytic/BracketHolomorphy.lean` | holomorphy | verified; no operator-zero definition |
| `Analytic/CanonicalContinuation.lean` | ambient analytic chart | cancellation label corrected |
| `Equivalence/ComplexCoordinates.lean` | R² ≃ C | explicit complex norm identities added |
| `Equivalence/RealAnalyticBoundary.lean` | boundary/readout identity | principal zero-locus identity theorem added |
| `Audit/TheoremId.lean` | kernel registry command | verified unchanged |
| `Audit/ExportTheoremTypes.lean` | generated theorem driver | regenerated from the 75-row registry |

## 3. Documentation coverage

| File | Result |
|---|---|
| `README.md` | rewritten around the semantic contract and principal theorem |
| `docs/00_SCOPE.md` | rewritten as the authoritative semantic scope |
| `docs/05_REPRODUCIBILITY.md` | updated to audit `v0.3.0` and the canonical theorem |
| `docs/10_POSITIONAL_GEOMETRY.md` | verified: arithmetic layer remains pre-operator |
| `docs/20_CARRY_MASS_AND_AMPLITUDE.md` | clarified integer weights and sigma/norm law |
| `docs/30_BRACKET_AND_CURVATURE.md` | detector loci separated from operator zeros |
| `docs/40_REAL_OPERATOR.md` | rewritten around the native operator-zero predicate |
| `docs/50_CANONICAL_ANALYTIC_PRESENTATION.md` | ambient continuation described as a chart |
| `docs/60_REAL_ANALYTIC_EQUIVALENCE.md` | rewritten as identity of the same operator |
| `docs/70_ZERO_SET_FACTORIZATION.md` | rewritten as one native operator-zero predicate plus representation |
| `docs/80_THEOREM_REGISTRY.md` | updated for 75 results and canonical labels |
| `docs/85_SOURCE_PROVENANCE.md` | removed “complete analytic predicate” ontology |
| `docs/88_EXCLUDED_RESEARCH_ROUTES.md` | aligned exclusions with the native proof DAG |
| `audit/README.md` | updated registry count and canonical API inventory |

## 4. Mechanical and generated coverage

| Paths | Audit treatment |
|---|---|
| `audit/theorems.tsv` | human-maintained sorted crosswalk; kernel-generated hashes |
| `audit/theorem-registry.json` | regenerated from elaborated Lean types |
| `audit/axioms.json` | regenerated transitive axiom inventory |
| `audit/preimages/NCG-*.txt` | one generated signature preimage per active ID |
| `audit/source-lock.json` | source and current registry counts checked |
| `scripts/*.py`, `scripts/*.sh` | reviewed; all invoked from the audit bundle |
| `.github/workflows/*.yml` | SHA-pinned actions and immutable release workflows |
| `.release/*.md` | immutable per-release publisher sentinels |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | exact package/toolchain/dependency locks |
| `CITATION.cff`, `.zenodo.json` | release and semantic abstract aligned |
| `LICENSE`, `.gitignore` | no mathematical semantics; checksum coverage |

## 5. Canonical vocabulary

| Legacy compatibility name | Canonical meaning |
|---|---|
| `massWeight` | `radialEnergyWeight`, the sigma-dependent chart energy |
| `BoundaryConvergesToZero` | `RadialChartCancelsAt` |
| `IsFiniteRealCarryOperatorZero` | `RadialChartRepresentsFiniteNativeZero` |
| `IsRealCarryOperatorZero` | `RadialChartRepresentsNativeZero` |
| `IsCanonicalCarryOperatorZero` | `AnalyticChartRepresentsNativeZero` |
| `IsNativeRealCarryOperatorZero` | `IsNativeCarryOperatorZero` |
| `IsNativeCanonicalCarryOperatorZero` | analytic-coordinate spelling of the same native operator-zero locus |

Legacy names remain reducible aliases so downstream Lean code continues to
compile. They are excluded from the canonical ontology.

## 6. Continuous enforcement

`scripts/check_semantic_contract.py` reads every versioned UTF-8 file and:

- requires the canonical declarations and principal documentation phrases;
- rejects language that recreates a taxonomy of zero predicates;
- requires an explicit legacy notice wherever a legacy API name appears in
  public narrative;
- rejects broken Unicode markers;
- records the total files inspected in the audit report.

The ordinary GitHub Actions audit runs this checker together with Lean
elaboration, theorem-registry regeneration checks, axiom inspection, import
reachability, dependency boundaries, placeholder rejection, and release
reproducibility.
