# Public Theorem Registry

## 1. Citation model

Release `v0.3.0` designates 75 citeable mathematical results. Each receives a
stable semantic identifier:

```text
NCG-<FAMILY>-<NUMBER>
```

The machine-readable authority is
[`audit/theorems.tsv`](../audit/theorems.tsv). This document is its
reader-facing index.

Supporting public definitions and helper lemmas remain addressable by their
fully qualified Lean names but do not receive synthetic theorem identifiers.


## 1.1. Canonical semantic surface

The principal public ontology for `v0.3.0` is:

- `IsNativeCarryOperatorZero`: the one operator-zero predicate;
- `RadialChartCancelsAt`: ambient comparison-chart cancellation;
- `RadialChartRepresentsNativeZero`: a representation relation;
- `AnalyticChartRepresentsNativeZero`: the same relation in analytic
  coordinates.

Rows whose declarations retain older zero-like names remain registered for
signature continuity. Their labels explicitly identify them as legacy or
radial-presentation results; they do not define the release ontology.

## 2. Positional arithmetic

| ID | Public declaration | Academic label |
|---|---|---|
| `NCG-POS-001` | `Arithmetic.positionalDecompositionAtDepth_existsUnique` | Canonical Positional Decomposition |
| `NCG-POS-002` | `Arithmetic.positionalDepth_factorization_existsUnique` | Positional Depth Factorization |
| `NCG-POS-003` | `Arithmetic.positionalDepth_spec` | Maximal Positional Depth |
| `NCG-POS-004` | `Arithmetic.residueAtDepth_eq_zero_iff_pow_dvd` | Positional Carry-Event Divisibility Criterion |
| `NCG-BIN-001` | `Arithmetic.Binary.four_dvd_binaryCenter` | Binary Center Divisibility |
| `NCG-BIN-002` | `Arithmetic.Binary.binaryCenter_unique` | Binary Adjacent-Center Uniqueness |
| `NCG-BIN-003` | `Arithmetic.Binary.oddLeg_equiv_binaryIncidence` | Binary Leg–Incidence Bijection |
| `NCG-BIN-004` | `Arithmetic.Binary.binaryEffectiveDepth_eq_centerDepth` | Binary Carry-Depth Identification |
| `NCG-BAL-001` | `Arithmetic.Balanced.card_balancedOffsets` | Balanced Camera Cardinality |
| `NCG-BAL-002` | `Arithmetic.Balanced.balancedOffset_equiv_nonzeroResidue` | Balanced Residue Representation |
| `NCG-BAL-003` | `Arithmetic.Balanced.centerOffsetDecomposition_existsUnique` | Canonical Center–Offset Decomposition |
| `NCG-DEP-001` | `Arithmetic.Balanced.offsetCarries_iff_eq_canonicalOffset` | Unique Carrying Offset |
| `NCG-DEP-002` | `Arithmetic.Balanced.effectiveDepth_eq_centerDepth` | Carry-Depth Identification |

## 3. Carry mass and quadratic amplitude

| ID | Public declaration | Academic label |
|---|---|---|
| `NCG-PRB-001` | `Measure.uniformCarryEvent_probability` | Uniform Carry Probability Law |
| `NCG-MAS-001` | `Measure.criticalAmplitude_sq_eq_carryMass` | Critical Amplitude–Mass Identity |
| `NCG-MAS-002` | `Measure.carryMass_effectiveDepth_eq_centerDepth` | Carry-Mass Depth Transport |
| `NCG-MAS-003` | `Measure.nativeTowerAmplitude_sq_eq_mass` | Native Tower Amplitude–Mass Identity |
| `NCG-AMP-001` | `Measure.deformedAmplitude_sq_eq_massWeight` | Deformed Amplitude Energy Identity |
| `NCG-AMP-002` | `Measure.deformedAmplitude_sq_eq_carryMass_iff` | Local Quadratic Amplitude Rigidity |
| `NCG-AMP-003` | `Measure.positionalMassCompatible_iff` | Global Quadratic Amplitude Rigidity |
| `NCG-AMP-004` | `Measure.radialBranchEnergy_eq_one_iff` | Radial Branch Saturation |
| `NCG-AMP-005` | `Measure.radialBranchSaturation_base_independent` | Base Independence of Saturation |
| `NCG-AMP-006` | `Measure.positionalMassCompatible_iff_realEnergyCompatible` | Quadratic Domain Crosswalk |
| `NCG-AMP-007` | `Measure.radialBranchEnergy_half_eq_one` | Critical Radial Branch Saturation |
| `NCG-AMP-008` | `Measure.radialBranchEnergy_half_ne_zero` | Critical Radial Branch Nondegeneracy |

## 4. Bracket and curvature

| ID | Public declaration | Academic label |
|---|---|---|
| `NCG-BRK-001` | `Bracket.centeredSecondDifference_neg_radius` | Radius Symmetry |
| `NCG-BRK-002` | `Bracket.centeredSecondDifference_add` | Bracket Additivity |
| `NCG-BRK-003` | `Bracket.Balanced.balancedBracket_eq_saturatedBracket` | Centered Bracket Representation |
| `NCG-BRK-004` | `Bracket.Balanced.finiteBracketCancellation` | Finite Bracket Cancellation |
| `NCG-BRK-005` | `Bracket.Balanced.finiteBracketChart_eq_intervalSum_sub_centerCorrection` | Finite Bracket-Chart Identity |
| `NCG-CUR-001` | `Bracket.Curvature.balancedRadialCurvature_eq_half_pairSum` | Paired Curvature Representation |
| `NCG-CUR-002` | `Bracket.Curvature.balancedRadialCurvature_pos_of_pos` | Convex-Side Positivity |
| `NCG-CUR-003` | `Bracket.Curvature.balancedRadialCurvature_neg_of_neg` | Concave-Side Negativity |
| `NCG-CUR-004` | `Bracket.Curvature.balancedRadialCurvature_eq_zero_iff` | Radial Curvature Rigidity |

## 5. Real state and operator

| ID | Public declaration | Academic label |
|---|---|---|
| `NCG-REA-001` | `Operator.quadraticEnergy_rotationDirection` | Real Rotation Unit-Energy Theorem |
| `NCG-REA-002` | `Operator.quadraticEnergy_realCarryState` | Radial-Deformation Energy Invariance |
| `NCG-REA-003` | `Operator.realCarryEnergyCompatible_iff` | Radial-Deformation Mass Rigidity |
| `NCG-REA-004` | `Operator.quadraticEnergy_nativeRealCarryState` | Native State Carry-Mass Energy |
| `NCG-REA-005` | `Operator.quadraticEnergy_radialDeformationState` | Canonical Radial-Deformation Quadratic-Norm Identity |
| `NCG-REA-006` | `Operator.radialDeformationRepresentsNativeMass_iff` | Canonical Radial-Deformation Mass Rigidity |
| `NCG-OPR-001` | `Operator.map_finiteSaturatedBracketOperator` | Additive Naturality of the Finite Operator |
| `NCG-OPR-002` | `Operator.quadraticEnergy_eq_zero_iff` | Faithfulness of Visible Energy |
| `NCG-OPR-003` | `Operator.isFiniteRealCarryOperatorZero_iff` | Finite Radial-Presentation Factorization |
| `NCG-OPR-004` | `Operator.isRealCarryOperatorZero_iff` | Radial Presentation Factorization |
| `NCG-OPR-005` | `Operator.realCarryOperatorZero_sigma_eq_half` | Radial-Presentation Uniqueness Corollary |
| `NCG-OPR-006` | `Operator.not_realCarryOperatorZero_of_sigma_ne_half` | Legacy Off-Shell Nonrepresentation Corollary |
| `NCG-OPR-007` | `Operator.radialChartRepresentsNativeZero_iff` | Canonical Radial-Chart Native Representation Factorization |
| `NCG-OPR-008` | `Operator.radialChartRepresentsFiniteNativeZero_iff` | Canonical Finite Radial-Chart Native Representation Factorization |

## 6. Canonical analytic presentation

| ID | Public declaration | Academic label |
|---|---|---|
| `NCG-ANL-001` | `Analytic.finiteBracketChart_eq_two_prefixes` | Finite Power-Sum Factorization |
| `NCG-ANL-002` | `Analytic.finiteBracketChart_tendsto_bracketSeries` | Bracket-Series Convergence |
| `NCG-ANL-003` | `Analytic.analyticOnNhd_bracketSeries` | Holomorphy of the Bracket Series |
| `NCG-ANL-004` | `Analytic.cameraNormalizationFactor_ne_zero` | Camera-Factor Nonvanishing |
| `NCG-ANL-005` | `Analytic.normalizedBracketChart_camera_independent` | Camera Compatibility |
| `NCG-ANL-006` | `Analytic.bracketSeries_eq_factor_mul_canonicalCarryContinuation` | Canonical Bracket Factorization |
| `NCG-ANL-007` | `Analytic.analyticOnNhd_canonicalCarryContinuation` | Holomorphy of the Canonical Continuation |
| `NCG-ANL-008` | `Analytic.bracketSeries_zero_iff_canonicalCarryContinuation_zero` | Canonical Chart-Cancellation Representation by Any Odd Prime Camera |

## 7. Presentation equivalence

| ID | Public declaration | Academic label |
|---|---|---|
| `NCG-EQV-001` | `Equivalence.complexCoordinates_injective` | Faithful Complex Coordinate Encoding |
| `NCG-EQV-002` | `Equivalence.normSq_complexCoordinates` | Energy Preservation under Encoding |
| `NCG-EQV-003` | `Equivalence.complexCoordinates_finiteOperator` | Finite-Operator Naturality |
| `NCG-EQV-004` | `Equivalence.finiteOperator_eq_zero_iff_complexCoordinates_eq_zero` | Finite Zero-Set Equivalence |
| `NCG-EQV-005` | `Equivalence.complexCoordinates_realCarryState_eq_powerMonomial` | Radial-State/Power-Monomial Coordinate Identity |
| `NCG-EQV-006` | `Equivalence.complexCoordinates_finiteRealOperator_eq_finiteBracketChart` | Finite Real–Analytic Operator Identity |
| `NCG-EQV-007` | `Equivalence.boundaryConvergesToZero_iff_canonicalCarryContinuation_eq_zero` | Camera-Three Boundary/Continuation Zero Equivalence |
| `NCG-EQV-008` | `Equivalence.isRealCarryOperatorZero_iff_isCanonicalCarryOperatorZero` | Real/Analytic Radial-Presentation Identity |
| `NCG-EQV-009` | `Equivalence.canonicalCarryOperatorZero_re_eq_half` | Canonical Analytic Radial-Presentation Uniqueness |
| `NCG-EQV-010` | `Equivalence.finiteNativeOperator_eq_zero_iff_complexCoordinates_eq_zero` | Native Finite Zero Coordinate Identity |
| `NCG-EQV-011` | `Equivalence.nativeBoundaryConvergesToZero_iff_nativeCarryAnalyticReadout_eq_zero` | Native Boundary/Analytic Readout Zero Identity |
| `NCG-EQV-012` | `Equivalence.isNativeRealCarryOperatorZero_iff_isNativeCanonicalCarryOperatorZero` | Legacy Coordinate-Labelled Native Zero Identity |
| `NCG-EQV-013` | `Equivalence.normSq_complexCoordinates_radialDeformationState` | Radial Complex-Norm Identity |
| `NCG-EQV-014` | `Equivalence.normSq_complexCoordinates_nativeRealCarryState` | Native Complex-Norm Identity |
| `NCG-EQV-015` | `Equivalence.radialComplexNormRepresentsNativeMass_iff` | Complex Radial-Chart Mass Rigidity |
| `NCG-EQV-016` | `Equivalence.normSq_powerMonomial_canonicalParameter` | Power-Monomial Quadratic-Norm Identity |
| `NCG-EQV-017` | `Equivalence.isNativeCarryOperatorZero_iff_analyticReadout_eq_zero` | One Native Operator Zero Analytic Identity |
| `NCG-EQV-018` | `Equivalence.analyticChartRepresentsNativeZero_iff` | Analytic-Chart Native Representation Factorization |
| `NCG-EQV-019` | `Equivalence.analyticChartRepresentsNativeZero_re_eq_half` | Analytic-Chart Native Representation Uniqueness |

All declarations above are relative to the root namespace
`NativeCarryGeometry`.

## 8. Digest policy

The registry column `type_sha256` contains the generated digest of this exact
UTF-8 preimage:

```text
format=ncg-signature-v1
declaration=<fully qualified Lean declaration>
lean=4.32.0
mathlib=81a5d257c8e410db227a6665ed08f64fea08e997
type-repr=<(repr info.type).pretty 1000000>
```

Every field ends with LF, including the final field. The deterministic
exporter loads each declaration under the pinned toolchain, reads its
elaborated type from the environment, hashes the preimage, and then repeats
the export in check mode. The 75 committed preimages are stored under
`audit/preimages/`.

A source-text hash, proof-body hash, line number, or hand-entered value is not
a substitute for the elaborated-type digest.

The citation identity has three components:

| Component | Identifies |
|---|---|
| stable NCG ID | the mathematical result across compatible releases |
| `type_sha256` | the exact elaborated statement |
| proof commit and release | the exact proof body and dependency lock |

## 9. New composed results

The registry records rather than hides the following release-level
compositions:

- `NCG-AMP-007` follows from `NCG-AMP-004`;
- `NCG-AMP-008` follows from `NCG-AMP-007`;
- `NCG-EQV-008` combines the retained energy domain with `NCG-EQV-007`;
- `NCG-EQV-009` combines `NCG-EQV-008` with `NCG-OPR-005`;
- `NCG-OPR-004` is deliberately reproved through `NCG-AMP-003` and
  `NCG-AMP-006`, making the carry-domain dependency visible;
- `NCG-MAS-003` and `NCG-REA-004` expose the mass-built native tower and state;
- `NCG-REA-005/006` give the canonical sigma/norm and mass-representation
  statements;
- `NCG-OPR-007/008` replace zero-like chart nouns with explicit
  representation relations;
- `NCG-EQV-013/014/015/016` make quadratic norm preservation explicit in
  real, complex, and power-monomial coordinates;
- `NCG-EQV-017` is the principal one-native-zero analytic identity;
- `NCG-EQV-018/019` factor and confine analytic chart representations.

These relationships are machine-readable in the `dependencies` column of
`audit/theorems.tsv`.
