# Source Provenance

## 1. Historical source lock

The selective port is locked to:

```text
repository: https://github.com/thiagomassensini/primos
branch: main
release: v0.52.0
commit: 7d8d0b345b329935674edc24e5ac08ad9f7b5804
```

The machine-readable lock is
[`audit/source-lock.json`](../audit/source-lock.json).

This lock identifies the complete historical tree from which proofs were
selected. Individual registry rows may cite an earlier ancestor commit at
which a source declaration first reached its audited form; all such
declarations are contained in the locked `v0.52.0` history.

## 2. Selective-port policy

The new repository is not a directory-level copy. The port follows these
rules:

1. retain only declarations needed for the stated audit chain;
2. preserve the exact mathematical hypotheses of source theorems;
3. replace narrative public names with mathematical names;
4. keep historical implementation namespaces internal;
5. expose a small public namespace organized by mathematical role;
6. reprove compositions through the public registered chain when this makes a
   dependency explicit;
7. record strengthened representations and new corollaries honestly;
8. exclude historical modules that are not proof dependencies of the
   advertised results.

## 3. Public and internal namespaces

The public API is divided into:

```text
NativeCarryGeometry.Arithmetic
NativeCarryGeometry.Measure
NativeCarryGeometry.Bracket
NativeCarryGeometry.Operator
NativeCarryGeometry.Analytic
NativeCarryGeometry.Equivalence
```

Historical proof implementations may remain under
`NativeCarryGeometry.Internal`. Their presence preserves auditable proof
content without exposing historical terminology as the official API.

## 4. Migration classes

Every row in [`audit/theorems.tsv`](../audit/theorems.tsv) records one of:

| Class | Meaning |
|---|---|
| `renamed_wrapper` | exact historical theorem exposed under the public nomenclature |
| `renamed_abbrev` | citeable equivalence exposed as a public abbreviation |
| `reproved_wrapper` | historical result reproved for a revised public representation |
| `reproved_composed` | historical result reconstructed through registered public theorems |
| `composed_new` | new corollary or identity composed from registered results |
| `strengthened_new_representation` | historical content preserved through a stronger public representation |

A source declaration is evidence of mathematical provenance, not a claim of
byte-for-byte identity.

## 5. Deliberate release-level changes

### 5.1. Explicit carry-to-operator dependency

The native tower is constructed from carry mass before the operator. The
radial representation theorem is reproved through the public positional-domain
crosswalk so that this causal dependency is visible in the proof term.

### 5.2. Additive coordinate equivalence

The historical coordinate map was an injective additive map. The public API
uses the stronger and more natural equivalence

```lean
RealCarryPlane ≃+ ℂ
```

and reproves energy, finite-resultant, and zero-locus preservation for that
coordinate representation.

### 5.3. One native operator-zero predicate and ambient chart relations

The historical camera-three theorem identifies real radial-chart cancellation
with analytic-chart cancellation. Release `v0.3.0` gives the native
operator-zero predicate the canonical name `IsNativeCarryOperatorZero` and registers its analytic
coordinate identity as `NCG-EQV-017`.

The wider propositions `RadialChartRepresentsNativeZero` and
`AnalyticChartRepresentsNativeZero` are representation relations: they retain
the upstream mass law while comparing ambient charts. Historical names that
look like additional zero predicates remain aliases only.

### 5.4. Registered corollaries

`NCG-AMP-007`, `NCG-AMP-008`, `NCG-EQV-009`, and the canonical
one-operator wrappers added in `v0.3.0` are explicit public compositions in
this repository. They are not misreported as exact
historical declarations.

## 6. Provenance checkpoints by layer

The theorem registry gives a row-level source commit. The main integration
checkpoints represented in the locked history are:

| Layer | Historical role |
|---|---|
| positional decomposition and uniform probability | general-base foundational seams |
| binary and balanced incidence geometry | center, residue, and depth constructions |
| carry mass and quadratic rigidity | local and global amplitude laws |
| real state and finite camera | rotating state, energy, additive bracket operator |
| native zero and radial-chart representation factorization | mass-built native predicate plus universal camera compatibility theorem and corollaries |
| canonical analytic presentation | bracket convergence, normalization, camera compatibility |
| real–analytic boundary crosswalk | positive samples, finite charts, and camera-three boundary equivalence |

For exact source declaration and commit values, use
`audit/theorems.tsv`, not prose or mutable line numbers.

## 7. Reproducibility implication

A valid audit citation must bind:

1. release `v0.3.0`;
2. the final proof commit of this repository;
3. the NCG identifier;
4. the elaborated type digest;
5. this historical source lock.

The source lock establishes provenance. The local kernel build establishes the
validity of the ported or composed proof.
