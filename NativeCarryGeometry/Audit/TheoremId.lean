import Mathlib.Util.AssertNoSorry

/-!
# Deterministic declaration audit

This module defines the command used by the repository's generated audit
driver.  It reads a declaration from Lean's elaborated environment and emits:

* the fully qualified declaration name;
* `repr` of the elaborated type, rendered on one line;
* the sorted transitive axiom set.

The versioned preimage also contains the fully qualified declaration name,
pinned Lean version, and pinned Mathlib commit. Proof bodies and axiom lists
are intentionally not part of the signature digest; Git commit and release
metadata identify the former, while `audit/axioms.json` records the latter.
-/

namespace NativeCarryGeometry.Audit

open Lean Elab Command

/--
Emit a machine-readable, tab-separated audit record for one elaborated
declaration.  The `repr` encoding is intentionally tied to the pinned Lean
toolchain and is versioned by the external preimage format.
-/
elab "#ncg_audit " n:ident : command => do
  let name ← liftCoreM <|
    Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  let env ← getEnv
  let some info := env.find? name
    | throwError "unknown declaration: {name}"
  let typeRecord := (repr info.type).pretty 1000000
  let axiomSet ← Lean.collectAxioms name
  let axioms := axiomSet.qsort Name.lt
  let axiomRecord :=
    String.intercalate "," (axioms.toList.map toString)
  logInfo m!"NCG_AUDIT\t{name}\t{typeRecord}\t{axiomRecord}"

end NativeCarryGeometry.Audit
