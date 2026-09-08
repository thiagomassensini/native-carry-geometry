# Native Carry Geometry paper

This directory contains the first paper draft derived from the formal repository contract and the registered Lean theorem layer.

## Source of truth

The Lean declarations under `NativeCarryGeometry/` are the formal authority. The paper deliberately distinguishes:

- raw operator zeros;
- native-mass compatibility;
- native representation;
- the unresolved raw confinement statement.

## Draft

`native_carry_geometry.tex` is the current manuscript draft.

## Formal status

The manuscript does not claim that every raw radial zero has real coordinate `1/2`, and it does not identify the canonical continuation with the classical Riemann zeta function. Those would require separate audited theorems.

## Build

The repository currently pins Lean 4 `v4.32.0`. The formal build is documented in the root README:

`lake build --wfail NativeCarryGeometry`

PDF compilation is intentionally kept separate from the Lean audit.