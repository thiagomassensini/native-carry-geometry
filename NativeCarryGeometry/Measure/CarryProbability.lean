import NativeCarryGeometry.Arithmetic.PositionalDecomposition
import NativeCarryGeometry.Measure.CarryMass
import Mathlib.Tactic


/-!
# Uniform probability of a positional carry event

At depth `k`, the residue space of a positional base `b` has exactly `b^k`
equiprobable classes.  A specified carry condition is one congruence class,
so its finite uniform probability is `1 / b^k`.

This module proves that statement as a cardinality calculation and then
identifies it with the already formalized carry mass `b^(-k)`.  The proof uses
only `0 < b`; no primality assumption enters.
-/

namespace NativeCarryGeometry.Internal.Carry.Positional

open NativeCarryGeometry.Internal.Carry.Cp

noncomputable section

/-- Probability of an event in a finite uniform residue space. -/
def uniformFiniteProbability
    {N : ℕ} (event : Finset (Fin N)) : ℝ :=
  (event.card : ℝ) / (N : ℝ)

/--
The distinguished congruence class in a nonempty residue space.  Translating
this singleton gives any other specified carry congruence class with the same
probability.
-/
def uniformCarryEvent
    (N : ℕ) (hN : 0 < N) : Finset (Fin N) :=
  {⟨0, hN⟩}

/-- A carry event occupies exactly one residue class. -/
@[simp] theorem card_uniformCarryEvent
    (N : ℕ) (hN : 0 < N) :
    (uniformCarryEvent N hN).card = 1 := by
  simp [uniformCarryEvent]

/--
Uniform Carry Probability Law.

For every positive positional base and every depth, the probability of the
zero-residue carry class is exactly the carry mass `b^(-k)`.
-/
theorem uniformCarryEvent_probability
    (b k : ℕ) (hb : 0 < b) :
    uniformFiniteProbability
        (uniformCarryEvent (b ^ k) (pow_pos hb k)) =
      criticalMass b k := by
  simp [uniformFiniteProbability, uniformCarryEvent, criticalMass,
    Real.rpow_neg_natCast, Nat.cast_pow, div_eq_mul_inv]

end

end NativeCarryGeometry.Internal.Carry.Positional

namespace NativeCarryGeometry.Measure

noncomputable abbrev uniformFiniteProbability
    {N : ℕ} (event : Finset (Fin N)) : ℝ :=
  Internal.Carry.Positional.uniformFiniteProbability event

abbrev uniformCarryEvent
    (N : ℕ) (hN : 0 < N) : Finset (Fin N) :=
  Internal.Carry.Positional.uniformCarryEvent N hN

/-- NCG-PRB-001: Uniform Carry Probability Law. -/
theorem uniformCarryEvent_probability
    (b k : ℕ) (hb : 0 < b) :
    uniformFiniteProbability
        (uniformCarryEvent (b ^ k) (pow_pos hb k)) =
      carryMass b k :=
  Internal.Carry.Positional.uniformCarryEvent_probability b k hb

end NativeCarryGeometry.Measure
