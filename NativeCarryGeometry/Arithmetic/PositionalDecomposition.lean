import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic

/-!
# Canonical positional decomposition at arbitrary depth

This module isolates the Euclidean arithmetic shared by every positional
camera.  For a natural base `b > 0`, a depth `k`, and an integer `n`, the
pair

`(n / b^k, n % b^k)`

is the unique quotient--residue pair whose residue lies in the canonical
window `[0, b^k)`.

No primality assumption is used.  The result is the common arithmetic source
for the later carry-mass and camera constructions.
-/

namespace NativeCarryGeometry.Internal.Carry.Positional

/-- Canonical quotient after removing the lowest `k` base-`b` positions. -/
def quotientAtDepth (b k n : ℕ) : ℕ :=
  n / b ^ k

/-- Canonical residue carried by the lowest `k` base-`b` positions. -/
def residueAtDepth (b k n : ℕ) : ℕ :=
  n % b ^ k

/--
Maximal vertical depth of `n` in base `b`.  For `b > 1` and `n > 0`, this is
the greatest exponent whose base power divides `n`.
-/
noncomputable def positionalDepth (b n : ℕ) : ℕ :=
  multiplicity b n

/--
The canonical quotient and residue reconstruct the original integer, and the
residue lies in the unique positional window at depth `k`.
-/
theorem positionalDecompositionAtDepth
    (b k n : ℕ) (hb : 0 < b) :
    residueAtDepth b k n + b ^ k * quotientAtDepth b k n = n ∧
      residueAtDepth b k n < b ^ k := by
  have hpow : 0 < b ^ k := pow_pos hb k
  exact (Nat.div_mod_unique hpow).1 ⟨rfl, rfl⟩

/--
Canonical positional decomposition: at every depth there is exactly one
quotient--residue pair with residue in `[0, b^k)`.
-/
theorem positionalDecompositionAtDepth_existsUnique
    (b k n : ℕ) (hb : 0 < b) :
    ∃! qr : ℕ × ℕ,
      qr.2 + b ^ k * qr.1 = n ∧ qr.2 < b ^ k := by
  have hpow : 0 < b ^ k := pow_pos hb k
  refine
    ⟨(quotientAtDepth b k n, residueAtDepth b k n),
      positionalDecompositionAtDepth b k n hb, ?_⟩
  rintro ⟨q, r⟩ hqr
  have hcanonical :
      n / b ^ k = q ∧ n % b ^ k = r :=
    (Nat.div_mod_unique hpow).2 hqr
  apply Prod.ext
  · exact hcanonical.1.symm
  · exact hcanonical.2.symm

/--
The depth-`k` residue is zero exactly when the depth modulus divides the
integer.  This is the arithmetic event later assigned uniform carry mass.
-/
theorem residueAtDepth_eq_zero_iff_pow_dvd
    (b k n : ℕ) :
    residueAtDepth b k n = 0 ↔ b ^ k ∣ n := by
  exact Nat.dvd_iff_mod_eq_zero.symm

/-- The positional depth is exactly the maximal base-power divisibility. -/
theorem positionalDepth_spec
    (b n : ℕ) (hb : 1 < b) (hn : 0 < n) :
    b ^ positionalDepth b n ∣ n ∧
      ¬b ^ (positionalDepth b n + 1) ∣ n := by
  have hfin : FiniteMultiplicity b n :=
    Nat.finiteMultiplicity_iff.mpr
      ⟨ne_of_gt hb, hn⟩
  constructor
  · exact pow_multiplicity_dvd b n
  · unfold positionalDepth
    exact (hfin.multiplicity_lt_iff_not_dvd).mp
      (Nat.lt_succ_self (multiplicity b n))

/--
Positional Depth Factorization.

Every positive integer in every base `b > 1` has a unique remaining core after
its maximal base power is removed.  The statement and proof remain valid for
composite bases.
-/
theorem positionalDepth_factorization_existsUnique
    (b n : ℕ) (hb : 1 < b) (hn : 0 < n) :
    ∃! m : ℕ,
      n = b ^ positionalDepth b n * m ∧ ¬b ∣ m := by
  have hfin : FiniteMultiplicity b n :=
    Nat.finiteMultiplicity_iff.mpr
      ⟨ne_of_gt hb, hn⟩
  obtain ⟨m, hfactor, hcore⟩ :=
    hfin.exists_eq_pow_mul_and_not_dvd
  have hfactor' :
      n = b ^ positionalDepth b n * m := by
    simpa [positionalDepth] using hfactor
  refine ⟨m, ⟨hfactor', hcore⟩, ?_⟩
  intro q hq
  have hpow : 0 < b ^ positionalDepth b n :=
    pow_pos (lt_trans Nat.zero_lt_one hb)
      (positionalDepth b n)
  exact Nat.mul_left_cancel hpow
    (hq.1.symm.trans hfactor')

end NativeCarryGeometry.Internal.Carry.Positional

namespace NativeCarryGeometry.Arithmetic

abbrev quotientAtDepth (b k n : ℕ) : ℕ :=
  Internal.Carry.Positional.quotientAtDepth b k n

abbrev residueAtDepth (b k n : ℕ) : ℕ :=
  Internal.Carry.Positional.residueAtDepth b k n

noncomputable abbrev positionalDepth (b n : ℕ) : ℕ :=
  Internal.Carry.Positional.positionalDepth b n

/-- NCG-POS-001: Canonical Positional Decomposition. -/
theorem positionalDecompositionAtDepth_existsUnique
    (b k n : ℕ) (hb : 0 < b) :
    ∃! qr : ℕ × ℕ,
      qr.2 + b ^ k * qr.1 = n ∧ qr.2 < b ^ k :=
  Internal.Carry.Positional.positionalDecompositionAtDepth_existsUnique
    b k n hb

/-- NCG-POS-002: Positional Depth Factorization. -/
theorem positionalDepth_factorization_existsUnique
    (b n : ℕ) (hb : 1 < b) (hn : 0 < n) :
    ∃! m : ℕ,
      n = b ^ positionalDepth b n * m ∧ ¬b ∣ m :=
  Internal.Carry.Positional.positionalDepth_factorization_existsUnique
    b n hb hn

/-- NCG-POS-003: Maximal Positional Depth. -/
theorem positionalDepth_spec
    (b n : ℕ) (hb : 1 < b) (hn : 0 < n) :
    b ^ positionalDepth b n ∣ n ∧
      ¬b ^ (positionalDepth b n + 1) ∣ n :=
  Internal.Carry.Positional.positionalDepth_spec b n hb hn

/-- NCG-POS-004: Positional Carry-Event Divisibility Criterion. -/
theorem residueAtDepth_eq_zero_iff_pow_dvd
    (b k n : ℕ) :
    residueAtDepth b k n = 0 ↔ b ^ k ∣ n :=
  Internal.Carry.Positional.residueAtDepth_eq_zero_iff_pow_dvd b k n

end NativeCarryGeometry.Arithmetic
