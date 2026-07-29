import NativeCarryGeometry.Measure.CarryProbability
import NativeCarryGeometry.Measure.QuadraticAmplitude
import NativeCarryGeometry.Operator.BoundaryOperator

/-!
# Zero-set factorization of the real carry operator

The zero predicate retains both parts of the operator construction:

1. the quadratic domain inherited from positional carry mass;
2. convergence of the bracket resultants to zero.

The proof deliberately passes through the positional/real domain crosswalk.
This makes the formal dependency chain from carry mass to operator
factorization visible in the proof term.
-/

namespace NativeCarryGeometry.Operator

noncomputable section

/--
Complete zero predicate for the real carry operator.  Boundary closure alone is
not promoted to an operator zero after discarding the quadratic domain.
-/
def IsRealCarryOperatorZero
    (camera : ℕ) (sigma time : ℝ) : Prop :=
  RealCarryEnergyCompatible sigma time ∧
    BoundaryConvergesToZero camera sigma time

/--
NCG-OPR-004: Real Carry Operator Zero-Set Factorization.

For every natural camera width, the full zero set is the product of the unique
quadratic shell with that camera's boundary-resonance set.
-/
theorem isRealCarryOperatorZero_iff
    (camera : ℕ) (sigma time : ℝ) :
    IsRealCarryOperatorZero camera sigma time ↔
      sigma = (1 : ℝ) / 2 ∧
        IsBoundaryResonance camera time := by
  unfold IsRealCarryOperatorZero IsBoundaryResonance
  constructor
  · rintro ⟨henergy, hclose⟩
    have hpositional :
        Measure.PositionalMassCompatible 2 sigma :=
      (Measure.positionalMassCompatible_iff_realEnergyCompatible
        2 (by norm_num) sigma time).2 henergy
    have hsigma : sigma = (1 : ℝ) / 2 :=
      (Measure.positionalMassCompatible_iff
        2 (by norm_num) sigma).1 hpositional
    subst sigma
    exact ⟨rfl, hclose⟩
  · rintro ⟨hsigma, hclose⟩
    subst sigma
    have hpositional :
        Measure.PositionalMassCompatible 2 ((1 : ℝ) / 2) :=
      (Measure.positionalMassCompatible_iff
        2 (by norm_num) ((1 : ℝ) / 2)).2 rfl
    have henergy :
        RealCarryEnergyCompatible ((1 : ℝ) / 2) time :=
      (Measure.positionalMassCompatible_iff_realEnergyCompatible
        2 (by norm_num) ((1 : ℝ) / 2) time).1 hpositional
    exact ⟨henergy, hclose⟩

/-- NCG-OPR-005: Radial Confinement Corollary. -/
theorem realCarryOperatorZero_sigma_eq_half
    {camera : ℕ} {sigma time : ℝ}
    (hzero : IsRealCarryOperatorZero camera sigma time) :
    sigma = (1 : ℝ) / 2 :=
  ((isRealCarryOperatorZero_iff camera sigma time).1 hzero).1

/-- NCG-OPR-006: Off-Shell Nonvanishing Corollary. -/
theorem not_realCarryOperatorZero_of_sigma_ne_half
    {camera : ℕ} {sigma time : ℝ}
    (hoff : sigma ≠ (1 : ℝ) / 2) :
    ¬ IsRealCarryOperatorZero camera sigma time := by
  intro hzero
  exact hoff (realCarryOperatorZero_sigma_eq_half hzero)

end
end NativeCarryGeometry.Operator
