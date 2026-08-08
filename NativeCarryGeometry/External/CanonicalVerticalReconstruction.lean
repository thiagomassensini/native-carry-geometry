import Mathlib

/-!
# Canonical vertical reconstruction

This module transports the lossless vertical core from the historical formal
development into the native repository without placing it in the public audit
root.  A finitely supported edge state is inserted coordinate-for-coordinate
in ell squared.  The weighted bracket, Green operator, boundary trace, and
return then satisfy the exact reconstruction identity.

Source provenance:
thiagomassensini/primos,
CPFormal/Analytic/CpNativeGpreTfvdCanonicalGluing.lean,
main at 0c64a8366ded96a3242cbe0888c55144442c570b.
-/

open scoped BigOperators lp ENNReal NNReal

namespace NativeCarryGeometry.External

noncomputable section

/-- Causal Green kernel in carry-amplitude coordinates. -/
def carryWeightedVerticalGreenKernel (q : ℝ) (r : ℕ) : ℝ :=
  (r : ℝ) * q ^ r

@[simp] theorem carryWeightedVerticalGreenKernel_zero (q : ℝ) :
    carryWeightedVerticalGreenKernel q 0 = 0 := by
  simp [carryWeightedVerticalGreenKernel]

theorem carryWeightedVerticalGreenKernel_nonneg
    {q : ℝ} (hq : 0 ≤ q) (r : ℕ) :
    0 ≤ carryWeightedVerticalGreenKernel q r := by
  unfold carryWeightedVerticalGreenKernel
  positivity

theorem carryWeightedVerticalGreenKernel_summable
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (carryWeightedVerticalGreenKernel q) := by
  let a : ℝ := (q + 1) / 2
  have hqa : q < a := by
    dsimp [a]
    linarith
  have ha1 : a < 1 := by
    dsimp [a]
    linarith
  have ha0 : 0 ≤ a := by
    dsimp [a]
    linarith
  have hgeom : Summable (fun n : ℕ => a ^ n) :=
    summable_geometric_of_lt_one ha0 ha1
  have hnorm : ‖q‖ < a := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hqa
  have hlittle :
      (fun n : ℕ => (n : ℝ) * q ^ n) =o[Filter.atTop]
        (fun n : ℕ => a ^ n) := by
    simpa only [pow_one] using
      (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt
        (R := ℝ) 1 hnorm)
  rcases hlittle.isBigO.exists_pos with ⟨C, _hCpos, hC⟩
  have hmajor : Summable (fun n : ℕ => C * a ^ n) :=
    hgeom.mul_left C
  refine hmajor.of_norm_bounded_eventually_nat ?_
  filter_upwards [hC.bound] with n hn
  simpa [carryWeightedVerticalGreenKernel, Real.norm_eq_abs,
    abs_of_nonneg hq0, abs_of_nonneg ha0] using hn

/-- A contractive family of vertical shifts. -/
structure CarryVerticalShiftFamily (H : Type*)
    [NormedAddCommGroup H] [NormedSpace ℂ H] where
  shift : ℕ → H →L[ℂ] H
  norm_shift_le_one : ∀ r : ℕ, ‖shift r‖ ≤ 1

section ShiftFamily

variable {H : Type*}
variable [NormedAddCommGroup H] [NormedSpace ℂ H]

def carryWeightedVerticalGreenTerm
    (S : CarryVerticalShiftFamily H) (q : ℝ) (r : ℕ) : H →L[ℂ] H :=
  (carryWeightedVerticalGreenKernel q r : ℂ) • S.shift r

theorem carryWeightedVerticalGreenTerm_norm_le
    (S : CarryVerticalShiftFamily H) {q : ℝ} (hq0 : 0 ≤ q) (r : ℕ) :
    ‖carryWeightedVerticalGreenTerm S q r‖ ≤
      carryWeightedVerticalGreenKernel q r := by
  have hk0 : 0 ≤ carryWeightedVerticalGreenKernel q r :=
    carryWeightedVerticalGreenKernel_nonneg hq0 r
  calc
    ‖carryWeightedVerticalGreenTerm S q r‖ ≤
        ‖(carryWeightedVerticalGreenKernel q r : ℂ)‖ * ‖S.shift r‖ := by
      rw [carryWeightedVerticalGreenTerm]
      exact norm_smul_le
        (carryWeightedVerticalGreenKernel q r : ℂ) (S.shift r)
    _ = carryWeightedVerticalGreenKernel q r * ‖S.shift r‖ := by
      simp [abs_of_nonneg hk0]
    _ ≤ carryWeightedVerticalGreenKernel q r * 1 :=
      mul_le_mul_of_nonneg_left (S.norm_shift_le_one r) hk0
    _ = carryWeightedVerticalGreenKernel q r := by ring

theorem carryWeightedVerticalGreenTerm_summable
    [CompleteSpace H]
    (S : CarryVerticalShiftFamily H) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun r : ℕ => carryWeightedVerticalGreenTerm S q r) :=
  (carryWeightedVerticalGreenKernel_summable hq0 hq1).of_norm_bounded
    (fun r => carryWeightedVerticalGreenTerm_norm_le S hq0 r)

def carryWeightedVerticalGreen
    [CompleteSpace H]
    (S : CarryVerticalShiftFamily H) (q : ℝ) : H →L[ℂ] H :=
  ∑' r : ℕ, carryWeightedVerticalGreenTerm S q r

end ShiftFamily

/-- Canonical vertical Hilbert space. -/
abbrev CarryVerticalL2 := ℓ²(ℕ, ℂ)

def carryVerticalL2BackwardShiftLinear (r : ℕ) :
    CarryVerticalL2 →ₗ[ℂ] CarryVerticalL2 where
  toFun x :=
    ⟨fun n => x (n + r), by
      change Memℓp (fun n : ℕ => x (n + r)) 2
      rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
      exact (summable_nat_add_iff r).2
        ((lp.memℓp x).summable
          (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩
  map_add' x y := by
    ext n
    rfl
  map_smul' c x := by
    ext n
    rfl

@[simp] theorem carryVerticalL2BackwardShiftLinear_apply
    (r : ℕ) (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2BackwardShiftLinear r x n = x (n + r) := rfl

theorem carryVerticalL2BackwardShiftLinear_norm_le
    (r : ℕ) (x : CarryVerticalL2) :
    ‖carryVerticalL2BackwardShiftLinear r x‖ ≤ ‖x‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp]
  rw [lp.norm_rpow_eq_tsum hp, lp.norm_rpow_eq_tsum hp]
  simp only [carryVerticalL2BackwardShiftLinear_apply]
  have hx : Summable (fun n : ℕ => ‖x n‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.memℓp x).summable hp
  have hsplit := hx.sum_add_tsum_nat_add r
  rw [← hsplit]
  exact le_add_of_nonneg_left
    (Finset.sum_nonneg fun n hn => by positivity)

def carryVerticalL2BackwardShift (r : ℕ) :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  LinearMap.mkContinuous (carryVerticalL2BackwardShiftLinear r) 1
    (fun x => by
      change ‖carryVerticalL2BackwardShiftLinear r x‖ ≤ 1 * ‖x‖
      simpa using carryVerticalL2BackwardShiftLinear_norm_le r x)

@[simp] theorem carryVerticalL2BackwardShift_apply
    (r : ℕ) (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2BackwardShift r x n = x (n + r) := rfl

theorem carryVerticalL2BackwardShift_norm_le_one (r : ℕ) :
    ‖carryVerticalL2BackwardShift r‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  change ‖carryVerticalL2BackwardShiftLinear r x‖ ≤ 1 * ‖x‖
  simpa using carryVerticalL2BackwardShiftLinear_norm_le r x

theorem carryVerticalL2BackwardShift_single (r k : ℕ) :
    carryVerticalL2BackwardShift r (lp.single 2 k (1 : ℂ)) =
      if r ≤ k then lp.single 2 (k - r) (1 : ℂ) else 0 := by
  ext n
  by_cases hrk : r ≤ k
  · have hiff : n + r = k ↔ n = k - r := by omega
    simp [carryVerticalL2BackwardShift_apply, lp.single_apply,
      Pi.single_apply, hrk, hiff]
  · have hne : n + r ≠ k := by omega
    simp [carryVerticalL2BackwardShift_apply, lp.single_apply, hrk, hne]

def carryVerticalL2UnilateralShift (r : ℕ) :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  ContinuousLinearMap.adjoint (carryVerticalL2BackwardShift r)

@[simp] theorem carryVerticalL2UnilateralShift_apply
    (r : ℕ) (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2UnilateralShift r x n =
      if r ≤ n then x (n - r) else 0 := by
  have hinner :
      inner ℂ (lp.single 2 n (1 : ℂ))
          (carryVerticalL2UnilateralShift r x) =
        inner ℂ
          (carryVerticalL2BackwardShift r
            (lp.single 2 n (1 : ℂ))) x := by
    exact ContinuousLinearMap.adjoint_inner_right
      (carryVerticalL2BackwardShift r) (lp.single 2 n (1 : ℂ)) x
  by_cases hrn : r ≤ n
  · simpa [carryVerticalL2UnilateralShift,
      carryVerticalL2BackwardShift_single, hrn,
      lp.inner_single_left] using hinner
  · simpa [carryVerticalL2UnilateralShift,
      carryVerticalL2BackwardShift_single, hrn,
      lp.inner_single_left] using hinner

theorem carryVerticalL2UnilateralShift_norm_le_one (r : ℕ) :
    ‖carryVerticalL2UnilateralShift r‖ ≤ 1 := by
  calc
    ‖carryVerticalL2UnilateralShift r‖ =
        ‖carryVerticalL2BackwardShift r‖ :=
      ContinuousLinearMap.adjoint.norm_map _
    _ ≤ 1 := carryVerticalL2BackwardShift_norm_le_one r

def carryVerticalL2ShiftFamily : CarryVerticalShiftFamily CarryVerticalL2 where
  shift := carryVerticalL2UnilateralShift
  norm_shift_le_one := carryVerticalL2UnilateralShift_norm_le_one

def carryVerticalL2WeightedGreen (q : ℝ) :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  carryWeightedVerticalGreen carryVerticalL2ShiftFamily q

def carryVerticalL2EvalLinear (n : ℕ) : CarryVerticalL2 →ₗ[ℂ] ℂ where
  toFun x := x n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def carryVerticalL2Eval (n : ℕ) : CarryVerticalL2 →L[ℂ] ℂ :=
  LinearMap.mkContinuous (carryVerticalL2EvalLinear n) 1
    (fun x => by
      change ‖x n‖ ≤ 1 * ‖x‖
      simpa using lp.norm_apply_le_norm (p := (2 : ℝ≥0∞))
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) x n)

@[simp] theorem carryVerticalL2Eval_apply
    (n : ℕ) (x : CarryVerticalL2) :
    carryVerticalL2Eval n x = x n := rfl

def carryVerticalL2ZeroHeadProjection :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  ContinuousLinearMap.id ℂ CarryVerticalL2 -
    (ContinuousLinearMap.toSpanSingleton ℂ
        (lp.single 2 0 (1 : ℂ)) ∘L carryVerticalL2Eval 0)

@[simp] theorem carryVerticalL2ZeroHeadProjection_apply
    (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2ZeroHeadProjection x n =
      if n = 0 then 0 else x n := by
  by_cases hn : n = 0
  · subst n
    simp [carryVerticalL2ZeroHeadProjection, lp.single_apply]
  · simp [carryVerticalL2ZeroHeadProjection, lp.single_apply, hn]

def carryWeightedVerticalCenteredBracketCore (q : ℝ) :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  ((q : ℂ)⁻¹) • carryVerticalL2BackwardShift 1 -
    (2 : ℂ) • ContinuousLinearMap.id ℂ CarryVerticalL2 +
    (q : ℂ) • carryVerticalL2UnilateralShift 1

@[simp] theorem carryWeightedVerticalCenteredBracketCore_apply
    (q : ℝ) (x : CarryVerticalL2) (n : ℕ) :
    carryWeightedVerticalCenteredBracketCore q x n =
      (q : ℂ)⁻¹ * x (n + 1) - 2 * x n +
        (q : ℂ) * (if 1 ≤ n then x (n - 1) else 0) := by
  change
    (q : ℂ)⁻¹ * x (n + 1) - 2 * x n +
        (q : ℂ) * (carryVerticalL2UnilateralShift 1 x n) =
      (q : ℂ)⁻¹ * x (n + 1) - 2 * x n +
        (q : ℂ) * (if 1 ≤ n then x (n - 1) else 0)
  rw [carryVerticalL2UnilateralShift_apply]

def carryWeightedVerticalCenteredBracket (q : ℝ) :
    CarryVerticalL2 →L[ℂ] CarryVerticalL2 :=
  carryVerticalL2ZeroHeadProjection ∘L
    carryWeightedVerticalCenteredBracketCore q

@[simp] theorem carryWeightedVerticalCenteredBracket_zero
    (q : ℝ) (x : CarryVerticalL2) :
    carryWeightedVerticalCenteredBracket q x 0 = 0 := by
  simp [carryWeightedVerticalCenteredBracket]

@[simp] theorem carryWeightedVerticalCenteredBracket_succ
    (q : ℝ) (x : CarryVerticalL2) (n : ℕ) :
    carryWeightedVerticalCenteredBracket q x (n + 1) =
      (q : ℂ)⁻¹ * x (n + 2) - 2 * x (n + 1) +
        (q : ℂ) * x n := by
  simp [carryWeightedVerticalCenteredBracket, Nat.add_assoc]

def carryWeightedVerticalTrace (q : ℝ) :
    CarryVerticalL2 →L[ℂ] (ℂ × ℂ) :=
  (carryVerticalL2Eval 0).prod
    (((q : ℂ)⁻¹) • carryVerticalL2Eval 1 - carryVerticalL2Eval 0)

@[simp] theorem carryWeightedVerticalTrace_apply
    (q : ℝ) (x : CarryVerticalL2) :
    carryWeightedVerticalTrace q x =
      (x 0, (q : ℂ)⁻¹ * x 1 - x 0) := by
  simp [carryWeightedVerticalTrace]

def carryGeometricAmplitudeVector
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) : CarryVerticalL2 :=
  ⟨fun n : ℕ => (q : ℂ) ^ n, by
    have hsum : Summable (fun n : ℕ => ‖(q : ℂ) ^ n‖) := by
      simpa [norm_pow, abs_of_nonneg hq0] using
        (summable_geometric_of_lt_one hq0 hq1)
    have hmem1 : Memℓp (fun n : ℕ => (q : ℂ) ^ n) 1 := by
      rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
      simpa using hsum
    exact hmem1.of_exponent_ge
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩

@[simp] theorem carryGeometricAmplitudeVector_apply
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    carryGeometricAmplitudeVector q hq0 hq1 n = (q : ℂ) ^ n := rfl

def carryAffineSlopeAmplitudeVector
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) : CarryVerticalL2 :=
  ⟨fun n : ℕ => (carryWeightedVerticalGreenKernel q n : ℂ), by
    have hsumReal : Summable (carryWeightedVerticalGreenKernel q) :=
      carryWeightedVerticalGreenKernel_summable hq0 hq1
    have hsumNorm : Summable
        (fun n : ℕ => ‖(carryWeightedVerticalGreenKernel q n : ℂ)‖) := by
      refine hsumReal.congr ?_
      intro n
      simp [abs_of_nonneg
        (carryWeightedVerticalGreenKernel_nonneg hq0 n)]
    have hmem1 : Memℓp
        (fun n : ℕ => (carryWeightedVerticalGreenKernel q n : ℂ)) 1 := by
      rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
      simpa using hsumNorm
    exact hmem1.of_exponent_ge
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩

@[simp] theorem carryAffineSlopeAmplitudeVector_apply
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    carryAffineSlopeAmplitudeVector q hq0 hq1 n =
      (carryWeightedVerticalGreenKernel q n : ℂ) := rfl

def carryWeightedVerticalReturn
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (ℂ × ℂ) →L[ℂ] CarryVerticalL2 :=
  (ContinuousLinearMap.toSpanSingleton ℂ
      (carryGeometricAmplitudeVector q hq0 hq1) ∘L
        ContinuousLinearMap.fst ℂ ℂ ℂ) +
  (ContinuousLinearMap.toSpanSingleton ℂ
      (carryAffineSlopeAmplitudeVector q hq0 hq1) ∘L
        ContinuousLinearMap.snd ℂ ℂ ℂ)

@[simp] theorem carryWeightedVerticalReturn_apply
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (boundary : ℂ × ℂ) (n : ℕ) :
    carryWeightedVerticalReturn q hq0 hq1 boundary n =
      (q : ℂ) ^ n * (boundary.1 + (n : ℂ) * boundary.2) := by
  rcases boundary with ⟨a, b⟩
  simp [carryWeightedVerticalReturn,
    carryWeightedVerticalGreenKernel]
  ring

def carryWeightedScalarFirstDifference
    (q : ℂ) (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  q⁻¹ * x (n + 1) - x n

def carryWeightedScalarSecondDifference
    (q : ℂ) (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  carryWeightedScalarFirstDifference q x (n + 1) -
    q * carryWeightedScalarFirstDifference q x n

theorem carryWeightedScalarSecondDifference_eq
    {q : ℂ} (hq : q ≠ 0) (x : ℕ → ℂ) (n : ℕ) :
    carryWeightedScalarSecondDifference q x n =
      q⁻¹ * x (n + 2) - 2 * x (n + 1) + q * x n := by
  unfold carryWeightedScalarSecondDifference
    carryWeightedScalarFirstDifference
  simp only [Nat.add_assoc]
  field_simp [hq]
  ring

def carryWeightedScalarGreenSum
    (q : ℂ) (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range n,
    ((n - 1 - j : ℕ) : ℂ) * q ^ (n - 1 - j) *
      carryWeightedScalarSecondDifference q x j

theorem sum_range_forwardDifference
    {R : Type*} [CommRing R] (f : ℕ → R) (start length : ℕ) :
    (∑ r ∈ Finset.range length,
      (f (start + r + 1) - f (start + r))) =
        f (start + length) - f start := by
  induction length with
  | zero => simp
  | succ length ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.add_succ]
      ring

theorem carryWeightedScalarSecondDifference_telescope
    (q : ℂ) (x : ℕ → ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range n,
      q ^ (n - 1 - j) * carryWeightedScalarSecondDifference q x j) =
        carryWeightedScalarFirstDifference q x n -
          q ^ n * carryWeightedScalarFirstDifference q x 0 := by
  let d : ℕ → ℂ := fun k => carryWeightedScalarFirstDifference q x k
  let F : ℕ → ℂ := fun k => q ^ (n - k) * d k
  calc
    (∑ j ∈ Finset.range n,
      q ^ (n - 1 - j) * carryWeightedScalarSecondDifference q x j) =
        ∑ j ∈ Finset.range n, (F (j + 1) - F j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjlt : j < n := Finset.mem_range.mp hj
          have hleft : n - (j + 1) = n - 1 - j := by omega
          have hright : n - j = (n - 1 - j) + 1 := by omega
          dsimp [F, d, carryWeightedScalarSecondDifference]
          rw [hleft, hright, pow_succ]
          ring
    _ = F (0 + n) - F 0 := by
      simpa using (sum_range_forwardDifference F 0 n)
    _ = carryWeightedScalarFirstDifference q x n -
          q ^ n * carryWeightedScalarFirstDifference q x 0 := by
      simp [F, d]

theorem carryWeightedScalarGreenSum_succ
    (q : ℂ) (x : ℕ → ℂ) (n : ℕ) :
    carryWeightedScalarGreenSum q x (n + 1) =
      q * carryWeightedScalarGreenSum q x n +
        q * (carryWeightedScalarFirstDifference q x n -
          q ^ n * carryWeightedScalarFirstDifference q x 0) := by
  rw [← carryWeightedScalarSecondDifference_telescope q x n]
  unfold carryWeightedScalarGreenSum
  rw [Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.cast_zero,
    zero_mul, add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < n := Finset.mem_range.mp hj
  have hsub : n - j = (n - 1 - j) + 1 := by omega
  rw [hsub, pow_succ]
  push_cast
  ring

theorem carryWeightedScalarReconstruction
    {q : ℂ} (hq : q ≠ 0) (x : ℕ → ℂ) (n : ℕ) :
    x n =
      q ^ n *
          (x 0 + (n : ℂ) * carryWeightedScalarFirstDifference q x 0) +
        carryWeightedScalarGreenSum q x n := by
  induction n with
  | zero =>
      simp [carryWeightedScalarGreenSum]
  | succ n ih =>
      calc
        x (n + 1) =
            q * x n + q * carryWeightedScalarFirstDifference q x n := by
              unfold carryWeightedScalarFirstDifference
              field_simp [hq]
              ring
        _ = q *
              (q ^ n *
                  (x 0 + (n : ℂ) *
                    carryWeightedScalarFirstDifference q x 0) +
                carryWeightedScalarGreenSum q x n) +
              q * carryWeightedScalarFirstDifference q x n := by
                rw [ih]
        _ = q ^ (n + 1) *
              (x 0 + ((n + 1 : ℕ) : ℂ) *
                carryWeightedScalarFirstDifference q x 0) +
              carryWeightedScalarGreenSum q x (n + 1) := by
                rw [carryWeightedScalarGreenSum_succ]
                rw [pow_succ]
                push_cast
                ring

def carryVerticalL2OperatorApply (x : CarryVerticalL2) :
    (CarryVerticalL2 →L[ℂ] CarryVerticalL2) →L[ℂ] CarryVerticalL2 :=
  LinearMap.mkContinuous
    { toFun := fun T => T x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ‖x‖
    (fun T => by
      simpa [mul_comm] using T.le_opNorm x)

def carryVerticalL2OperatorCoordinate
    (x : CarryVerticalL2) (n : ℕ) :
    (CarryVerticalL2 →L[ℂ] CarryVerticalL2) →L[ℂ] ℂ :=
  carryVerticalL2Eval n ∘L carryVerticalL2OperatorApply x

@[simp] theorem carryVerticalL2OperatorCoordinate_apply
    (x : CarryVerticalL2) (n : ℕ)
    (T : CarryVerticalL2 →L[ℂ] CarryVerticalL2) :
    carryVerticalL2OperatorCoordinate x n T = T x n := rfl

theorem carryVerticalL2WeightedGreen_apply
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2WeightedGreen q x n =
      ∑ r ∈ Finset.range (n + 1),
        (carryWeightedVerticalGreenKernel q r : ℂ) * x (n - r) := by
  have hsum : Summable (fun r : ℕ =>
      carryWeightedVerticalGreenTerm carryVerticalL2ShiftFamily q r) :=
    carryWeightedVerticalGreenTerm_summable
      carryVerticalL2ShiftFamily hq0 hq1
  rw [carryVerticalL2WeightedGreen, carryWeightedVerticalGreen]
  change
    carryVerticalL2OperatorCoordinate x n
        (∑' r : ℕ,
          carryWeightedVerticalGreenTerm carryVerticalL2ShiftFamily q r) = _
  rw [(carryVerticalL2OperatorCoordinate x n).map_tsum hsum]
  rw [tsum_eq_sum (s := Finset.range (n + 1)) (fun r hr => by
    have hrge : n + 1 ≤ r := by
      simpa only [Finset.mem_range, not_lt] using hr
    have hrnot : ¬r ≤ n := by omega
    simp [carryWeightedVerticalGreenTerm, carryVerticalL2ShiftFamily,
      carryVerticalL2UnilateralShift_apply, hrnot])]
  apply Finset.sum_congr rfl
  intro r hr
  have hrlt : r < n + 1 := Finset.mem_range.mp hr
  have hrle : r ≤ n := by omega
  simp [carryWeightedVerticalGreenTerm, carryVerticalL2ShiftFamily,
    carryVerticalL2UnilateralShift_apply, hrle]

theorem carryVerticalL2WeightedGreen_apply_reindexed
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2WeightedGreen q x n =
      ∑ j ∈ Finset.range (n + 1),
        (carryWeightedVerticalGreenKernel q (n - j) : ℂ) * x j := by
  rw [carryVerticalL2WeightedGreen_apply q hq0 hq1]
  calc
    (∑ r ∈ Finset.range (n + 1),
        (carryWeightedVerticalGreenKernel q r : ℂ) * x (n - r)) =
      ∑ r ∈ Finset.range (n + 1),
        (carryWeightedVerticalGreenKernel q
            (n - (n + 1 - 1 - r)) : ℂ) *
          x (n + 1 - 1 - r) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrlt : r < n + 1 := Finset.mem_range.mp hr
        have hrle : r ≤ n := by omega
        have hleft : n + 1 - 1 - r = n - r := by omega
        have hright : n - (n - r) = r := by omega
        rw [hleft, hright]
    _ = ∑ j ∈ Finset.range (n + 1),
        (carryWeightedVerticalGreenKernel q (n - j) : ℂ) * x j :=
      Finset.sum_range_reflect
        (fun j =>
          (carryWeightedVerticalGreenKernel q (n - j) : ℂ) * x j)
        (n + 1)

theorem carryVerticalL2WeightedGreen_bracket_apply
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2WeightedGreen q
        (carryWeightedVerticalCenteredBracket q x) n =
      carryWeightedScalarGreenSum (q : ℂ) x n := by
  rw [carryVerticalL2WeightedGreen_apply_reindexed q hqpos.le hq1]
  rw [Finset.sum_range_succ']
  simp only [carryWeightedVerticalCenteredBracket_zero, mul_zero, add_zero]
  unfold carryWeightedScalarGreenSum
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < n := Finset.mem_range.mp hj
  have hsub : n - (j + 1) = n - 1 - j := by omega
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqpos.ne'
  rw [hsub, carryWeightedVerticalCenteredBracket_succ,
    carryWeightedScalarSecondDifference_eq hqC]
  simp [carryWeightedVerticalGreenKernel]

theorem carryWeightedVerticalTfvd_apply
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (x : CarryVerticalL2) (n : ℕ) :
    carryVerticalL2WeightedGreen q
          (carryWeightedVerticalCenteredBracket q x) n +
        carryWeightedVerticalReturn q hqpos.le hq1
          (carryWeightedVerticalTrace q x) n =
      x n := by
  rw [carryVerticalL2WeightedGreen_bracket_apply q hqpos hq1]
  rw [carryWeightedVerticalReturn_apply,
    carryWeightedVerticalTrace_apply]
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hqpos.ne'
  have hrec := carryWeightedScalarReconstruction
    (q := (q : ℂ)) hqC (fun k => x k) n
  simpa [carryWeightedScalarFirstDifference, add_comm] using hrec.symm

theorem carryWeightedVerticalTfvd_identity
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1) :
    carryVerticalL2WeightedGreen q ∘L
          carryWeightedVerticalCenteredBracket q +
        carryWeightedVerticalReturn q hqpos.le hq1 ∘L
          carryWeightedVerticalTrace q =
      ContinuousLinearMap.id ℂ CarryVerticalL2 := by
  apply ContinuousLinearMap.ext
  intro x
  ext n
  simpa using carryWeightedVerticalTfvd_apply q hqpos hq1 x n

/-- Finitely supported native edge core. -/
abbrev NativeVerticalCore := ℕ →₀ ℂ

/-- Coordinate-for-coordinate inclusion of the finite core into ell squared. -/
noncomputable def nativeCanonicalVerticalRealization :
    NativeVerticalCore →ₗ[ℂ] CarryVerticalL2 where
  toFun x :=
    ⟨fun n : ℕ => x n, by
      change Memℓp (fun n : ℕ => x n) 2
      rw [memℓp_gen_iff
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
      refine summable_of_ne_finset_zero (s := x.support) ?_
      intro n hn
      have hx : x n = 0 := Finsupp.notMem_support_iff.mp hn
      simp [hx]⟩
  map_add' x y := by
    ext n
    rfl
  map_smul' a x := by
    ext n
    rfl

@[simp] theorem nativeCanonicalVerticalRealization_apply
    (x : NativeVerticalCore) (n : ℕ) :
    nativeCanonicalVerticalRealization x n = x n := rfl

theorem nativeCanonicalVerticalRealization_injective :
    Function.Injective nativeCanonicalVerticalRealization := by
  intro x y hxy
  apply Finsupp.ext
  intro n
  have hcoord := congrArg (fun z : CarryVerticalL2 => z n) hxy
  simpa using hcoord

abbrev NativeTfvdProductState :=
  CarryVerticalL2 × NativeVerticalCore

def nativeCanonicalTfvdGlue :
    NativeVerticalCore →ₗ[ℂ] NativeTfvdProductState :=
  nativeCanonicalVerticalRealization.prod LinearMap.id

@[simp] theorem nativeCanonicalTfvdGlue_apply
    (x : NativeVerticalCore) :
    nativeCanonicalTfvdGlue x =
      (nativeCanonicalVerticalRealization x, x) := rfl

theorem nativeCanonicalTfvdGlue_injective :
    Function.Injective nativeCanonicalTfvdGlue := by
  intro x y hxy
  have hsnd := congrArg Prod.snd hxy
  simpa using hsnd

/-- Exact reconstruction of the vertical leg of the same finite core. -/
theorem nativeCanonicalTfvd_vertical_reconstruction
    (q : ℝ) (hqpos : 0 < q) (hq1 : q < 1)
    (x : NativeVerticalCore) :
    carryVerticalL2WeightedGreen q
          (carryWeightedVerticalCenteredBracket q
            (nativeCanonicalVerticalRealization x)) +
        carryWeightedVerticalReturn q hqpos.le hq1
          (carryWeightedVerticalTrace q
            (nativeCanonicalVerticalRealization x)) =
      nativeCanonicalVerticalRealization x := by
  ext n
  exact carryWeightedVerticalTfvd_apply
    q hqpos hq1 (nativeCanonicalVerticalRealization x) n

end

end NativeCarryGeometry.External
