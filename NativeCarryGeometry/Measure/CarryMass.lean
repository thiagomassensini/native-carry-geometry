import NativeCarryGeometry.Arithmetic.CarryDepth
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace NativeCarryGeometry.Internal.Carry.Cp

noncomputable section

/-- Massa critica de uma coordenada na profundidade de carry `k`: `p^(-k)`. -/
def criticalMass (p k : ℕ) : ℝ :=
  (p : ℝ) ^ (-((k : ℝ)))

/-- Amplitude critica na profundidade `k`: `p^(-k/2)`. -/
def criticalAmplitude (p k : ℕ) : ℝ :=
  (p : ℝ) ^ (-((k : ℝ)) / 2)

/-- Amplitude do ramo na abscissa `sigma`: `p^(-k sigma)`. -/
def branchAmplitude (p : ℕ) (sigma : ℝ) (k : ℕ) : ℝ :=
  (p : ℝ) ^ (-((k : ℝ)) * sigma)

/-- Razao quadratica entre duas profundidades consecutivas. -/
def branchRatio (p : ℕ) (sigma : ℝ) : ℝ :=
  (p : ℝ) ^ (-2 * sigma)

/-- Massa quadratica de uma perna na profundidade `k`. -/
def branchMassWeight (p : ℕ) (sigma : ℝ) (k : ℕ) : ℝ :=
  (branchRatio p sigma) ^ k

/-- A amplitude critica e nao negativa. -/
theorem criticalAmplitude_nonneg (p k : ℕ) :
    0 ≤ criticalAmplitude p k := by
  unfold criticalAmplitude
  exact Real.rpow_nonneg (by positivity) _

/-- Identidade local amplitude--massa: `(p^(-k/2))^2 = p^(-k)`. -/
@[simp] theorem criticalAmplitude_sq_eq_mass (p k : ℕ) :
    (criticalAmplitude p k) ^ 2 = criticalMass p k := by
  unfold criticalAmplitude criticalMass
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  rw [← Real.rpow_mul_natCast hp0 (-((k : ℝ)) / 2) 2]
  congr 1
  ring

/-- O quadrado de `p^(-k sigma)` e a massa geometrica de razao `p^(-2 sigma)`. -/
@[simp] theorem branchAmplitude_sq_eq_massWeight
    (p : ℕ) (sigma : ℝ) (k : ℕ) :
    (branchAmplitude p sigma k) ^ 2 = branchMassWeight p sigma k := by
  unfold branchAmplitude branchMassWeight branchRatio
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  calc
    ((p : ℝ) ^ (-((k : ℝ)) * sigma)) ^ 2 =
        (p : ℝ) ^ ((-((k : ℝ)) * sigma) * (2 : ℝ)) := by
      exact (Real.rpow_mul_natCast hp0 (-((k : ℝ)) * sigma) 2).symm
    _ = (p : ℝ) ^ ((-2 * sigma) * (k : ℝ)) := by
      congr 1
      ring
    _ = ((p : ℝ) ^ (-2 * sigma)) ^ k := by
      exact Real.rpow_mul_natCast hp0 (-2 * sigma) k

/-- Em `sigma = 1/2`, a amplitude geral vira `p^(-k/2)`. -/
@[simp] theorem branchAmplitude_half (p k : ℕ) :
    branchAmplitude p ((1 : ℝ) / 2) k = criticalAmplitude p k := by
  unfold branchAmplitude criticalAmplitude
  congr 1
  ring

/-- Em `sigma = 1/2`, a massa quadratica geral vira o peso de carry `p^(-k)`. -/
@[simp] theorem branchMassWeight_half (p k : ℕ) :
    branchMassWeight p ((1 : ℝ) / 2) k = criticalMass p k := by
  calc
    branchMassWeight p ((1 : ℝ) / 2) k =
        (branchAmplitude p ((1 : ℝ) / 2) k) ^ 2 :=
      (branchAmplitude_sq_eq_massWeight p ((1 : ℝ) / 2) k).symm
    _ = (criticalAmplitude p k) ^ 2 := by rw [branchAmplitude_half]
    _ = criticalMass p k := criticalAmplitude_sq_eq_mass p k

/--
O peso `p^(-k)` ve a mesma profundidade no canal direto e no centro canonico.
-/
@[simp] theorem criticalMass_effectiveDepth_eq_centerDepth
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) :
    criticalMass p (effectiveDepth p n.1) =
      criticalMass p (centerDepth p hp hpodd n) := by
  rw [effectiveDepth_eq_centerDepth]

end
end NativeCarryGeometry.Internal.Carry.Cp

namespace NativeCarryGeometry.Measure

noncomputable section

abbrev carryMass (b k : ℕ) : ℝ :=
  Internal.Carry.Cp.criticalMass b k

abbrev criticalAmplitude (b k : ℕ) : ℝ :=
  Internal.Carry.Cp.criticalAmplitude b k

abbrev deformedAmplitude (b : ℕ) (sigma : ℝ) (k : ℕ) : ℝ :=
  Internal.Carry.Cp.branchAmplitude b sigma k

abbrev radialRatio (b : ℕ) (sigma : ℝ) : ℝ :=
  Internal.Carry.Cp.branchRatio b sigma

abbrev massWeight (b : ℕ) (sigma : ℝ) (k : ℕ) : ℝ :=
  Internal.Carry.Cp.branchMassWeight b sigma k

/-- NCG-MAS-001: Critical Amplitude-Mass Identity. -/
@[simp] theorem criticalAmplitude_sq_eq_carryMass (b k : ℕ) :
    (criticalAmplitude b k) ^ 2 = carryMass b k :=
  Internal.Carry.Cp.criticalAmplitude_sq_eq_mass b k

/-- NCG-MAS-002: Carry-Mass Depth Transport. -/
@[simp] theorem carryMass_effectiveDepth_eq_centerDepth
    (b : ℕ) (hb : Nat.Prime b) (hbodd : Odd b)
    (n : Arithmetic.Balanced.Nonmultiple b) :
    carryMass b
        (Arithmetic.Balanced.effectiveDepth b n.1) =
      carryMass b
        (Arithmetic.Balanced.centerDepth b hb hbodd n) :=
  Internal.Carry.Cp.criticalMass_effectiveDepth_eq_centerDepth
    b hb hbodd n

end
end NativeCarryGeometry.Measure
