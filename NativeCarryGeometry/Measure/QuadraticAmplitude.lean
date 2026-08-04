import NativeCarryGeometry.Measure.CarryMass
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped BigOperators Topology

namespace NativeCarryGeometry.Internal.Analytic.Cp

open NativeCarryGeometry.Internal.Carry.Cp

noncomputable section

/--
Quadratic norm of the sigma-radial deformation family.  This is chart energy,
not an operator and not an operator-zero predicate.
-/
def branchNormSq (p : ℕ) (sigma : ℝ) : ℝ :=
  ((p - 1 : ℕ) : ℝ) *
    ∑' k : ℕ, branchMassWeight p sigma (k + 1)

/-- Defeito em relacao a saturacao unitaria. -/
def branchDefect (p : ℕ) (sigma : ℝ) : ℝ :=
  branchNormSq p sigma - 1

/-- Coordenada transversal comum: distancia assinada ate a linha critica. -/
def criticalDisplacement (sigma : ℝ) : ℝ :=
  sigma - (1 : ℝ) / 2

/-- A razao geometrica e positiva para uma base prima. -/
theorem branchRatio_pos (p : ℕ) (hp : Nat.Prime p) (sigma : ℝ) :
    0 < branchRatio p sigma := by
  unfold branchRatio
  apply Real.rpow_pos_of_pos
  exact_mod_cast hp.pos

/-- Para `sigma > 0`, a razao quadratica esta estritamente abaixo de um. -/
theorem branchRatio_lt_one
    (p : ℕ) (hp : Nat.Prime p) {sigma : ℝ} (hsigma : 0 < sigma) :
    branchRatio p sigma < 1 := by
  unfold branchRatio
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hp.one_lt
  · linarith

/-- Forma em norma da hipotese usada pela serie geometrica da Mathlib. -/
theorem norm_branchRatio_lt_one
    (p : ℕ) (hp : Nat.Prime p) {sigma : ℝ} (hsigma : 0 < sigma) :
    ‖branchRatio p sigma‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (branchRatio_pos p hp sigma)]
  exact branchRatio_lt_one p hp hsigma

/-- Forma fechada da serie da norma quadratica. -/
theorem branchNormSq_eq_closed
    (p : ℕ) (hp : Nat.Prime p) {sigma : ℝ} (hsigma : 0 < sigma) :
    branchNormSq p sigma =
      ((p - 1 : ℕ) : ℝ) * branchRatio p sigma *
        (1 - branchRatio p sigma)⁻¹ := by
  have hnorm := norm_branchRatio_lt_one p hp hsigma
  unfold branchNormSq branchMassWeight
  rw [← geom_series_mul_shift (branchRatio p sigma) hnorm]
  rw [tsum_geometric_of_norm_lt_one hnorm]
  ring

/-- Na meia abscissa, a razao quadratica e exatamente `1/p`. -/
@[simp] theorem branchRatio_half (p : ℕ) :
    branchRatio p ((1 : ℝ) / 2) = (p : ℝ)⁻¹ := by
  unfold branchRatio
  have hexponent : -2 * ((1 : ℝ) / 2) = (-1 : ℝ) := by ring
  rw [hexponent, Real.rpow_neg_one]

/--
Lema algebrico: com `p-1` pernas, a massa geometrica normalizada vale um
exatamente quando sua razao vale `1/p`.
-/
theorem normalizedGeometricMass_eq_one_iff
    (p : ℕ) (hp : Nat.Prime p) {q : ℝ} (hq : q < 1) :
    ((p - 1 : ℕ) : ℝ) * q * (1 - q)⁻¹ = 1 ↔
      q = (p : ℝ)⁻¹ := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  have hden : 1 - q ≠ 0 := by linarith
  rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  constructor
  · intro h
    have hdiv : (((p : ℝ) - 1) * q) / (1 - q) = 1 := by
      simpa [div_eq_mul_inv, mul_assoc] using h
    have hmul : ((p : ℝ) - 1) * q = 1 - q := by
      simpa using (div_eq_iff hden).mp hdiv
    have hqp : q * (p : ℝ) = 1 := by nlinarith
    simpa only [one_div] using (eq_div_iff hp0).2 hqp
  · intro hqeq
    rw [hqeq]
    field_simp [hp0, hp1]

/-- A razao `p^(-2 sigma)` vale `1/p` somente na meia abscissa. -/
theorem branchRatio_eq_inv_iff
    (p : ℕ) (hp : Nat.Prime p) (sigma : ℝ) :
    branchRatio p sigma = (p : ℝ)⁻¹ ↔
      sigma = (1 : ℝ) / 2 := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  constructor
  · intro hratio
    have hpow :
        (p : ℝ) ^ (-2 * sigma) = (p : ℝ) ^ (-1 : ℝ) := by
      simpa [branchRatio, Real.rpow_neg_one] using hratio
    have hexponent : -2 * sigma = (-1 : ℝ) :=
      (Real.rpow_right_inj hp0 hp1).mp hpow
    linarith
  · intro hsigma
    subst sigma
    exact branchRatio_half p

/-- A cardinalidade `p-1` da camera satura a norma em `sigma = 1/2`. -/
@[simp] theorem branchNormSq_half (p : ℕ) (hp : Nat.Prime p) :
    branchNormSq p ((1 : ℝ) / 2) = 1 := by
  rw [branchNormSq_eq_closed p hp (by norm_num), branchRatio_half]
  exact (normalizedGeometricMass_eq_one_iff p hp (by
    have hpgt : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    exact inv_lt_one_of_one_lt₀ hpgt)).2 rfl

/--
Coracao quadratico: no semiplano de convergencia, a norma do ramo vale um se,
e somente se, `sigma = 1/2`.
-/
theorem branchNormSq_eq_one_iff
    (p : ℕ) (hp : Nat.Prime p) {sigma : ℝ} (hsigma : 0 < sigma) :
    branchNormSq p sigma = 1 ↔ sigma = (1 : ℝ) / 2 := by
  rw [branchNormSq_eq_closed p hp hsigma]
  rw [normalizedGeometricMass_eq_one_iff p hp
    (branchRatio_lt_one p hp hsigma)]
  exact branchRatio_eq_inv_iff p hp sigma

/--
O defeito escalar da norma e o deslocamento critico possuem o mesmo locus
nulo de saturacao. Esse locus nao e um zero do operador.
-/
theorem branchDefect_eq_zero_iff_criticalDisplacement_eq_zero
    (p : ℕ) (hp : Nat.Prime p) {sigma : ℝ} (hsigma : 0 < sigma) :
    branchDefect p sigma = 0 ↔ criticalDisplacement sigma = 0 := by
  rw [branchDefect, sub_eq_zero]
  rw [branchNormSq_eq_one_iff p hp hsigma]
  unfold criticalDisplacement
  constructor <;> intro h <;> linarith
theorem branchAmplitude_sq_eq_criticalMass_iff_of_one_lt
    (b k : ℕ) (hb : 1 < b) (hk : 0 < k) (sigma : ℝ) :
    (branchAmplitude b sigma k) ^ 2 = criticalMass b k ↔
      sigma = (1 : ℝ) / 2 := by
  have hb0 : 0 < (b : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hb)
  have hb1 : (b : ℝ) ≠ 1 := by
    exact_mod_cast (ne_of_gt hb)
  have hk0 : 0 < (k : ℝ) := by
    exact_mod_cast hk
  constructor
  · intro hmass
    unfold branchAmplitude criticalMass at hmass
    rw [← Real.rpow_mul_natCast (le_of_lt hb0)
      (-((k : ℝ)) * sigma) 2] at hmass
    have hexponent :
        (-((k : ℝ)) * sigma) * (2 : ℝ) = -((k : ℝ)) :=
      (Real.rpow_right_inj hb0 hb1).mp hmass
    nlinarith
  · intro hsigma
    subst sigma
    rw [branchAmplitude_half]
    exact criticalAmplitude_sq_eq_mass b k

/--
Um expoente e admissivel para a geometria posicional quando sua energia
reproduz a massa de carry em toda profundidade positiva.
-/
def PositionalCarryMassCompatible (b : ℕ) (sigma : ℝ) : Prop :=
  ∀ k : ℕ, 0 < k →
    (branchAmplitude b sigma k) ^ 2 = criticalMass b k

/--
O dominio de expoentes compativeis com a massa de carry e o singleton
`{1/2}`. Basta uma profundidade positiva para obter a reciproca.
-/
theorem positionalCarryMassCompatible_iff
    (b : ℕ) (hb : 1 < b) (sigma : ℝ) :
    PositionalCarryMassCompatible b sigma ↔
      sigma = (1 : ℝ) / 2 := by
  constructor
  · intro hcompatible
    exact
      (branchAmplitude_sq_eq_criticalMass_iff_of_one_lt
        b 1 hb (by norm_num) sigma).mp
        (hcompatible 1 (by norm_num))
  · intro hsigma
    subst sigma
    intro k hk
    rw [branchAmplitude_half]
    exact criticalAmplitude_sq_eq_mass b k

/-! ## Realizacao em plano real e invariancia de fase -/

/-- Plano real de amplitudes, sem estrutura complexa. -/
abbrev PositionalAmplitudePlane := ℝ × ℝ

/-- Energia quadratica euclidiana no plano real de amplitudes. -/
def positionalPlaneEnergy (u : PositionalAmplitudePlane) : ℝ :=
  u.1 ^ 2 + u.2 ^ 2

/-- Direcao real de angulo `theta`. -/
def realRotationDirection (theta : ℝ) : PositionalAmplitudePlane :=
  (Real.cos theta, Real.sin theta)

/-- A direcao de rotacao real possui energia unitaria. -/
@[simp] theorem positionalPlaneEnergy_realRotationDirection
    (theta : ℝ) :
    positionalPlaneEnergy (realRotationDirection theta) = 1 := by
  unfold positionalPlaneEnergy realRotationDirection
  rw [add_comm, Real.sin_sq_add_cos_sq]

/-- Casca de amplitude em uma direcao real arbitraria. -/
def positionalBranchShell
    (b : ℕ) (sigma : ℝ) (k : ℕ)
    (u : PositionalAmplitudePlane) :
    PositionalAmplitudePlane :=
  (branchAmplitude b sigma k * u.1,
    branchAmplitude b sigma k * u.2)

/-- Escalar uma direcao multiplica sua energia pelo quadrado da amplitude. -/
theorem positionalPlaneEnergy_positionalBranchShell
    (b : ℕ) (sigma : ℝ) (k : ℕ)
    (u : PositionalAmplitudePlane) :
    positionalPlaneEnergy (positionalBranchShell b sigma k u) =
      (branchAmplitude b sigma k) ^ 2 * positionalPlaneEnergy u := by
  unfold positionalPlaneEnergy positionalBranchShell
  ring

/--
Em qualquer direcao unitaria, a energia da casca e exatamente o peso
quadratico do ramo.
-/
theorem positionalPlaneEnergy_shell_eq_branchMassWeight
    (b : ℕ) (sigma : ℝ) (k : ℕ)
    (u : PositionalAmplitudePlane)
    (hu : positionalPlaneEnergy u = 1) :
    positionalPlaneEnergy (positionalBranchShell b sigma k u) =
      branchMassWeight b sigma k := by
  rw [positionalPlaneEnergy_positionalBranchShell, hu, mul_one]
  exact branchAmplitude_sq_eq_massWeight b sigma k

/--
Para a orbita real `cos`/`sin`, a energia nao depende do angulo.
-/
@[simp] theorem positionalPlaneEnergy_rotatedShell_eq_branchMassWeight
    (b : ℕ) (sigma theta : ℝ) (k : ℕ) :
    positionalPlaneEnergy
        (positionalBranchShell b sigma k (realRotationDirection theta)) =
      branchMassWeight b sigma k := by
  exact positionalPlaneEnergy_shell_eq_branchMassWeight
    b sigma k (realRotationDirection theta)
    (positionalPlaneEnergy_realRotationDirection theta)

/--
Rigidez local no plano real: para qualquer angulo, igualar a energia da casca
a massa de carry equivale a `sigma = 1/2`.
-/
theorem positionalPlaneEnergy_rotatedShell_eq_criticalMass_iff
    (b k : ℕ) (hb : 1 < b) (hk : 0 < k)
    (sigma theta : ℝ) :
    positionalPlaneEnergy
        (positionalBranchShell b sigma k (realRotationDirection theta)) =
        criticalMass b k ↔
      sigma = (1 : ℝ) / 2 := by
  rw [positionalPlaneEnergy_rotatedShell_eq_branchMassWeight]
  rw [← branchAmplitude_sq_eq_massWeight]
  exact branchAmplitude_sq_eq_criticalMass_iff_of_one_lt
    b k hb hk sigma

/-! ## Saturacao global sem hipotese de primalidade -/

/-- A razao quadratica e positiva em toda base `b > 1`. -/
theorem branchRatio_pos_of_one_lt
    (b : ℕ) (hb : 1 < b) (sigma : ℝ) :
    0 < branchRatio b sigma := by
  unfold branchRatio
  apply Real.rpow_pos_of_pos
  exact_mod_cast (lt_trans Nat.zero_lt_one hb)

/-- Para `sigma > 0`, a razao quadratica esta abaixo de um em toda base. -/
theorem branchRatio_lt_one_of_one_lt
    (b : ℕ) (hb : 1 < b)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    branchRatio b sigma < 1 := by
  unfold branchRatio
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hb
  · linarith

/-- Forma em norma da condicao de convergencia geometrica. -/
theorem norm_branchRatio_lt_one_of_one_lt
    (b : ℕ) (hb : 1 < b)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    ‖branchRatio b sigma‖ < 1 := by
  rw [Real.norm_eq_abs,
    abs_of_pos (branchRatio_pos_of_one_lt b hb sigma)]
  exact branchRatio_lt_one_of_one_lt b hb hsigma

/-- Forma fechada da norma do ramo para qualquer base `b > 1`. -/
theorem branchNormSq_eq_closed_of_one_lt
    (b : ℕ) (hb : 1 < b)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    branchNormSq b sigma =
      ((b - 1 : ℕ) : ℝ) * branchRatio b sigma *
        (1 - branchRatio b sigma)⁻¹ := by
  have hnorm :=
    norm_branchRatio_lt_one_of_one_lt b hb hsigma
  unfold branchNormSq branchMassWeight
  rw [← geom_series_mul_shift (branchRatio b sigma) hnorm]
  rw [tsum_geometric_of_norm_lt_one hnorm]
  ring

/--
Com `b-1` pernas, a massa geometrica normalizada vale um exatamente quando
sua razao vale `1/b`; nenhuma fatoracao de `b` e usada.
-/
theorem normalizedGeometricMass_eq_one_iff_of_one_lt
    (b : ℕ) (hb : 1 < b)
    {q : ℝ} (hq : q < 1) :
    ((b - 1 : ℕ) : ℝ) * q * (1 - q)⁻¹ = 1 ↔
      q = (b : ℝ)⁻¹ := by
  have hb0 : (b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hb))
  have hb1 : (b : ℝ) ≠ 1 := by
    exact_mod_cast (ne_of_gt hb)
  have hden : 1 - q ≠ 0 := by
    linarith
  rw [Nat.cast_sub (Nat.le_of_lt hb), Nat.cast_one]
  constructor
  · intro h
    have hdiv : (((b : ℝ) - 1) * q) / (1 - q) = 1 := by
      simpa [div_eq_mul_inv, mul_assoc] using h
    have hmul : ((b : ℝ) - 1) * q = 1 - q := by
      simpa using (div_eq_iff hden).mp hdiv
    have hqb : q * (b : ℝ) = 1 := by
      nlinarith
    simpa only [one_div] using (eq_div_iff hb0).2 hqb
  · intro hqeq
    rw [hqeq]
    field_simp [hb0, hb1]

/-- A razao `b^(-2 sigma)` vale `1/b` somente em `sigma = 1/2`. -/
theorem branchRatio_eq_inv_iff_of_one_lt
    (b : ℕ) (hb : 1 < b) (sigma : ℝ) :
    branchRatio b sigma = (b : ℝ)⁻¹ ↔
      sigma = (1 : ℝ) / 2 := by
  have hb0 : 0 < (b : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hb)
  have hb1 : (b : ℝ) ≠ 1 := by
    exact_mod_cast (ne_of_gt hb)
  constructor
  · intro hratio
    have hpow :
        (b : ℝ) ^ (-2 * sigma) =
          (b : ℝ) ^ (-1 : ℝ) := by
      simpa [branchRatio, Real.rpow_neg_one] using hratio
    have hexponent : -2 * sigma = (-1 : ℝ) :=
      (Real.rpow_right_inj hb0 hb1).mp hpow
    linarith
  · intro hsigma
    subst sigma
    exact branchRatio_half b

/--
Coracao global sem primalidade: no semiplano de convergencia, a norma
quadratica do ramo vale um exatamente em `sigma = 1/2`.
-/
theorem branchNormSq_eq_one_iff_of_one_lt
    (b : ℕ) (hb : 1 < b)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    branchNormSq b sigma = 1 ↔
      sigma = (1 : ℝ) / 2 := by
  rw [branchNormSq_eq_closed_of_one_lt b hb hsigma]
  rw [normalizedGeometricMass_eq_one_iff_of_one_lt b hb
    (branchRatio_lt_one_of_one_lt b hb hsigma)]
  exact branchRatio_eq_inv_iff_of_one_lt b hb sigma

/--
Invariancia multibase do locus de saturacao: duas bases posicionais
arbitrarias veem exatamente o mesmo expoente admissivel.
-/
theorem branchNormSq_eq_one_base_independent
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    branchNormSq b sigma = 1 ↔
      branchNormSq c sigma = 1 := by
  rw [branchNormSq_eq_one_iff_of_one_lt b hb hsigma,
    branchNormSq_eq_one_iff_of_one_lt c hc hsigma]

end
end NativeCarryGeometry.Internal.Analytic.Cp

namespace NativeCarryGeometry.Measure

noncomputable section

/-- NCG-AMP-001: Deformed Amplitude Energy Identity. -/
@[simp] theorem deformedAmplitude_sq_eq_massWeight
    (b : ℕ) (sigma : ℝ) (k : ℕ) :
    (deformedAmplitude b sigma k) ^ 2 =
      massWeight b sigma k :=
  Internal.Carry.Cp.branchAmplitude_sq_eq_massWeight b sigma k

/-- Preferred-name form of `deformedAmplitude_sq_eq_massWeight`. -/
@[simp] theorem deformedAmplitude_sq_eq_radialEnergyWeight
    (b : ℕ) (sigma : ℝ) (k : ℕ) :
    (deformedAmplitude b sigma k) ^ 2 =
      radialEnergyWeight b sigma k :=
  deformedAmplitude_sq_eq_massWeight b sigma k

/-- NCG-AMP-002: Local Quadratic Amplitude Rigidity. -/
theorem deformedAmplitude_sq_eq_carryMass_iff
    (b k : ℕ) (hb : 1 < b) (hk : 0 < k) (sigma : ℝ) :
    (deformedAmplitude b sigma k) ^ 2 = carryMass b k ↔
      sigma = (1 : ℝ) / 2 :=
  Internal.Analytic.Cp.branchAmplitude_sq_eq_criticalMass_iff_of_one_lt
    b k hb hk sigma

abbrev PositionalMassCompatible (b : ℕ) (sigma : ℝ) : Prop :=
  Internal.Analytic.Cp.PositionalCarryMassCompatible b sigma

/-- NCG-AMP-003: Global Quadratic Amplitude Rigidity. -/
theorem positionalMassCompatible_iff
    (b : ℕ) (hb : 1 < b) (sigma : ℝ) :
    PositionalMassCompatible b sigma ↔
      sigma = (1 : ℝ) / 2 :=
  Internal.Analytic.Cp.positionalCarryMassCompatible_iff b hb sigma

abbrev radialBranchEnergy (b : ℕ) (sigma : ℝ) : ℝ :=
  Internal.Analytic.Cp.branchNormSq b sigma

/-- NCG-AMP-004: Radial Branch Saturation. -/
theorem radialBranchEnergy_eq_one_iff
    (b : ℕ) (hb : 1 < b)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    radialBranchEnergy b sigma = 1 ↔
      sigma = (1 : ℝ) / 2 :=
  Internal.Analytic.Cp.branchNormSq_eq_one_iff_of_one_lt
    b hb hsigma

/-- NCG-AMP-005: Base Independence of Saturation. -/
theorem radialBranchSaturation_base_independent
    (b c : ℕ) (hb : 1 < b) (hc : 1 < c)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    radialBranchEnergy b sigma = 1 ↔
      radialBranchEnergy c sigma = 1 :=
  Internal.Analytic.Cp.branchNormSq_eq_one_base_independent
    b c hb hc hsigma

/-- NCG-AMP-007: Critical Radial Branch Saturation. -/
theorem radialBranchEnergy_half_eq_one
    (b : ℕ) (hb : 1 < b) :
    radialBranchEnergy b ((1 : ℝ) / 2) = 1 :=
  (radialBranchEnergy_eq_one_iff b hb (by norm_num)).2 rfl

/-- NCG-AMP-008: Critical Radial Branch Nondegeneracy. -/
theorem radialBranchEnergy_half_ne_zero
    (b : ℕ) (hb : 1 < b) :
    radialBranchEnergy b ((1 : ℝ) / 2) ≠ 0 := by
  rw [radialBranchEnergy_half_eq_one b hb]
  norm_num

end
end NativeCarryGeometry.Measure
