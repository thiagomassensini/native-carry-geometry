import NativeCarryGeometry.Analytic.BracketSeries
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.Basic


/-!
# Holomorfia e unicidade da continuacao da carta Cp bracketada

Este modulo fecha a passagem analitica minima da construcao bracketada.
Cada bloco e uma soma finita de potencias complexas de bases positivas e,
portanto, e inteiro na variavel `s`. Em torno de cada ponto de

`bracketHalfPlane = {s | -1 < re(s)}`

escolhemos uma bola que permanece afastada da reta `re(s) = -1`. Nessa bola,
o fator quadratico `‖s * (s + 1)‖` e uniformemente limitado, enquanto os
expoentes sao dominados por uma unica p-serie somavel. O criterio de
Weierstrass de Mathlib fornece entao a holomorfia da cauda e da carta.

O ultimo teorema aplica o principio da identidade. Ele diz precisamente que
a carta bracketada e a unica funcao analitica no semiplano `re(s)>-1` que
coincide com o fator Genuine no subsemiplano `re(s)>1`.
-/

open scoped BigOperators Topology

namespace NativeCarryGeometry.Internal.Analytic.Cp

open NativeCarryGeometry.Internal.Genuine.Cp
open Filter Metric Set

noncomputable section

attribute [local instance 10000]
  NormedAddCommGroup.toAddCommGroup
  CommCStarAlgebra.toNonUnitalCommCStarAlgebra
  NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra
  NonUnitalCStarAlgebra.toNormedSpace
  NormedSpace.toModule

/-- Dominio natural aberto da serie bracketada. -/
def bracketHalfPlane : Set ℂ :=
  {s : ℂ | -1 < s.re}

theorem isOpen_bracketHalfPlane : IsOpen bracketHalfPlane := by
  simpa [bracketHalfPlane] using
    (isOpen_lt continuous_const Complex.continuous_re)

/-- A potencia de Dirichlet de uma base real nao nula e inteira em `s`. -/
theorem differentiable_realDirichletPower_in_parameter
    {x : ℝ} (hx : x ≠ 0) :
    Differentiable ℂ (fun s : ℂ ↦ realDirichletPower s x) := by
  have hxComplex : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  letI : NeZero (x : ℂ) := ⟨hxComplex⟩
  simpa [realDirichletPower, Function.comp_def] using
    (differentiable_const_cpow_of_neZero (x : ℂ)).comp differentiable_neg

/-- A potencia de Dirichlet de um inteiro positivo e inteira em `s`. -/
theorem differentiable_dirichletTerm_in_parameter
    {n : ℤ} (hn : 0 < n) :
    Differentiable ℂ (fun s : ℂ ↦ dirichletTerm s n) := by
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hnComplex : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
  letI : NeZero (n : ℂ) := ⟨hnComplex⟩
  simpa [dirichletTerm, Function.comp_def] using
    (differentiable_const_cpow_of_neZero (n : ℂ)).comp differentiable_neg

/-- Cada par bracketado admissivel e inteiro na variavel espectral. -/
theorem differentiable_realCpPairBracket
    {p radius k : ℕ} (hp : Nat.Prime p)
    (hradius : radius ∈ Finset.Icc 1 (halfRange p)) :
    Differentiable ℂ (realCpPairBracket p radius k) := by
  have hradiusUpper : radius ≤ halfRange p :=
    (Finset.mem_Icc.mp hradius).2
  have hleftLower :=
    natCast_add_one_le_alignedCenter_sub_radius (k := k) hp hradiusUpper
  have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hleft :
      0 < (p : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ) :=
    lt_of_lt_of_le hkpos hleftLower
  have hcenter : 0 < (p : ℝ) * ((k + 1 : ℕ) : ℝ) := by
    exact mul_pos (by exact_mod_cast hp.pos) (by positivity)
  have hright :
      0 < (p : ℝ) * ((k + 1 : ℕ) : ℝ) + (radius : ℝ) := by
    exact add_pos_of_pos_of_nonneg hcenter (by positivity)
  have hleftDiff :=
    differentiable_realDirichletPower_in_parameter (ne_of_gt hleft)
  have hcenterDiff :=
    differentiable_realDirichletPower_in_parameter (ne_of_gt hcenter)
  have hrightDiff :=
    differentiable_realDirichletPower_in_parameter (ne_of_gt hright)
  rw [show realCpPairBracket p radius k =
      ((fun s : ℂ ↦ realDirichletPower s
          ((p : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ))) -
        ((fun s : ℂ ↦ realDirichletPower s
            ((p : ℝ) * ((k + 1 : ℕ) : ℝ))) +
          (fun s : ℂ ↦ realDirichletPower s
            ((p : ℝ) * ((k + 1 : ℕ) : ℝ))))) +
        (fun s : ℂ ↦ realDirichletPower s
          ((p : ℝ) * ((k + 1 : ℕ) : ℝ) + (radius : ℝ))) by
    funext s
    simp [realCpPairBracket, two_smul]]
  exact (hleftDiff.sub (hcenterDiff.add hcenterDiff)).add hrightDiff

/-- Cada bloco Cp saturado e uma soma finita de funcoes inteiras. -/
theorem differentiable_realCpSaturatedBracket
    (p k : ℕ) (hp : Nat.Prime p) :
    Differentiable ℂ (realCpSaturatedBracket p k) := by
  classical
  unfold realCpSaturatedBracket
  exact Differentiable.fun_sum fun radius hradius ↦
    differentiable_realCpPairBracket hp hradius

/-- A semente finita da carta e inteira na variavel espectral. -/
theorem differentiable_seedSum_dirichletTerm (p : ℕ) :
    Differentiable ℂ
      (fun s : ℂ ↦ NativeCarryGeometry.Internal.Genuine.Cp.seedSum p (dirichletTerm s)) := by
  classical
  unfold NativeCarryGeometry.Internal.Genuine.Cp.seedSum
  exact Differentiable.fun_sum fun n hn ↦
    differentiable_dirichletTerm_in_parameter (Finset.mem_Icc.mp hn).1

/-- Raio canonico da vizinhanca local em torno de um ponto do semiplano. -/
def bracketNeighborhoodRadius (z : ℂ) : ℝ :=
  (z.re + 1) / 2

/-- Menor expoente real usado no majorante local. -/
def bracketNeighborhoodFloor (z : ℂ) : ℝ :=
  (z.re - 1) / 2

/-- Limite uniforme local para `‖w * (w+1)‖` numa bola de raio `R`. -/
def localQuadraticNormBound (z : ℂ) (R : ℝ) : ℝ :=
  (‖z‖ + R) * (‖z‖ + R + 1)

/-- Constante finita do majorante local, depois de somar os raios da camera. -/
def localCpBracketMajorantConstant (p : ℕ) (z : ℂ) (R : ℝ) : ℝ :=
  ∑ radius ∈ Finset.Icc 1 (halfRange p),
    2 * localQuadraticNormBound z R * (radius : ℝ) ^ 2

theorem localCpBracketMajorantConstant_nonneg
    {p : ℕ} {z : ℂ} {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ localCpBracketMajorantConstant p z R := by
  classical
  unfold localCpBracketMajorantConstant localQuadraticNormBound
  apply Finset.sum_nonneg
  intro radius _hradius
  have hzR : 0 ≤ ‖z‖ + R := add_nonneg (norm_nonneg _) hR
  have hzROne : 0 ≤ ‖z‖ + R + 1 := by linarith
  exact mul_nonneg
    (mul_nonneg (by norm_num) (mul_nonneg hzR hzROne))
    (sq_nonneg (radius : ℝ))

/-- Dentro de uma bola, a norma quadratica em `w` e uniformemente limitada. -/
theorem norm_mul_add_one_le_localQuadraticNormBound
    {z w : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hw : w ∈ Metric.ball z R) :
    ‖w * (w + 1)‖ ≤ localQuadraticNormBound z R := by
  have hdist : ‖w - z‖ < R := by
    simpa [dist_eq_norm] using hw
  have hwNorm : ‖w‖ ≤ ‖z‖ + R := by
    calc
      ‖w‖ = ‖(w - z) + z‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + R := by linarith
  have hwAddOne : ‖w + 1‖ ≤ ‖z‖ + R + 1 := by
    calc
      ‖w + 1‖ ≤ ‖w‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖z‖ + R + 1 := by norm_num; linarith
  rw [norm_mul]
  unfold localQuadraticNormBound
  calc
    ‖w‖ * ‖w + 1‖ ≤ (‖z‖ + R) * ‖w + 1‖ :=
      mul_le_mul_of_nonneg_right hwNorm (norm_nonneg _)
    _ ≤ (‖z‖ + R) * (‖z‖ + R + 1) :=
      mul_le_mul_of_nonneg_left hwAddOne (by positivity)

/-- O fator finito da cota pontual e limitado pela constante local. -/
theorem cpBracketMajorantConstant_le_local
    {p : ℕ} {z w : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hw : w ∈ Metric.ball z R) :
    cpBracketMajorantConstant p w ≤
      localCpBracketMajorantConstant p z R := by
  classical
  unfold cpBracketMajorantConstant localCpBracketMajorantConstant
  apply Finset.sum_le_sum
  intro radius _hradius
  have hquad := norm_mul_add_one_le_localQuadraticNormBound hR hw
  nlinarith [sq_nonneg (radius : ℝ)]

/-- A bola canonica permanece acima do piso real escolhido. -/
theorem bracketNeighborhoodFloor_lt_re
    {z w : ℂ} (hw : w ∈ Metric.ball z (bracketNeighborhoodRadius z)) :
    bracketNeighborhoodFloor z < w.re := by
  have hdist : ‖w - z‖ < bracketNeighborhoodRadius z := by
    simpa [dist_eq_norm] using hw
  have hreNorm : |w.re - z.re| ≤ ‖w - z‖ := by
    simpa using Complex.abs_re_le_norm (w - z)
  have hnegative : -‖w - z‖ ≤ w.re - z.re := by
    calc
      -‖w - z‖ ≤ -|w.re - z.re| := neg_le_neg hreNorm
      _ ≤ w.re - z.re := neg_abs_le _
  have hdist' : ‖w - z‖ < (z.re + 1) / 2 := by
    simpa [bracketNeighborhoodRadius] using hdist
  change (z.re - 1) / 2 < w.re
  linarith [hdist']

theorem neg_one_lt_bracketNeighborhoodFloor
    {z : ℂ} (hz : z ∈ bracketHalfPlane) :
    -1 < bracketNeighborhoodFloor z := by
  change -1 < (z.re - 1) / 2
  change -1 < z.re at hz
  linarith

theorem bracketNeighborhoodRadius_pos
    {z : ℂ} (hz : z ∈ bracketHalfPlane) :
    0 < bracketNeighborhoodRadius z := by
  change 0 < (z.re + 1) / 2
  change -1 < z.re at hz
  linarith

/-- Versao real, independente de um numero complexo, da p-serie deslocada. -/
theorem summable_nat_add_one_rpow_neg_sub_two
    {a : ℝ} (ha : -1 < a) :
    Summable (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) ^ (-a - 2)) := by
  have hbase : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-a - 2)) :=
    Real.summable_nat_rpow.mpr (by linarith [ha])
  have hshift := hbase.comp_injective
    (show Function.Injective (fun n : ℕ ↦ n + 1) by
      intro x y hxy
      exact Nat.add_right_cancel hxy)
  simpa [Function.comp_def] using hshift

/-- A sequencia numerica somavel que domina todos os blocos numa bola. -/
theorem summable_localCpBracketMajorant
    (p : ℕ) {z : ℂ} (hz : z ∈ bracketHalfPlane) :
    Summable (fun k : ℕ ↦
      localCpBracketMajorantConstant p z (bracketNeighborhoodRadius z) *
        ((k + 1 : ℕ) : ℝ) ^ (-bracketNeighborhoodFloor z - 2)) := by
  exact (summable_nat_add_one_rpow_neg_sub_two
    (neg_one_lt_bracketNeighborhoodFloor hz)).mul_left _

/-!
Este e o majorante uniforme local indispensavel. A constante e o expoente
dependem apenas do centro da bola, nunca do ponto `w` nem da profundidade
`k`.
-/
theorem norm_realCpSaturatedBracket_le_local
    (p : ℕ) (hp : Nat.Prime p) {z w : ℂ}
    (hz : z ∈ bracketHalfPlane)
    (hw : w ∈ Metric.ball z (bracketNeighborhoodRadius z)) (k : ℕ) :
    ‖realCpSaturatedBracket p k w‖ ≤
      localCpBracketMajorantConstant p z (bracketNeighborhoodRadius z) *
        ((k + 1 : ℕ) : ℝ) ^ (-bracketNeighborhoodFloor z - 2) := by
  have hfloor := bracketNeighborhoodFloor_lt_re hw
  have hwDomain : -1 < w.re :=
    lt_trans (neg_one_lt_bracketNeighborhoodFloor hz) hfloor
  have hconstant := cpBracketMajorantConstant_le_local (p := p)
    (le_of_lt (bracketNeighborhoodRadius_pos hz)) hw
  have hbase : 1 ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hpower :
      ((k + 1 : ℕ) : ℝ) ^ (-w.re - 2) ≤
        ((k + 1 : ℕ) : ℝ) ^ (-bracketNeighborhoodFloor z - 2) :=
    Real.monotone_rpow_of_base_ge_one hbase (by linarith [hfloor])
  calc
    ‖realCpSaturatedBracket p k w‖ ≤
        cpBracketMajorantConstant p w *
          ((k + 1 : ℕ) : ℝ) ^ (-w.re - 2) :=
      norm_realCpSaturatedBracket_le hp hwDomain
    _ ≤ localCpBracketMajorantConstant p z (bracketNeighborhoodRadius z) *
          ((k + 1 : ℕ) : ℝ) ^ (-bracketNeighborhoodFloor z - 2) := by
      calc
        cpBracketMajorantConstant p w *
            ((k + 1 : ℕ) : ℝ) ^ (-w.re - 2) ≤
            localCpBracketMajorantConstant p z (bracketNeighborhoodRadius z) *
              ((k + 1 : ℕ) : ℝ) ^ (-w.re - 2) :=
          mul_le_mul_of_nonneg_right hconstant
            (Real.rpow_nonneg (by positivity) _)
        _ ≤ localCpBracketMajorantConstant p z (bracketNeighborhoodRadius z) *
              ((k + 1 : ℕ) : ℝ) ^ (-bracketNeighborhoodFloor z - 2) :=
          mul_le_mul_of_nonneg_left hpower
            (localCpBracketMajorantConstant_nonneg
              (le_of_lt (bracketNeighborhoodRadius_pos hz)))

/-- A cauda bracketada e holomorfa em todo o semiplano `re(s)>-1`. -/
theorem differentiableOn_tsum_realCpSaturatedBracket
    (p : ℕ) (hp : Nat.Prime p) :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ ∑' k : ℕ, realCpSaturatedBracket p k s)
      bracketHalfPlane := by
  intro z hz
  let R := bracketNeighborhoodRadius z
  let U : Set ℂ := Metric.ball z R
  let u : ℕ → ℝ := fun k ↦
    localCpBracketMajorantConstant p z R *
      ((k + 1 : ℕ) : ℝ) ^ (-bracketNeighborhoodFloor z - 2)
  have hR : 0 < R := bracketNeighborhoodRadius_pos hz
  have hu : Summable u := by
    simpa [u, R] using summable_localCpBracketMajorant p hz
  have hUOpen : IsOpen U := Metric.isOpen_ball
  have htailOn : DifferentiableOn ℂ
      (fun w : ℂ ↦ ∑' k : ℕ, realCpSaturatedBracket p k w) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm hu
    · intro k
      exact (differentiable_realCpSaturatedBracket p k hp).differentiableOn
    · exact hUOpen
    · intro k w hw
      simpa [u, U, R] using
        norm_realCpSaturatedBracket_le_local p hp hz hw k
  have hzU : z ∈ U := by
    change dist z z < R
    simpa using hR
  exact (htailOn.differentiableAt (hUOpen.mem_nhds hzU)).differentiableWithinAt

/-- A carta bracketada completa e holomorfa em `re(s)>-1`. -/
theorem differentiableOn_bracketedDirichletChart
    (p : ℕ) (hp : Nat.Prime p) :
    DifferentiableOn ℂ (bracketedDirichletChart p) bracketHalfPlane := by
  exact (differentiable_seedSum_dirichletTerm p).differentiableOn.add
    (differentiableOn_tsum_realCpSaturatedBracket p hp)

/-- Forma `AnalyticOnNhd` da continuacao, usada pelo principio da identidade. -/
theorem analyticOnNhd_bracketedDirichletChart
    (p : ℕ) (hp : Nat.Prime p) :
    AnalyticOnNhd ℂ (bracketedDirichletChart p) bracketHalfPlane :=
  (differentiableOn_bracketedDirichletChart p hp).analyticOnNhd
    isOpen_bracketHalfPlane

/-- O semiplano bracketado e convexo e, portanto, preconexo. -/
theorem convex_bracketHalfPlane : Convex ℝ bracketHalfPlane := by
  intro z hz w hw a b ha hb hab
  change -1 < z.re at hz
  change -1 < w.re at hw
  change -1 < (a • z + b • w).re
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  have hwb : 0 ≤ b * (w.re + 1) :=
    mul_nonneg hb (by linarith [hw])
  have hstrict : 0 < a * (z.re + 1) + b * (w.re + 1) := by
    rcases ha.eq_or_lt with rfl | haPos
    · have hbOne : b = 1 := by linarith [hab]
      subst b
      norm_num
      linarith [hw]
    · exact add_pos_of_pos_of_nonneg
        (mul_pos haPos (by linarith [hz])) hwb
  linarith [hab]

theorem isPreconnected_bracketHalfPlane : IsPreconnected bracketHalfPlane :=
  convex_bracketHalfPlane.isPreconnected

/-!
Unicidade da continuacao analitica. Nao pressupomos que a expressao Genuine
totalizada seja holomorfa fora de `re(s)>1`: quantificamos uma candidata `F`
que ja e analitica no dominio maior e usamos apenas sua igualdade com o fator
Genuine no semiplano onde a serie de Dirichlet foi construida.
-/
theorem bracketedDirichletChart_unique_analytic_continuation
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F bracketHalfPlane)
    (hF_genuine : ∀ s : ℂ, 1 < s.re →
      F s = (1 - (p : ℂ) ^ (1 - s)) * genuineDirichlet s) :
    Set.EqOn F (bracketedDirichletChart p) bracketHalfPlane := by
  have hrightOpen : IsOpen {s : ℂ | 1 < s.re} := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hrightMem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    hrightOpen.mem_nhds (by norm_num)
  have heventually : F =ᶠ[𝓝 (2 : ℂ)] bracketedDirichletChart p := by
    filter_upwards [hrightMem] with s hs
    calc
      F s = (1 - (p : ℂ) ^ (1 - s)) * genuineDirichlet s :=
        hF_genuine s hs
      _ = bracketedDirichletChart p s :=
        (bracketedDirichletChart_eq_genuine_factor p hp hpodd hs).symm
  exact hF.eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_bracketedDirichletChart p hp)
    isPreconnected_bracketHalfPlane
    (by norm_num [bracketHalfPlane]) heventually

end

end NativeCarryGeometry.Internal.Analytic.Cp

namespace NativeCarryGeometry.Analytic

noncomputable section

abbrev bracketHalfPlane : Set ℂ :=
  Internal.Analytic.Cp.bracketHalfPlane

/-- NCG-ANL-003: Holomorphy of the Bracket Series. -/
theorem analyticOnNhd_bracketSeries
    (camera : ℕ) (hprime : Nat.Prime camera) :
    AnalyticOnNhd ℂ (bracketSeries camera) bracketHalfPlane :=
  Internal.Analytic.Cp.analyticOnNhd_bracketedDirichletChart
    camera hprime

end
end NativeCarryGeometry.Analytic
