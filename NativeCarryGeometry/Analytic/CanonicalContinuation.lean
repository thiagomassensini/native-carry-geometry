import NativeCarryGeometry.Analytic.BracketHolomorphy
import Mathlib.Analysis.Analytic.Constructions


/-!
# Fator regular da carta Cp e quociente Genuine

Este modulo fecha a consequencia algebrica minima da continuacao bracketada.
Para primo `p`, o modulo de

`p^(1-s)`

e `p^(1-re(s))`. Portanto `1-p^(1-s)` so pode zerar sobre a reta
`re(s)=1`, e em particular nunca zera no interior da faixa critica.

Definimos entao o quociente Cp

`cpGenuineQuotient p s = bracketedDirichletChart p s / cpChartFactor p s`.

Ele e holomorfo no interior da faixa, coincide com a serie Genuine original
em `re(s)>1` e define exatamente o mesmo locus nulo da carta onde o fator nao
zera. O indice `p` permanece explicito: compatibilidade entre quocientes de
cameras primas distintas nao e presumida neste checkpoint.
-/

open scoped Topology

namespace NativeCarryGeometry.Internal.Analytic.Cp

open Set

noncomputable section

attribute [local instance 10000]
  NormedAddCommGroup.toAddCommGroup
  CommCStarAlgebra.toNonUnitalCommCStarAlgebra
  NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra
  NonUnitalCStarAlgebra.toNormedSpace
  NormedSpace.toModule

/-- Fator local que relaciona a carta Cp ao canal Genuine. -/
def cpChartFactor (p : ℕ) (s : ℂ) : ℂ :=
  1 - (p : ℂ) ^ (1 - s)

/-- Interior usual da faixa critica. -/
def genuineCriticalStrip : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < 1}

/-- Norma exata da potencia prima que aparece no fator da carta. -/
theorem norm_prime_cpow_one_sub
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    ‖(p : ℂ) ^ (1 - s)‖ = (p : ℝ) ^ (1 - s.re) := by
  have hpReal : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  simpa using
    (Complex.norm_cpow_eq_rpow_re_of_pos hpReal (1 - s))

/-- Abaixo da reta `re(s)=1`, a potencia prima possui modulo estritamente
maior que um e nao pode ser igual a um. -/
theorem prime_cpow_one_sub_ne_one_of_re_lt_one
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ} (hs : s.re < 1) :
    (p : ℂ) ^ (1 - s) ≠ 1 := by
  intro hpower
  have hnorm := congrArg norm hpower
  rw [norm_prime_cpow_one_sub p hp s, norm_one] at hnorm
  have hpReal : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  have hexponent : 0 < (1 : ℝ) - s.re := by
    linarith
  have hstrict := Real.one_lt_rpow hpReal hexponent
  linarith

/-- Acima da reta `re(s)=1`, a potencia prima possui modulo estritamente
menor que um e tambem nao pode ser igual a um. -/
theorem prime_cpow_one_sub_ne_one_of_one_lt_re
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ} (hs : 1 < s.re) :
    (p : ℂ) ^ (1 - s) ≠ 1 := by
  intro hpower
  have hnorm := congrArg norm hpower
  rw [norm_prime_cpow_one_sub p hp s, norm_one] at hnorm
  have hpReal : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp.one_lt
  have hexponent : (1 : ℝ) - s.re < 0 := by
    linarith
  have hstrict := Real.rpow_lt_one_of_one_lt_of_neg hpReal hexponent
  linarith

theorem cpChartFactor_ne_zero_of_re_lt_one
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ} (hs : s.re < 1) :
    cpChartFactor p s ≠ 0 := by
  intro hzero
  apply prime_cpow_one_sub_ne_one_of_re_lt_one p hp hs
  exact (sub_eq_zero.mp hzero).symm

theorem cpChartFactor_ne_zero_of_one_lt_re
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ} (hs : 1 < s.re) :
    cpChartFactor p s ≠ 0 := by
  intro hzero
  apply prime_cpow_one_sub_ne_one_of_one_lt_re p hp hs
  exact (sub_eq_zero.mp hzero).symm

/-- Forma forte: fora da reta `re(s)=1`, o fator Cp nao zera. -/
theorem cpChartFactor_ne_zero_of_re_ne_one
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ} (hs : s.re ≠ 1) :
    cpChartFactor p s ≠ 0 := by
  rcases lt_or_gt_of_ne hs with hleft | hright
  · exact cpChartFactor_ne_zero_of_re_lt_one p hp hleft
  · exact cpChartFactor_ne_zero_of_one_lt_re p hp hright

/-- Consequentemente, todo zero do fator esta confinado a `re(s)=1`. -/
theorem cpChartFactor_zero_implies_re_eq_one
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ}
    (hzero : cpChartFactor p s = 0) :
    s.re = 1 := by
  by_contra hne
  exact cpChartFactor_ne_zero_of_re_ne_one p hp hne hzero

/-- Corolario diretamente usado na faixa critica. -/
theorem cpChartFactor_ne_zero_on_genuineCriticalStrip
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) :
    cpChartFactor p s ≠ 0 :=
  cpChartFactor_ne_zero_of_re_lt_one p hp hs.2

/-- O fator Cp e inteiro na variavel espectral. -/
theorem differentiable_cpChartFactor
    (p : ℕ) (hp : Nat.Prime p) :
    Differentiable ℂ (cpChartFactor p) := by
  have hpComplex : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  letI : NeZero (p : ℂ) := ⟨hpComplex⟩
  change Differentiable ℂ (fun s : ℂ ↦ 1 - (p : ℂ) ^ (1 - s))
  exact (differentiable_const (c := (1 : ℂ))).sub
    ((differentiable_const_cpow_of_neZero (p : ℂ)).comp
      ((differentiable_const (c := (1 : ℂ))).sub differentiable_id))

/-- Quociente Cp que recupera o canal Genuine onde o fator e regular. -/
def cpGenuineQuotient (p : ℕ) (s : ℂ) : ℂ :=
  bracketedDirichletChart p s / cpChartFactor p s

/-- No semiplano original de convergencia absoluta, o quociente recupera
literalmente a serie Genuine usada na construcao. -/
theorem cpGenuineQuotient_eq_genuineDirichlet
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : 1 < s.re) :
    cpGenuineQuotient p s = genuineDirichlet s := by
  have hfactor := cpChartFactor_ne_zero_of_one_lt_re p hp hs
  rw [cpGenuineQuotient,
    bracketedDirichletChart_eq_genuine_factor p hp hpodd hs]
  change (cpChartFactor p s * genuineDirichlet s) /
      cpChartFactor p s = genuineDirichlet s
  field_simp

/-- No interior da faixa, a carta volta a ser fator vezes quociente. -/
theorem bracketedDirichletChart_eq_factor_mul_cpGenuineQuotient
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) :
    bracketedDirichletChart p s =
      cpChartFactor p s * cpGenuineQuotient p s := by
  have hfactor := cpChartFactor_ne_zero_on_genuineCriticalStrip p hp hs
  unfold cpGenuineQuotient
  field_simp

/-- O quociente Cp e holomorfo no interior da faixa critica. -/
theorem analyticOnNhd_cpGenuineQuotient_genuineCriticalStrip
    (p : ℕ) (hp : Nat.Prime p) :
    AnalyticOnNhd ℂ (cpGenuineQuotient p) genuineCriticalStrip := by
  have hchart : AnalyticOnNhd ℂ
      (bracketedDirichletChart p) genuineCriticalStrip :=
    (analyticOnNhd_bracketedDirichletChart p hp).mono (by
      intro s hs
      change -1 < s.re
      linarith [hs.1])
  have hfactorAll : AnalyticOnNhd ℂ (cpChartFactor p) Set.univ :=
    (differentiable_cpChartFactor p hp).differentiableOn.analyticOnNhd
      isOpen_univ
  have hfactor : AnalyticOnNhd ℂ
      (cpChartFactor p) genuineCriticalStrip :=
    hfactorAll.mono (subset_univ _)
  exact hchart.div hfactor fun s hs ↦
    cpChartFactor_ne_zero_on_genuineCriticalStrip p hp hs

/-- Cancelamento da carta e cancelamento do quociente analítico legado são equivalentes no
interior da faixa critica. -/
theorem bracketedDirichletChart_zero_iff_cpGenuineQuotient_zero
    (p : ℕ) (hp : Nat.Prime p) {s : ℂ}
    (hs : s ∈ genuineCriticalStrip) :
    bracketedDirichletChart p s = 0 ↔ cpGenuineQuotient p s = 0 := by
  constructor
  · intro hchart
    simp [cpGenuineQuotient, hchart]
  · intro hquotient
    rw [bracketedDirichletChart_eq_factor_mul_cpGenuineQuotient p hp hs,
      hquotient, mul_zero]

end

end NativeCarryGeometry.Internal.Analytic.Cp

/-!
# Compatibilidade Genuine entre cameras Cp

Este modulo fecha a independencia prima minima sem importar uma funcao externa.
Para duas cameras primas impares `p` e `q`, consideramos os produtos cruzados

`F_q * B_p` e `F_p * B_q`,

onde `F_p = 1-p^(1-s)` e `B_p` e a carta bracketada. Em `re(s)>1`, as duas
cartas ja foram obtidas como `F_p * genuineDirichlet`; portanto os produtos
cruzados coincidem literalmente. Como ambos sao holomorfos em `re(s)>-1`, o
principio da identidade prolonga essa igualdade sem dividir por nenhum fator.

Somente depois restringimos ao interior da faixa critica, onde os fatores ja
foram provados nao nulos. O cancelamento fornece a igualdade dos quocientes
de todas as cameras primas impares. Assim podemos escolher a camera `p=3`
apenas como representante canonico de um unico objeto Genuine na faixa.
-/

open scoped Topology

namespace NativeCarryGeometry.Internal.Analytic.Cp

open Filter Set

noncomputable section

attribute [local instance 10000]
  NormedAddCommGroup.toAddCommGroup
  CommCStarAlgebra.toNonUnitalCommCStarAlgebra
  NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra
  NonUnitalCStarAlgebra.toNormedSpace
  NormedSpace.toModule

/-- Produto cruzado: o fator da camera `q` aplicado a carta da camera `p`. -/
def crossNormalizedChart (p q : ℕ) (s : ℂ) : ℂ :=
  cpChartFactor q s * bracketedDirichletChart p s

/-- Forma nomeada da identidade ja obtida no semiplano de convergencia. -/
theorem bracketedDirichletChart_eq_cpChartFactor_mul_genuineDirichlet
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : 1 < s.re) :
    bracketedDirichletChart p s =
      cpChartFactor p s * genuineDirichlet s := by
  simpa [cpChartFactor] using
    (bracketedDirichletChart_eq_genuine_factor p hp hpodd hs)

/-- Cada produto cruzado e holomorfo no semiplano bracketado inteiro. -/
theorem analyticOnNhd_crossNormalizedChart
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    AnalyticOnNhd ℂ (crossNormalizedChart p q) bracketHalfPlane := by
  have hfactorAll : AnalyticOnNhd ℂ (cpChartFactor q) Set.univ :=
    (differentiable_cpChartFactor q hq).differentiableOn.analyticOnNhd
      isOpen_univ
  have hfactor : AnalyticOnNhd ℂ (cpChartFactor q) bracketHalfPlane :=
    hfactorAll.mono (subset_univ _)
  exact hfactor.mul (analyticOnNhd_bracketedDirichletChart p hp)

/-- No dominio inicial, os produtos cruzados sao o mesmo produto
`F_p * F_q * genuineDirichlet`. -/
theorem crossNormalizedChart_eq_swap_of_one_lt_re
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : 1 < s.re) :
    crossNormalizedChart p q s = crossNormalizedChart q p s := by
  unfold crossNormalizedChart
  rw [bracketedDirichletChart_eq_cpChartFactor_mul_genuineDirichlet
      p hp hpodd hs,
    bracketedDirichletChart_eq_cpChartFactor_mul_genuineDirichlet
      q hq hqodd hs]
  ring

/-!
Coracao do checkpoint: a identidade cruzada e prolongada antes de qualquer
divisao. Portanto nenhum zero de fator cria um buraco no argumento de
continuacao.
-/
theorem crossNormalizedChart_eq_swap
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q) :
    Set.EqOn (crossNormalizedChart p q)
      (crossNormalizedChart q p) bracketHalfPlane := by
  have hrightOpen : IsOpen {s : ℂ | 1 < s.re} := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hrightMem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    hrightOpen.mem_nhds (by norm_num)
  have heventually :
      crossNormalizedChart p q =ᶠ[𝓝 (2 : ℂ)]
        crossNormalizedChart q p := by
    filter_upwards [hrightMem] with s hs
    exact crossNormalizedChart_eq_swap_of_one_lt_re
      p q hp hpodd hq hqodd hs
  have hleft := analyticOnNhd_crossNormalizedChart p q hp hq
  exact hleft.eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_crossNormalizedChart q p hq hp)
      isPreconnected_bracketHalfPlane
      (by norm_num [bracketHalfPlane]) heventually

/-- Forma pontual da identidade cruzada no semiplano maior. -/
theorem crossNormalizedChart_eq_swap_at
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : -1 < s.re) :
    crossNormalizedChart p q s = crossNormalizedChart q p s :=
  crossNormalizedChart_eq_swap p q hp hpodd hq hqodd hs

/-- Cancelando os fatores regulares, quaisquer duas cameras primas impares
produzem o mesmo quociente Genuine no interior da faixa critica. -/
theorem cpGenuineQuotient_eq_cpGenuineQuotient
    (p q : ℕ)
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : Nat.Prime q) (hqodd : Odd q)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    cpGenuineQuotient p s = cpGenuineQuotient q s := by
  have hfactorP := cpChartFactor_ne_zero_on_genuineCriticalStrip p hp hs
  have hfactorQ := cpChartFactor_ne_zero_on_genuineCriticalStrip q hq hs
  have hcross := crossNormalizedChart_eq_swap_at
    p q hp hpodd hq hqodd (s := s) (by linarith [hs.1])
  unfold cpGenuineQuotient
  field_simp [hfactorP, hfactorQ]
  simpa [crossNormalizedChart, mul_comm] using hcross

/-- Representante canonico do Genuine continuado, escolhido pela menor
camera prima impar. A independencia da camera e provada abaixo. -/
def genuineContinuation (s : ℂ) : ℂ :=
  cpGenuineQuotient 3 s

/-- O representante canonico recupera a serie Genuine original em
`re(s)>1`. -/
theorem genuineContinuation_eq_genuineDirichlet
    {s : ℂ} (hs : 1 < s.re) :
    genuineContinuation s = genuineDirichlet s := by
  simpa [genuineContinuation] using
    (cpGenuineQuotient_eq_genuineDirichlet 3 (by norm_num) (by norm_num) hs)

/-- O Genuine canonico e holomorfo no interior da faixa critica. -/
theorem analyticOnNhd_genuineContinuation_genuineCriticalStrip :
    AnalyticOnNhd ℂ genuineContinuation genuineCriticalStrip := by
  change AnalyticOnNhd ℂ (cpGenuineQuotient 3) genuineCriticalStrip
  exact analyticOnNhd_cpGenuineQuotient_genuineCriticalStrip 3 (by norm_num)

/-- Toda camera prima impar produz o representante canonico na faixa. -/
theorem cpGenuineQuotient_eq_genuineContinuation
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    cpGenuineQuotient p s = genuineContinuation s := by
  change cpGenuineQuotient p s = cpGenuineQuotient 3 s
  exact cpGenuineQuotient_eq_cpGenuineQuotient
    p 3 hp hpodd (by norm_num) (by norm_num) hs

/-- Fatoracao Genuine independente da camera no interior da faixa. -/
theorem bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    bracketedDirichletChart p s =
      cpChartFactor p s * genuineContinuation s := by
  rw [bracketedDirichletChart_eq_factor_mul_cpGenuineQuotient p hp hs,
    cpGenuineQuotient_eq_genuineContinuation p hp hpodd hs]

/-- O locus nulo de qualquer carta prima ímpar é exatamente o locus nulo do mesmo
Genuine canonico dentro da faixa critica. -/
theorem bracketedDirichletChart_zero_iff_genuineContinuation_zero
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    bracketedDirichletChart p s = 0 ↔ genuineContinuation s = 0 := by
  rw [bracketedDirichletChart_zero_iff_cpGenuineQuotient_zero p hp hs,
    cpGenuineQuotient_eq_genuineContinuation p hp hpodd hs]

end

end NativeCarryGeometry.Internal.Analytic.Cp

namespace NativeCarryGeometry.Analytic

noncomputable section

abbrev cameraNormalizationFactor (camera : ℕ) (s : ℂ) : ℂ :=
  Internal.Analytic.Cp.cpChartFactor camera s

abbrev canonicalStrip : Set ℂ :=
  Internal.Analytic.Cp.genuineCriticalStrip

abbrev normalizedBracketChart (camera : ℕ) (s : ℂ) : ℂ :=
  Internal.Analytic.Cp.cpGenuineQuotient camera s

abbrev canonicalCarryContinuation (s : ℂ) : ℂ :=
  Internal.Analytic.Cp.genuineContinuation s

/-- NCG-ANL-004: Camera-Factor Nonvanishing. -/
theorem cameraNormalizationFactor_ne_zero
    (camera : ℕ) (hprime : Nat.Prime camera)
    {s : ℂ} (hs : s ∈ canonicalStrip) :
    cameraNormalizationFactor camera s ≠ 0 :=
  Internal.Analytic.Cp.cpChartFactor_ne_zero_on_genuineCriticalStrip
    camera hprime hs

/-- NCG-ANL-005: Camera Compatibility. -/
theorem normalizedBracketChart_camera_independent
    (camera₁ camera₂ : ℕ)
    (hprime₁ : Nat.Prime camera₁) (hodd₁ : Odd camera₁)
    (hprime₂ : Nat.Prime camera₂) (hodd₂ : Odd camera₂)
    {s : ℂ} (hs : s ∈ canonicalStrip) :
    normalizedBracketChart camera₁ s =
      normalizedBracketChart camera₂ s :=
  Internal.Analytic.Cp.cpGenuineQuotient_eq_cpGenuineQuotient
    camera₁ camera₂ hprime₁ hodd₁ hprime₂ hodd₂ hs

/-- NCG-ANL-006: Canonical Bracket Factorization. -/
theorem bracketSeries_eq_factor_mul_canonicalCarryContinuation
    (camera : ℕ) (hprime : Nat.Prime camera) (hodd : Odd camera)
    {s : ℂ} (hs : s ∈ canonicalStrip) :
    bracketSeries camera s =
      cameraNormalizationFactor camera s *
        canonicalCarryContinuation s :=
  Internal.Analytic.Cp.bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation
    camera hprime hodd hs

/-- NCG-ANL-007: Holomorphy of the Canonical Continuation. -/
theorem analyticOnNhd_canonicalCarryContinuation :
    AnalyticOnNhd ℂ canonicalCarryContinuation canonicalStrip :=
  Internal.Analytic.Cp.analyticOnNhd_genuineContinuation_genuineCriticalStrip

/-- NCG-ANL-008: Odd-Prime Camera Ambient Chart-Cancellation Locus Identity. -/
theorem bracketSeries_zero_iff_canonicalCarryContinuation_zero
    (camera : ℕ) (hprime : Nat.Prime camera) (hodd : Odd camera)
    {s : ℂ} (hs : s ∈ canonicalStrip) :
    bracketSeries camera s = 0 ↔
      canonicalCarryContinuation s = 0 :=
  Internal.Analytic.Cp.bracketedDirichletChart_zero_iff_genuineContinuation_zero
    camera hprime hodd hs

end
end NativeCarryGeometry.Analytic
