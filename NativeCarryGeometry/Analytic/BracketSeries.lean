import NativeCarryGeometry.Analytic.FiniteBracketChart
import NativeCarryGeometry.Bracket.CenteredDifference
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic


/-!
# Ganho quadratico da segunda diferenca central

Este arquivo isola o mecanismo analitico minimo usado pelas cartas
bracketadas. Se a segunda derivada de `f : R -> C` tem norma limitada por
`C` a direita de `lower`, entao o bracket de raio nao negativo `radius`
satisfaz

`||f (center-radius) - 2 f center + f (center+radius)||
    <= 2 C radius^2`.

A prova usa duas vezes a desigualdade do valor medio para funcoes com valores
em um espaco normado. O fator `radius^2` e o ganho que, para `f(x)=x^(-s)`,
desloca a barreira de convergencia de `re(s)>1` para `re(s)>-1`.
-/

namespace NativeCarryGeometry.Internal.Analytic

noncomputable section

attribute [local instance 10000] NormedSpace.complexToReal

/--
Uma cota uniforme para a segunda derivada produz o ganho quadratico de uma
segunda diferenca central. A formulacao usa derivadas ordinarias nos pontos
de `Set.Ici lower`; nas duas aplicacoes do valor medio elas sao restringidas
automaticamente ao conjunto convexo relevante.
-/
theorem norm_centeredSecondDifference_le
    {f f' f'' : ℝ → ℂ} {lower center radius C : ℝ}
    (hradius : 0 ≤ radius)
    (hleft : lower ≤ center - radius)
    (hf : ∀ x, lower ≤ x → HasDerivAt f (f' x) x)
    (hf' : ∀ x, lower ≤ x → HasDerivAt f' (f'' x) x)
    (hbound : ∀ x, lower ≤ x → ‖f'' x‖ ≤ C) :
    ‖f (center - radius) - (2 • f center) + f (center + radius)‖ ≤
      2 * C * radius ^ 2 := by
  have hC : 0 ≤ C :=
    le_trans (norm_nonneg (f'' (center - radius)))
      (hbound (center - radius) hleft)

  let g : ℝ → ℂ := fun t ↦
    f (center - t) + f (center + t) - (2 • f center)

  have hfirstDifference :
      ∀ t ∈ Set.Icc (0 : ℝ) radius,
        ‖f' (center + t) - f' (center - t)‖ ≤ 2 * C * radius := by
    intro t ht
    have hminus : lower ≤ center - t := by linarith [ht.2]
    have hplus : lower ≤ center + t := by linarith [ht.1]
    have hlip :=
      (convex_Ici lower).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun x hx ↦ (hf' x hx).hasDerivWithinAt)
        hbound hminus hplus
    calc
      ‖f' (center + t) - f' (center - t)‖ ≤
          C * ‖(center + t) - (center - t)‖ := hlip
      _ = C * (2 * t) := by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · ring
        · linarith [ht.1]
      _ ≤ 2 * C * radius := by nlinarith [ht.2]

  have hg :
      ∀ t ∈ Set.Icc (0 : ℝ) radius,
        HasDerivWithinAt g
          (f' (center + t) - f' (center - t))
          (Set.Icc (0 : ℝ) radius) t := by
    intro t ht
    have hminusPoint : lower ≤ center - t := by linarith [ht.2]
    have hplusPoint : lower ≤ center + t := by linarith [ht.1]
    have hinnerMinus :
        HasDerivAt (fun u : ℝ ↦ center - u) (-1 : ℝ) t := by
      exact (hasDerivAt_id' t).const_sub center
    have hinnerPlus :
        HasDerivAt (fun u : ℝ ↦ center + u) (1 : ℝ) t := by
      exact (hasDerivAt_id' t).const_add center
    have hminus :
        HasDerivAt (fun u : ℝ ↦ f (center - u))
          (-f' (center - t)) t := by
      simpa [Function.comp_def] using
        (hf (center - t) hminusPoint).scomp t hinnerMinus
    have hplus :
        HasDerivAt (fun u : ℝ ↦ f (center + u))
          (f' (center + t)) t := by
      simpa [Function.comp_def] using
        (hf (center + t) hplusPoint).scomp t hinnerPlus
    have hsum :
        HasDerivAt
          (fun u : ℝ ↦ f (center - u) + f (center + u))
          (-f' (center - t) + f' (center + t)) t :=
      hminus.fun_add hplus
    have hsumConst := hsum.sub_const (2 • f center)
    simpa only [g, sub_eq_add_neg, neg_add_rev, add_comm] using
      hsumConst.hasDerivWithinAt

  have houter :=
    (convex_Icc (0 : ℝ) radius).norm_image_sub_le_of_norm_hasDerivWithin_le
      hg hfirstDifference
      (show (0 : ℝ) ∈ Set.Icc 0 radius by exact ⟨le_rfl, hradius⟩)
      (show radius ∈ Set.Icc (0 : ℝ) radius by exact ⟨hradius, le_rfl⟩)

  have hleftNorm :
      ‖g radius - g 0‖ =
        ‖f (center - radius) - (2 • f center) +
          f (center + radius)‖ := by
    simp only [g]
    congr 1
    simp only [sub_zero, two_smul]
    abel_nf

  rw [hleftNorm] at houter
  calc
    ‖f (center - radius) - (2 • f center) +
        f (center + radius)‖ ≤
        (2 * C * radius) * ‖radius - 0‖ := houter
    _ = 2 * C * radius ^ 2 := by
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hradius]
      ring

end

end NativeCarryGeometry.Internal.Analytic

/-!
# Segunda diferenca do monomio de Dirichlet

Este arquivo especializa o ganho abstrato da segunda diferenca a

`f_s(x) = x^(-s)`, para `x > 0`.

A segunda derivada e

`s * (s + 1) * x^(-s-2)`.

Consequentemente, quando `re(s) > -1`, cada bracket centrado satisfaz uma
cota por uma constante vezes `x^(-re(s)-2)`. Esta e a estimativa analitica
que alimenta a comparacao posterior com uma p-serie.
-/

namespace NativeCarryGeometry.Internal.Analytic.Cp

noncomputable section

attribute [local instance 10000] NormedSpace.complexToReal

/-- O monomio de Dirichlet visto como funcao de uma variavel real positiva. -/
def realDirichletPower (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-s)

/-- Primeira derivada formal de `realDirichletPower`. -/
def realDirichletPowerDeriv (s : ℂ) (x : ℝ) : ℂ :=
  (-s) * (x : ℂ) ^ (-s - 1)

/-- Segunda derivada formal de `realDirichletPower`. -/
def realDirichletPowerDeriv2 (s : ℂ) (x : ℝ) : ℂ :=
  s * (s + 1) * (x : ℂ) ^ (-s - 2)

/-- Derivada de `x^(-s)` no eixo real positivo, no caso nao constante. -/
theorem hasDerivAt_realDirichletPower
    {s : ℂ} (hs : s ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (realDirichletPower s)
      (realDirichletPowerDeriv s x) x := by
  change HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ (-s))
    ((-s) * (x : ℂ) ^ (-s - 1)) x
  simpa only [neg_mul] using
    (hasDerivAt_ofReal_cpow_const (ne_of_gt hx) (neg_ne_zero.mpr hs))

/-- A segunda derivada existe em todo ponto positivo quando `re(s)>-1`. -/
theorem hasDerivAt_realDirichletPowerDeriv
    {s : ℂ} (hs : -1 < s.re) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (realDirichletPowerDeriv s)
      (realDirichletPowerDeriv2 s x) x := by
  have hexponent : -s - 1 ≠ 0 := by
    intro h
    have hre : -s.re - 1 = 0 := by
      simpa using congrArg Complex.re h
    linarith
  have hpow :=
    hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hexponent
  have hscaled :
      HasDerivAt
        (fun y : ℝ ↦ (-s) • (y : ℂ) ^ (-s - 1))
        ((-s) • ((-s - 1) * (x : ℂ) ^ ((-s - 1) - 1))) x := by
    apply HasDerivAt.fun_const_smul
    exact hpow
  have hexponentSub : (-s - 1) - 1 = -s - 2 := by ring
  have hcoefficient : (-s) * (-s - 1) = s * (s + 1) := by ring
  change HasDerivAt
    (fun y : ℝ ↦ (-s) * (y : ℂ) ^ (-s - 1))
    (s * (s + 1) * (x : ℂ) ^ (-s - 2)) x
  simpa only [realDirichletPowerDeriv, realDirichletPowerDeriv2,
    smul_eq_mul, hexponentSub, ← mul_assoc, hcoefficient] using
      hscaled

/-- Norma exata da segunda derivada sobre o eixo real positivo. -/
theorem norm_realDirichletPowerDeriv2
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖realDirichletPowerDeriv2 s x‖ =
      ‖s * (s + 1)‖ * x ^ (-s.re - 2) := by
  rw [realDirichletPowerDeriv2, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1

/-!
O ganho concreto: a braquetada compra duas potencias. A base da cota e o
menor ponto do segmento, `center-radius`, pois o expoente real
`-re(s)-2` e negativo em todo o dominio `re(s)>-1`.
-/
theorem norm_realDirichletPower_centeredSecondDifference_le
    {s : ℂ} (hs : -1 < s.re)
    {center radius : ℝ}
    (hradius : 0 ≤ radius)
    (hleft : 0 < center - radius) :
    ‖realDirichletPower s (center - radius) -
        (2 • realDirichletPower s center) +
          realDirichletPower s (center + radius)‖ ≤
      2 *
        (‖s * (s + 1)‖ *
          (center - radius) ^ (-s.re - 2)) *
        radius ^ 2 := by
  by_cases hs0 : s = 0
  · subst s
    norm_num [realDirichletPower, two_smul]
  · refine norm_centeredSecondDifference_le
      (f := realDirichletPower s)
      (f' := realDirichletPowerDeriv s)
      (f'' := realDirichletPowerDeriv2 s)
      (lower := center - radius)
      (C := ‖s * (s + 1)‖ *
        (center - radius) ^ (-s.re - 2))
      hradius le_rfl ?_ ?_ ?_
    · intro x hx
      exact hasDerivAt_realDirichletPower hs0 (lt_of_lt_of_le hleft hx)
    · intro x hx
      exact hasDerivAt_realDirichletPowerDeriv hs
        (lt_of_lt_of_le hleft hx)
    · intro x hx
      rw [norm_realDirichletPowerDeriv2 s (lt_of_lt_of_le hleft hx)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hleft hx (by linarith [hs]))
        (norm_nonneg _)

end

end NativeCarryGeometry.Internal.Analytic.Cp

/-!
# Convergencia da carta Cp bracketada em `re(s)>-1`

Aqui a estimativa de segunda diferenca e somada sobre os raios finitos da
camera e comparada com a p-serie

`(k+1)^(-re(s)-2)`.

O modulo prova a somabilidade absoluta dos blocos bracketados, identifica
cada prefixo com `Genuine.Cp.finiteChart` e usa a unicidade do limite para
recuperar o fator Genuine no semiplano comum `re(s)>1`. Holomorfia e
continuacao analitica sao tratadas no modulo seguinte,
`CpBracketHolomorphic`.
-/

open scoped BigOperators

namespace NativeCarryGeometry.Internal.Analytic.Cp

open NativeCarryGeometry.Internal.Genuine.Cp

noncomputable section

/-- Segunda diferenca de raio natural na camera real centrada em `p(k+1)`. -/
def realCpPairBracket (p radius k : ℕ) (s : ℂ) : ℂ :=
  let center : ℝ := (p : ℝ) * ((k + 1 : ℕ) : ℝ)
  let r : ℝ := radius
  realDirichletPower s (center - r) -
    (2 • realDirichletPower s center) +
      realDirichletPower s (center + r)

/-- Soma dos pares de raios `1,...,halfRange(p)` no `k`-esimo centro. -/
def realCpSaturatedBracket (p k : ℕ) (s : ℂ) : ℂ :=
  ∑ radius ∈ Finset.Icc 1 (halfRange p),
    realCpPairBracket p radius k s

/-- A versao real da braquetada coincide com a segunda diferenca inteira. -/
theorem realCpPairBracket_eq_centeredSecondDifference
    (p radius k : ℕ) (s : ℂ) :
    realCpPairBracket p radius k s =
      NativeCarryGeometry.Internal.centeredSecondDifference (dirichletTerm s)
        (alignedCenter p k) (radius : ℤ) := by
  simp [realCpPairBracket, realDirichletPower,
    NativeCarryGeometry.Internal.centeredSecondDifference, dirichletTerm, alignedCenter]

/-- O bloco analitico e literalmente o `saturatedBracket` finito ja auditado. -/
theorem realCpSaturatedBracket_eq_saturatedBracket
    (p k : ℕ) (s : ℂ) :
    realCpSaturatedBracket p k s =
      NativeCarryGeometry.Internal.saturatedBracket (halfRange p) (dirichletTerm s)
        (alignedCenter p k) := by
  classical
  unfold realCpSaturatedBracket NativeCarryGeometry.Internal.saturatedBracket
  apply Finset.sum_congr rfl
  intro radius hradius
  exact realCpPairBracket_eq_centeredSecondDifference p radius k s

/-!
Ponte finita entre as duas linguagens: o bloco analitico por segundas
diferencas e exatamente o `Genuine.Cp.bracket` no mesmo centro.
-/
theorem realCpSaturatedBracket_eq_genuineBracket
    (p k : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (s : ℂ) :
    realCpSaturatedBracket p k s =
      NativeCarryGeometry.Internal.Genuine.Cp.bracket p (dirichletTerm s)
        (alignedCenter p k) := by
  rw [realCpSaturatedBracket_eq_saturatedBracket]
  exact (NativeCarryGeometry.Internal.Genuine.Cp.bracket_eq_saturatedBracket
    p hp hpodd (dirichletTerm s) (alignedCenter p k)).symm

/-- Constante finita produzida pelas pernas de uma camera Cp. -/
def cpBracketMajorantConstant (p : ℕ) (s : ℂ) : ℝ :=
  ∑ radius ∈ Finset.Icc 1 (halfRange p),
    2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2

/-- Um raio admissivel deixa o bordo esquerdo alem de `k+1`. -/
theorem natCast_add_one_le_alignedCenter_sub_radius
    {p radius k : ℕ} (hp : Nat.Prime p)
    (hradius : radius ≤ halfRange p) :
    ((k + 1 : ℕ) : ℝ) ≤
      (p : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ) := by
  have hhalf : halfRange p ≤ p - 1 := by
    unfold halfRange
    exact Nat.div_le_self (p - 1) 2
  have hradius' : radius ≤ p - 1 := le_trans hradius hhalf
  have hpone : 1 ≤ p := hp.one_le
  have hponeReal : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpone
  have hpnonneg : 0 ≤ (p : ℝ) - 1 := sub_nonneg.mpr hponeReal
  have hkNat : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  have hk : 1 ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hkNat
  have hradiusRealNat : (radius : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast hradius'
  have hpCast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hpone]
    norm_num
  have hradiusReal : (radius : ℝ) ≤ (p : ℝ) - 1 := by
    simpa [hpCast] using hradiusRealNat
  nlinarith [mul_nonneg hpnonneg (sub_nonneg.mpr hk)]

/--
Cota de uma unica braquetada: o centro `p(k+1)` pode ser substituido pelo
majorante mais simples `k+1`, uniformemente em `k`.
-/
theorem norm_realCpPairBracket_le
    {p radius k : ℕ} (hp : Nat.Prime p)
    {s : ℂ} (hs : -1 < s.re)
    (hradius : radius ∈ Finset.Icc 1 (halfRange p)) :
    ‖realCpPairBracket p radius k s‖ ≤
      (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
  have hradiusUpper : radius ≤ halfRange p :=
    (Finset.mem_Icc.mp hradius).2
  have hleftLower :=
    natCast_add_one_le_alignedCenter_sub_radius (k := k) hp hradiusUpper
  have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hleft :
      0 < (p : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ) :=
    lt_of_lt_of_le hkpos hleftLower
  have hraw := norm_realDirichletPower_centeredSecondDifference_le
    hs (show 0 ≤ (radius : ℝ) by positivity) hleft
  have hpower :
      ((p : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
          (-s.re - 2) ≤
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) :=
    Real.rpow_le_rpow_of_nonpos hkpos hleftLower (by linarith [hs])
  calc
    ‖realCpPairBracket p radius k s‖ ≤
        2 *
          (‖s * (s + 1)‖ *
            ((p : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
              (-s.re - 2)) *
          (radius : ℝ) ^ 2 := by
      simpa [realCpPairBracket] using hraw
    _ = (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
          (((p : ℝ) * ((k + 1 : ℕ) : ℝ) - (radius : ℝ)) ^
            (-s.re - 2)) := by ring
    _ ≤ (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
          ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) :=
      mul_le_mul_of_nonneg_left hpower (by positivity)

/-- Cota de um bloco inteiro por uma unica p-serie. -/
theorem norm_realCpSaturatedBracket_le
    {p k : ℕ} (hp : Nat.Prime p)
    {s : ℂ} (hs : -1 < s.re) :
    ‖realCpSaturatedBracket p k s‖ ≤
      cpBracketMajorantConstant p s *
        ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
  classical
  unfold realCpSaturatedBracket cpBracketMajorantConstant
  calc
    ‖∑ radius ∈ Finset.Icc 1 (halfRange p),
        realCpPairBracket p radius k s‖ ≤
        ∑ radius ∈ Finset.Icc 1 (halfRange p),
          ‖realCpPairBracket p radius k s‖ := norm_sum_le _ _
    _ ≤ ∑ radius ∈ Finset.Icc 1 (halfRange p),
          (2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
            ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
      exact Finset.sum_le_sum fun radius hradius ↦
        norm_realCpPairBracket_le hp hs hradius
    _ = (∑ radius ∈ Finset.Icc 1 (halfRange p),
          2 * ‖s * (s + 1)‖ * (radius : ℝ) ^ 2) *
            ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2) := by
      rw [Finset.sum_mul]

/-- A p-serie deslocada que domina a carta e somavel para `re(s)>-1`. -/
theorem summable_nat_add_one_rpow_neg_re_sub_two
    {s : ℂ} (hs : -1 < s.re) :
    Summable (fun k : ℕ ↦
      ((k + 1 : ℕ) : ℝ) ^ (-s.re - 2)) := by
  have hbase : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-s.re - 2)) :=
    Real.summable_nat_rpow.mpr (by linarith [hs])
  have hshift := hbase.comp_injective
    (show Function.Injective (fun n : ℕ ↦ n + 1) by
      intro a b hab
      exact Nat.add_right_cancel hab)
  simpa [Function.comp_def] using hshift

/-!
Teorema central deste checkpoint: as normas dos blocos bracketados formam
uma serie somavel em todo o semiplano aberto `re(s)>-1`.
-/
theorem summable_norm_realCpSaturatedBracket
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : -1 < s.re) :
    Summable (fun k : ℕ ↦ ‖realCpSaturatedBracket p k s‖) := by
  have hpower := summable_nat_add_one_rpow_neg_re_sub_two hs
  have hmajorant := hpower.mul_left (cpBracketMajorantConstant p s)
  exact hmajorant.of_norm_bounded
    (fun k ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact norm_realCpSaturatedBracket_le hp hs)

/-- A serie complexa converge como consequencia de sua somabilidade absoluta. -/
theorem summable_realCpSaturatedBracket
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : -1 < s.re) :
    Summable (fun k : ℕ ↦ realCpSaturatedBracket p k s) :=
  (summable_norm_realCpSaturatedBracket p hp hs).of_norm

/-- A carta bracketada convergente, com a semente finita mantida explicita. -/
def bracketedDirichletChart (p : ℕ) (s : ℂ) : ℂ :=
  NativeCarryGeometry.Internal.Genuine.Cp.seedSum p (dirichletTerm s) +
    ∑' k : ℕ, realCpSaturatedBracket p k s

/-- Prefixo finito da mesma carta, antes da passagem ao limite. -/
def finiteBracketedDirichletChart (p M : ℕ) (s : ℂ) : ℂ :=
  NativeCarryGeometry.Internal.Genuine.Cp.seedSum p (dirichletTerm s) +
    ∑ k ∈ Finset.range M, realCpSaturatedBracket p k s

/-!
Os prefixos bracketados analiticos nao sao uma aproximacao diferente: em
cada corte `M`, eles sao literalmente a carta `Genuine.Cp.finiteChart`.
-/
theorem finiteBracketedDirichletChart_eq_finiteChart
    (p M : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) (s : ℂ) :
    finiteBracketedDirichletChart p M s =
      NativeCarryGeometry.Internal.Genuine.Cp.finiteChart p M (dirichletTerm s) := by
  unfold finiteBracketedDirichletChart NativeCarryGeometry.Internal.Genuine.Cp.finiteChart
  apply congrArg (fun tail : ℂ ↦
    NativeCarryGeometry.Internal.Genuine.Cp.seedSum p (dirichletTerm s) + tail)
  apply Finset.sum_congr rfl
  intro k hk
  exact realCpSaturatedBracket_eq_genuineBracket p k hp hpodd s

/-- Passagem ao limite dos prefixos bracketados no dominio `re(s)>-1`. -/
theorem finiteBracketedDirichletChart_tendsto
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : -1 < s.re) :
    Filter.Tendsto (fun M : ℕ ↦ finiteBracketedDirichletChart p M s)
      Filter.atTop (nhds (bracketedDirichletChart p s)) := by
  have hsum := (summable_realCpSaturatedBracket p hp hs).tendsto_sum_tsum_nat
  simpa [finiteBracketedDirichletChart, bracketedDirichletChart] using
    tendsto_const_nhds.add hsum

/-!
A mesma passagem ao limite, agora escrita diretamente para os prefixos
`Genuine.Cp.finiteChart`. Esta e a identificacao solicitada entre a camera
finita Genuine e a carta bracketada convergente.
-/
theorem finiteChart_dirichlet_tendsto_bracketedDirichletChart
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : -1 < s.re) :
    Filter.Tendsto
      (fun M : ℕ ↦
        NativeCarryGeometry.Internal.Genuine.Cp.finiteChart p M (dirichletTerm s))
      Filter.atTop (nhds (bracketedDirichletChart p s)) := by
  exact (finiteBracketedDirichletChart_tendsto p hp hs).congr'
    (Filter.Eventually.of_forall fun M ↦
      finiteBracketedDirichletChart_eq_finiteChart p M hp hpodd s)

/-!
No semiplano comum `re(s)>1`, os dois limites ja construidos partem da mesma
sequencia finita. A unicidade do limite identifica a carta bracketada com o
fator Genuine. Isto ainda nao invoca continuacao analitica.
-/
theorem bracketedDirichletChart_eq_genuine_factor
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : 1 < s.re) :
    bracketedDirichletChart p s =
      (1 - (p : ℂ) ^ (1 - s)) * genuineDirichlet s := by
  exact tendsto_nhds_unique
    (finiteChart_dirichlet_tendsto_bracketedDirichletChart
      p hp hpodd (by linarith [hs]))
    (finiteChart_dirichlet_tendsto_genuine_factor p hp hpodd hs)

end

end NativeCarryGeometry.Internal.Analytic.Cp

namespace NativeCarryGeometry.Analytic

noncomputable section

abbrev bracketSeries (camera : ℕ) (s : ℂ) : ℂ :=
  Internal.Analytic.Cp.bracketedDirichletChart camera s

abbrev finiteBracketSeries
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  Internal.Analytic.Cp.finiteBracketedDirichletChart
    camera cutoff s

/-- NCG-ANL-002: Bracket-Series Convergence. -/
theorem finiteBracketChart_tendsto_bracketSeries
    (camera : ℕ) (hprime : Nat.Prime camera) (hodd : Odd camera)
    {s : ℂ} (hs : -1 < s.re) :
    Filter.Tendsto
      (fun cutoff : ℕ =>
        Bracket.Balanced.finiteBracketChart
          camera cutoff (powerMonomial s))
      Filter.atTop (nhds (bracketSeries camera s)) :=
  Internal.Analytic.Cp.finiteChart_dirichlet_tendsto_bracketedDirichletChart
    camera hprime hodd hs

end
end NativeCarryGeometry.Analytic
