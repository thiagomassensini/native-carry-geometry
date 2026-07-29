import NativeCarryGeometry.Bracket.BalancedCamera
import Mathlib.Analysis.PSeriesComplex


/-!
# Fatoracao finita da carta Cp em potencias de Dirichlet

Este arquivo faz somente a primeira especializacao analitica indispensavel.
Para inteiros positivos, usamos a potencia complexa principal `n ^ (-s)`.
A positividade das bases permite aplicar a multiplicatividade de `cpow` sem
qualquer ambiguidade de ramo.

O resultado central e inteiramente finito:

`p * sum_{m=1}^M (p*m)^(-s) = p^(1-s) * sum_{m=1}^M m^(-s)`.

Nao ha serie externa, convergencia infinita, continuacao analitica ou zeros.
-/

open scoped BigOperators

namespace NativeCarryGeometry.Internal.Analytic.Cp

noncomputable section

/-- Monomio de Dirichlet no ramo principal; a carta o usa apenas em `n > 0`. -/
def dirichletTerm (s : ℂ) (n : ℤ) : ℂ :=
  (n : ℂ) ^ (-s)

/-- Prefixo `1^(-s) + ... + M^(-s)` escrito com indices iniciando em zero. -/
def positiveDirichletPrefix (s : ℂ) (M : ℕ) : ℂ :=
  ∑ k ∈ Finset.range M, dirichletTerm s (((k + 1 : ℕ) : ℤ))

/-- Em um centro alinhado, o monomio separa base prima e indice horizontal. -/
theorem dirichletTerm_alignedCenter
    (p k : ℕ) (s : ℂ) :
    dirichletTerm s (NativeCarryGeometry.Internal.Genuine.Cp.alignedCenter p k) =
      dirichletTerm s (p : ℤ) *
        dirichletTerm s (((k + 1 : ℕ) : ℤ)) := by
  simpa [dirichletTerm, NativeCarryGeometry.Internal.Genuine.Cp.alignedCenter] using
    (Complex.natCast_mul_natCast_cpow p (k + 1) (-s))

/-- O coeficiente `p` junto de `p^(-s)` e exatamente `p^(1-s)`. -/
theorem prime_mul_dirichletTerm_eq_cpow_one_sub
    (p : ℕ) (hp : Nat.Prime p) (s : ℂ) :
    (p : ℂ) * dirichletTerm s (p : ℤ) =
      (p : ℂ) ^ (1 - s) := by
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  simpa [dirichletTerm, sub_eq_add_neg] using
    (Complex.cpow_add (x := (p : ℂ)) (1 : ℂ) (-s) hp0).symm

/-!
Coracao desta etapa: a correcao vertical finita se separa em um fator da base
e o prefixo horizontal curto.
-/
theorem p_mul_centerSum_dirichlet_eq_cpow_mul_prefix
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ) (s : ℂ) :
    (p : ℂ) *
        ∑ k ∈ Finset.range M,
          dirichletTerm s (NativeCarryGeometry.Internal.Genuine.Cp.alignedCenter p k) =
      (p : ℂ) ^ (1 - s) * positiveDirichletPrefix s M := by
  unfold positiveDirichletPrefix
  simp_rw [dirichletTerm_alignedCenter]
  rw [← Finset.mul_sum]
  rw [← mul_assoc]
  rw [prime_mul_dirichletTerm_eq_cpow_one_sub p hp s]

/-- Carta Cp finita: prefixo positivo longo menos o prefixo vertical fatorado. -/
theorem finiteChart_dirichlet_eq_prefix_sub_cpow_mul_prefix
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (M : ℕ) (s : ℂ) :
    NativeCarryGeometry.Internal.Genuine.Cp.finiteChart p M (dirichletTerm s) =
      (∑ n ∈ Finset.Icc (1 : ℤ)
        ((p : ℤ) * (M : ℤ) +
          (NativeCarryGeometry.Internal.Genuine.Cp.halfRange p : ℤ)), dirichletTerm s n) -
        (p : ℂ) ^ (1 - s) * positiveDirichletPrefix s M := by
  rw [NativeCarryGeometry.Internal.Genuine.Cp.finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum
    p hp hpodd]
  rw [p_mul_centerSum_dirichlet_eq_cpow_mul_prefix p hp M s]

end

end NativeCarryGeometry.Internal.Analytic.Cp

/-!
# Limite da carta Cp no semiplano de convergencia absoluta

Partimos da identidade finita ja verificada e tomamos `M -> infinity` apenas
sob a hipotese `1 < re(s)`. O objeto Genuine desta etapa e definido primeiro
pela propria serie de Dirichlet positiva, sem identificacao externa.

O resultado e

`finiteChart_p,M(s) -> (1 - p^(1-s)) * genuineDirichlet(s)`.

Este arquivo nao trata continuacao analitica, o dominio bracketado maior,
zeros ou a ponte Green.
-/

open scoped BigOperators Topology
open Filter

namespace NativeCarryGeometry.Internal.Analytic.Cp

noncomputable section

/-- Canal Genuine inicial: a serie positiva `sum_{n>=1} n^(-s)`. -/
def genuineDirichlet (s : ℂ) : ℂ :=
  ∑' k : ℕ, dirichletTerm s (((k + 1 : ℕ) : ℤ))

/-- No semiplano `re(s)>1`, os monomios positivos sao somaveis. -/
theorem summable_dirichletTerm_nat_add_one
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun k : ℕ =>
      dirichletTerm s (((k + 1 : ℕ) : ℤ))) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  have hshift := hbase.comp_injective
    (show Function.Injective (fun n : ℕ => n + 1) by
      intro a b hab
      exact Nat.add_right_cancel hab)
  simpa [Function.comp_def, dirichletTerm, Complex.cpow_neg] using hshift

/-- Os prefixos positivos convergem para o canal Genuine inicial. -/
theorem positiveDirichletPrefix_tendsto_genuineDirichlet
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (positiveDirichletPrefix s) atTop
      (nhds (genuineDirichlet s)) := by
  change Tendsto
    (fun N : ℕ => ∑ k ∈ Finset.range N,
      dirichletTerm s (((k + 1 : ℕ) : ℤ)))
    atTop
    (nhds (∑' k : ℕ,
      dirichletTerm s (((k + 1 : ℕ) : ℤ))))
  exact (summable_dirichletTerm_nat_add_one hs).tendsto_sum_tsum_nat

/-- Acrescentar um termo ao prefixo positivo. -/
theorem positiveDirichletPrefix_succ
    (s : ℂ) (N : ℕ) :
    positiveDirichletPrefix s (N + 1) =
      positiveDirichletPrefix s N +
        dirichletTerm s (((N + 1 : ℕ) : ℤ)) := by
  simp [positiveDirichletPrefix, Finset.sum_range_succ]

/-- O prefixo por `range` e a soma literal no intervalo inteiro `1,...,N`. -/
theorem positiveDirichletPrefix_eq_sum_Icc
    (s : ℂ) (N : ℕ) :
    positiveDirichletPrefix s N =
      ∑ n ∈ Finset.Icc (1 : ℤ) (N : ℤ), dirichletTerm s n := by
  induction N with
  | zero =>
      simp [positiveDirichletPrefix]
  | succ N ih =>
      rw [positiveDirichletPrefix_succ, ih]
      have hset :
          insert (((N + 1 : ℕ) : ℤ))
              (Finset.Icc (1 : ℤ) (N : ℤ)) =
            Finset.Icc (1 : ℤ) (((N + 1 : ℕ) : ℤ)) := by
        ext n
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hnot :
          (((N + 1 : ℕ) : ℤ)) ∉ Finset.Icc (1 : ℤ) (N : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      rw [← hset, Finset.sum_insert hnot]
      ring

/-- A carta finita usa dois prefixos da mesma serie Genuine. -/
theorem finiteChart_dirichlet_eq_two_prefixes
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (M : ℕ) (s : ℂ) :
    NativeCarryGeometry.Internal.Genuine.Cp.finiteChart p M (dirichletTerm s) =
      positiveDirichletPrefix s
          (p * M + NativeCarryGeometry.Internal.Genuine.Cp.halfRange p) -
        (p : ℂ) ^ (1 - s) * positiveDirichletPrefix s M := by
  rw [finiteChart_dirichlet_eq_prefix_sub_cpow_mul_prefix p hp hpodd M s]
  have hlong :
      (∑ n ∈ Finset.Icc (1 : ℤ)
        ((p : ℤ) * (M : ℤ) +
          (NativeCarryGeometry.Internal.Genuine.Cp.halfRange p : ℤ)), dirichletTerm s n) =
        positiveDirichletPrefix s
          (p * M + NativeCarryGeometry.Internal.Genuine.Cp.halfRange p) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using
      (positiveDirichletPrefix_eq_sum_Icc s
        (p * M + NativeCarryGeometry.Internal.Genuine.Cp.halfRange p)).symm
  rw [hlong]

/-- O cutoff longo `p*M+halfRange(p)` tambem tende ao infinito. -/
theorem chartCutoff_tendsto_atTop
    (p : ℕ) (hp : Nat.Prime p) :
    Tendsto (fun M : ℕ =>
      p * M + NativeCarryGeometry.Internal.Genuine.Cp.halfRange p) atTop atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop b] with a ha
  have hpone : 1 ≤ p := hp.one_le
  calc
    b ≤ a := ha
    _ ≤ p * a := by
      simpa only [one_mul] using Nat.mul_le_mul_right a hpone
    _ ≤ p * a + NativeCarryGeometry.Internal.Genuine.Cp.halfRange p :=
      Nat.le_add_right _ _

/-!
Passagem ao limite principal. Os dois prefixos convergem para o mesmo canal;
a identidade finita e a continuidade das operacoes produzem o fator da carta.
-/
theorem finiteChart_dirichlet_tendsto_genuine_factor
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto
      (fun M : ℕ =>
        NativeCarryGeometry.Internal.Genuine.Cp.finiteChart p M (dirichletTerm s))
      atTop
      (nhds ((1 - (p : ℂ) ^ (1 - s)) * genuineDirichlet s)) := by
  have hprefix := positiveDirichletPrefix_tendsto_genuineDirichlet hs
  have hlong :
      Tendsto
        (fun M : ℕ => positiveDirichletPrefix s
          (p * M + NativeCarryGeometry.Internal.Genuine.Cp.halfRange p))
        atTop (nhds (genuineDirichlet s)) := by
    simpa [Function.comp_def] using
      hprefix.comp (chartCutoff_tendsto_atTop p hp)
  have hscaled :
      Tendsto
        (fun M : ℕ =>
          (p : ℂ) ^ (1 - s) * positiveDirichletPrefix s M)
        atTop
        (nhds ((p : ℂ) ^ (1 - s) * genuineDirichlet s)) := by
    exact tendsto_const_nhds.mul hprefix
  have hdiff := hlong.sub hscaled
  have heq :
      (fun M : ℕ =>
        positiveDirichletPrefix s
            (p * M + NativeCarryGeometry.Internal.Genuine.Cp.halfRange p) -
          (p : ℂ) ^ (1 - s) * positiveDirichletPrefix s M) =ᶠ[atTop]
        (fun M : ℕ =>
          NativeCarryGeometry.Internal.Genuine.Cp.finiteChart p M (dirichletTerm s)) :=
    Filter.Eventually.of_forall fun M =>
      (finiteChart_dirichlet_eq_two_prefixes p hp hpodd M s).symm
  have hchart := hdiff.congr' heq
  simpa only [sub_mul, one_mul] using hchart

end

end NativeCarryGeometry.Internal.Analytic.Cp

namespace NativeCarryGeometry.Analytic

noncomputable section

abbrev powerMonomial (s : ℂ) (n : ℤ) : ℂ :=
  Internal.Analytic.Cp.dirichletTerm s n

abbrev positivePowerPrefix (s : ℂ) (cutoff : ℕ) : ℂ :=
  Internal.Analytic.Cp.positiveDirichletPrefix s cutoff

abbrev convergentPowerSeries (s : ℂ) : ℂ :=
  Internal.Analytic.Cp.genuineDirichlet s

/-- NCG-ANL-001: Finite Power-Sum Factorization. -/
theorem finiteBracketChart_eq_two_prefixes
    (camera : ℕ) (hprime : Nat.Prime camera) (hodd : Odd camera)
    (cutoff : ℕ) (s : ℂ) :
    Bracket.Balanced.finiteBracketChart
        camera cutoff (powerMonomial s) =
      positivePowerPrefix s
          (camera * cutoff + Bracket.Balanced.halfRange camera) -
        (camera : ℂ) ^ (1 - s) *
          positivePowerPrefix s cutoff :=
  Internal.Analytic.Cp.finiteChart_dirichlet_eq_two_prefixes
    camera hprime hodd cutoff s

end
end NativeCarryGeometry.Analytic
