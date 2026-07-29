import NativeCarryGeometry.Arithmetic.BalancedResidue
import NativeCarryGeometry.Bracket.CenteredDifference
import Mathlib.Tactic


/-!
# Lei finita do Genuine

Esta e a identidade central anterior a toda analise:

`canal direto das pernas - canal bracketado = centros sobreviventes`.

Nao ha serie externa, zeros, limite ou continuacao analitica neste arquivo.
-/

open scoped BigOperators

namespace NativeCarryGeometry.Internal.Genuine

variable {ι R : Type*} [CommRing R]

/-- Soma ponderada das pernas ja agrupadas por centro. -/
def directChannel
    (centers : Finset ι) (weight legs : ι → R) : R :=
  ∑ c ∈ centers, weight c * legs c

/--
Canal bracketado: em cada centro, subtrai-se da soma das pernas o multiplo
central determinado pela camera.
-/
def bracketChannel
    (centers : Finset ι) (weight legs coefficient centerValue : ι → R) : R :=
  ∑ c ∈ centers,
    weight c * (legs c - coefficient c * centerValue c)

/-- Canal formado somente pelos centros que sobrevivem ao cancelamento. -/
def survivingCenterChannel
    (centers : Finset ι) (weight coefficient centerValue : ι → R) : R :=
  ∑ c ∈ centers, weight c * coefficient c * centerValue c

/-- Cancelamento local de uma camera em um unico centro. -/
theorem localCancellation (legs coefficient centerValue : R) :
    legs - (legs - coefficient * centerValue) = coefficient * centerValue := by
  ring

/--
Lei Genuine finita. Cada termo de perna cancela literalmente e resta apenas o
termo central ponderado. A identidade vale para qualquer conjunto finito de
centros e nao depende da origem analitica dos valores.
-/
theorem finiteCancellation
    (centers : Finset ι) (weight legs coefficient centerValue : ι → R) :
    directChannel centers weight legs -
        bracketChannel centers weight legs coefficient centerValue =
      survivingCenterChannel centers weight coefficient centerValue := by
  classical
  simp only [directChannel, bracketChannel, survivingCenterChannel]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  ring

end NativeCarryGeometry.Internal.Genuine

/-!
# Camera Genuine Cp finita

Para uma camera de base `p`, as pernas sao indexadas pelos offsets balanceados
nao nulos. O bracket subtrai `(p-1)` copias do centro. A lei de cancelamento e
puramente finita e vale antes de assumir que `p` e primo.
-/

open scoped BigOperators

namespace NativeCarryGeometry.Internal.Genuine.Cp

variable {R : Type*} [CommRing R]

noncomputable section

/-- Soma das `p-1` pernas formais da camera Cp. -/
def legSum (p : ℕ) (f : ℤ → R) (center : ℤ) : R :=
  ∑ a ∈ balancedOffsets p, f (center + a)

/-- Bracket saturado da camera Cp. -/
def bracket (p : ℕ) (f : ℤ → R) (center : ℤ) : R :=
  legSum p f center - ((p - 1 : ℕ) : R) * f center

@[simp] theorem local_genuine_cancellation
    (p : ℕ) (f : ℤ → R) (center : ℤ) :
    legSum p f center - bracket p f center =
      ((p - 1 : ℕ) : R) * f center := by
  simp [bracket]

/-- Canal direto Cp numa caixa finita. -/
def finiteDirect
    (p : ℕ) (centers : Finset ℤ) (weight : ℤ → R) (f : ℤ → R) : R :=
  ∑ c ∈ centers, weight c * legSum p f c

/-- Canal dos brackets Cp na mesma caixa. -/
def finiteBrackets
    (p : ℕ) (centers : Finset ℤ) (weight : ℤ → R) (f : ℤ → R) : R :=
  ∑ c ∈ centers, weight c * bracket p f c

/-- Centros Cp sobreviventes, com multiplicidade `p-1`. -/
def finiteCenters
    (p : ℕ) (centers : Finset ℤ) (weight : ℤ → R) (f : ℤ → R) : R :=
  ∑ c ∈ centers, weight c * ((p - 1 : ℕ) : R) * f c

/-- Versao Cp da lei Genuine finita. -/
theorem finite_genuine_cancellation
    (p : ℕ) (centers : Finset ℤ) (weight : ℤ → R) (f : ℤ → R) :
    finiteDirect p centers weight f - finiteBrackets p centers weight f =
      finiteCenters p centers weight f := by
  classical
  simp only [finiteDirect, finiteBrackets, finiteCenters]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  simp [bracket]
  ring

end
end NativeCarryGeometry.Internal.Genuine.Cp

/-!
# Carta finita `C_p` por blocos completos

Este arquivo abre cada bracket antes de qualquer passagem ao limite. Para um
centro `c`, o intervalo completo de offsets e

`[-halfRange p, ..., 0, ..., halfRange p]`.

O `legSum` usa o mesmo intervalo sem o zero. Portanto um bracket saturado e
literalmente

`bloco completo no centro c - p * f(c)`.

Somando os primeiros `M` centros `p, 2p, ..., Mp`, obtemos a identidade
finita da carta como prefixo por blocos menos a correcao vertical dos centros.
Os blocos sao depois ladrilhados no intervalo literal
`1, ..., pM + halfRange p`. Ainda nao introduzimos potencias complexas, series
infinitas ou limites.
-/

open scoped BigOperators

namespace NativeCarryGeometry.Internal.Genuine.Cp

variable {R : Type*} [CommRing R]

noncomputable section

/-- Intervalo completo da camera, incluindo o offset central `0`. -/
def fullOffsets (p : ℕ) : Finset ℤ :=
  Finset.Icc (-(halfRange p : ℤ)) (halfRange p : ℤ)

/-- Um bloco completo de valores em torno do centro `center`. -/
def centerBlock (p : ℕ) (f : ℤ → R) (center : ℤ) : R :=
  ∑ a ∈ fullOffsets p, f (center + a)

/-- A semente positiva `1, ..., halfRange p` da carta finita. -/
def seedSum (p : ℕ) (f : ℤ → R) : R :=
  ∑ n ∈ Finset.Icc (1 : ℤ) (halfRange p : ℤ), f n

/-- O `k`-esimo centro positivo, com indices iniciando em zero. -/
def alignedCenter (p k : ℕ) : ℤ :=
  (p : ℤ) * ((k + 1 : ℕ) : ℤ)

/-- Soma finita da semente e dos brackets nos centros `p, ..., Mp`. -/
def finiteChart (p M : ℕ) (f : ℤ → R) : R :=
  seedSum p f +
    ∑ k ∈ Finset.range M, bracket p f (alignedCenter p k)

/-- Prefixo finito ainda escrito como semente seguida de blocos completos. -/
def blockPrefix (p M : ℕ) (f : ℤ → R) : R :=
  seedSum p f +
    ∑ k ∈ Finset.range M, centerBlock p f (alignedCenter p k)

/-- Correcao vertical: `p` copias do valor em cada centro. -/
def verticalCorrection (p M : ℕ) (f : ℤ → R) : R :=
  ∑ k ∈ Finset.range M, (p : R) * f (alignedCenter p k)

/-- Remover o centro do intervalo completo recupera os offsets das pernas. -/
@[simp] theorem fullOffsets_erase_zero (p : ℕ) :
    (fullOffsets p).erase 0 = balancedOffsets p := by
  rfl

/-- O offset central pertence sempre ao bloco completo. -/
@[simp] theorem zero_mem_fullOffsets (p : ℕ) :
    (0 : ℤ) ∈ fullOffsets p := by
  simp [fullOffsets]

/-- Para `p` impar, um bloco completo possui literalmente `p` posicoes. -/
@[simp] theorem card_fullOffsets {p : ℕ} (hpodd : Odd p) :
    (fullOffsets p).card = p := by
  have hpformNat := NativeCarryGeometry.Internal.Carry.Cp.two_mul_halfRange_add_one hpodd
  have hpformInt :
      (p : ℤ) = 2 * (halfRange p : ℤ) + 1 := by
    exact_mod_cast hpformNat.symm
  unfold fullOffsets
  rw [Int.card_Icc]
  rw [show
    (halfRange p : ℤ) + 1 - (-(halfRange p : ℤ)) = (p : ℤ) by omega]
  simp

/-- O bloco completo e a soma das pernas mais a unica copia do centro. -/
theorem centerBlock_eq_legSum_add_center
    (p : ℕ) (f : ℤ → R) (center : ℤ) :
    centerBlock p f center = legSum p f center + f center := by
  classical
  have hsum := Finset.sum_erase_add
    (fullOffsets p) (fun a : ℤ => f (center + a))
    (zero_mem_fullOffsets p)
  simpa [centerBlock, legSum] using hsum.symm

/-- Transladar os offsets completos produz o intervalo inteiro do bloco. -/
theorem centerBlock_eq_sum_Icc
    (p : ℕ) (f : ℤ → R) (center : ℤ) :
    centerBlock p f center =
      ∑ n ∈ Finset.Icc
        (center - (halfRange p : ℤ))
        (center + (halfRange p : ℤ)), f n := by
  classical
  unfold centerBlock fullOffsets
  apply Finset.sum_bijective (fun a : ℤ => center + a)
  · constructor
    · intro a b hab
      exact add_left_cancel hab
    · intro n
      exact ⟨n - center, by ring⟩
  · intro a
    simp only [Finset.mem_Icc]
    constructor <;> intro ha <;> constructor <;> omega
  · intro a ha
    rfl

/-- Soma sobre dois intervalos inteiros adjacentes. -/
theorem sum_Icc_split_adjacent
    (f : ℤ → R) {left middle right : ℤ}
    (hleft : left ≤ middle) (hright : middle < right) :
    (∑ n ∈ Finset.Icc left right, f n) =
      (∑ n ∈ Finset.Icc left middle, f n) +
        ∑ n ∈ Finset.Icc (middle + 1) right, f n := by
  classical
  have hdisjoint :
      Disjoint (Finset.Icc left middle) (Finset.Icc (middle + 1) right) := by
    rw [Finset.disjoint_left]
    intro n hnleft hnright
    simp only [Finset.mem_Icc] at hnleft hnright
    omega
  have hunion :
      Finset.Icc left middle ∪ Finset.Icc (middle + 1) right =
        Finset.Icc left right := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  rw [← hunion, Finset.sum_union hdisjoint]

/-- Acrescentar um centro acrescenta exatamente seu bloco completo. -/
theorem blockPrefix_succ
    (p M : ℕ) (f : ℤ → R) :
    blockPrefix p (M + 1) f =
      blockPrefix p M f + centerBlock p f (alignedCenter p M) := by
  unfold blockPrefix
  rw [Finset.sum_range_succ]
  ring

/-
O coeficiente `p-1` do bracket, junto da copia central que faltava nas
pernas, produz exatamente a correcao `p * f(center)`.
-/
theorem bracket_eq_centerBlock_sub_p_mul_center
    (p : ℕ) (hp : Nat.Prime p) (f : ℤ → R) (center : ℤ) :
    bracket p f center = centerBlock p f center - (p : R) * f center := by
  rw [centerBlock_eq_legSum_add_center]
  unfold bracket
  rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  ring

/-!
Identidade finita principal deste modulo. Ela nao usa convergencia externa,
zeros, ortogonalidade ou argumentos numericos.
-/
theorem finiteChart_eq_blockPrefix_sub_verticalCorrection
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ) (f : ℤ → R) :
    finiteChart p M f = blockPrefix p M f - verticalCorrection p M f := by
  classical
  unfold finiteChart blockPrefix verticalCorrection
  simp_rw [bracket_eq_centerBlock_sub_p_mul_center p hp]
  rw [Finset.sum_sub_distrib]
  ring

/-- A correcao vertical tambem pode ser lida como `p` vezes a soma dos centros. -/
theorem verticalCorrection_eq_p_mul_centerSum
    (p M : ℕ) (f : ℤ → R) :
    verticalCorrection p M f =
      (p : R) * ∑ k ∈ Finset.range M, f (alignedCenter p k) := by
  classical
  simp [verticalCorrection, Finset.mul_sum]

/-- Forma tradicional: prefixo por blocos menos `p` vezes os centros. -/
theorem finiteChart_eq_blockPrefix_sub_p_mul_centerSum
    (p : ℕ) (hp : Nat.Prime p) (M : ℕ) (f : ℤ → R) :
    finiteChart p M f =
      blockPrefix p M f -
        (p : R) * ∑ k ∈ Finset.range M, f (alignedCenter p k) := by
  rw [finiteChart_eq_blockPrefix_sub_verticalCorrection p hp]
  rw [verticalCorrection_eq_p_mul_centerSum]

/-!
Ladrilhamento minimo necessario para ligar a carta por blocos ao prefixo
literal dos inteiros positivos.
-/
theorem blockPrefix_eq_positiveIntervalSum
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (M : ℕ) (f : ℤ → R) :
    blockPrefix p M f =
      ∑ n ∈ Finset.Icc (1 : ℤ)
        ((p : ℤ) * (M : ℤ) + (halfRange p : ℤ)), f n := by
  induction M with
  | zero =>
      simp [blockPrefix, seedSum]
  | succ M ih =>
      rw [blockPrefix_succ, ih, centerBlock_eq_sum_Icc]
      have hpformNat := NativeCarryGeometry.Internal.Carry.Cp.two_mul_halfRange_add_one hpodd
      have hpformInt :
          (p : ℤ) = 2 * (halfRange p : ℤ) + 1 := by
        exact_mod_cast hpformNat.symm
      have hlower :
          alignedCenter p M - (halfRange p : ℤ) =
            (p : ℤ) * (M : ℤ) + (halfRange p : ℤ) + 1 := by
        unfold alignedCenter
        push_cast
        rw [hpformInt]
        ring
      have hupper :
          alignedCenter p M + (halfRange p : ℤ) =
            (p : ℤ) * ((M + 1 : ℕ) : ℤ) + (halfRange p : ℤ) := by
        rfl
      rw [hlower, hupper]
      have hhNat : 1 ≤ halfRange p := by
        have hpgt := hp.one_lt
        omega
      have hhInt : (1 : ℤ) ≤ (halfRange p : ℤ) := by
        exact_mod_cast hhNat
      have hnonneg : 0 ≤ (p : ℤ) * (M : ℤ) := by
        positivity
      have hleft :
          (1 : ℤ) ≤
            (p : ℤ) * (M : ℤ) + (halfRange p : ℤ) := by
        omega
      have hpIntPos : 0 < (p : ℤ) := by
        exact_mod_cast hp.pos
      have hstep :
          (p : ℤ) * ((M + 1 : ℕ) : ℤ) + (halfRange p : ℤ) =
            ((p : ℤ) * (M : ℤ) + (halfRange p : ℤ)) + (p : ℤ) := by
        push_cast
        ring
      have hright :
          (p : ℤ) * (M : ℤ) + (halfRange p : ℤ) <
            (p : ℤ) * ((M + 1 : ℕ) : ℤ) + (halfRange p : ℤ) := by
        rw [hstep]
        exact lt_add_of_pos_right _ hpIntPos
      exact (sum_Icc_split_adjacent f hleft hright).symm

/-- Carta finita escrita diretamente no prefixo positivo literal. -/
theorem finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (M : ℕ) (f : ℤ → R) :
    finiteChart p M f =
      (∑ n ∈ Finset.Icc (1 : ℤ)
        ((p : ℤ) * (M : ℤ) + (halfRange p : ℤ)), f n) -
          (p : R) * ∑ k ∈ Finset.range M, f (alignedCenter p k) := by
  rw [finiteChart_eq_blockPrefix_sub_p_mul_centerSum p hp]
  rw [blockPrefix_eq_positiveIntervalSum p hp hpodd]

end

end NativeCarryGeometry.Internal.Genuine.Cp

/-!
# Identificacao da braquetada saturada com a camera Genuine Cp

Este arquivo fecha uma identidade puramente finita. Para primo impar, os
offsets balanceados nao nulos sao exatamente os pares

`-halfRange(p), ..., -1, 1, ..., halfRange(p)`.

Logo o `Genuine.Cp.bracket`, definido pela soma das pernas menos `p-1`
copias do centro, coincide com a soma das segundas diferencas de raios
`1, ..., halfRange(p)`.
-/

open scoped BigOperators

namespace NativeCarryGeometry.Internal.Genuine.Cp

variable {R : Type*} [CommRing R]

noncomputable section

/-- Reindexacao dos raios naturais positivos pelo intervalo inteiro positivo. -/
lemma sum_nat_radii_eq_sum_int_positive
    (h : ℕ) (g : ℤ → R) :
    (∑ radius ∈ Finset.Icc 1 h, g (radius : ℤ)) =
      ∑ a ∈ Finset.Icc (1 : ℤ) (h : ℤ), g a := by
  classical
  refine Finset.sum_bij (fun radius _ ↦ (radius : ℤ)) ?_ ?_ ?_ ?_
  · intro radius hradius
    simp only [Finset.mem_Icc] at hradius ⊢
    exact_mod_cast hradius
  · intro radius₁ hradius₁ radius₂ hradius₂ heq
    exact_mod_cast heq
  · intro a ha
    have haBounds := Finset.mem_Icc.mp ha
    have haNonneg : 0 ≤ a := le_trans (by norm_num) haBounds.1
    have hcast : ((a.toNat : ℕ) : ℤ) = a := Int.toNat_of_nonneg haNonneg
    refine ⟨a.toNat, ?_, hcast⟩
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast (show (1 : ℤ) ≤ (a.toNat : ℤ) by simpa [hcast] using haBounds.1)
    · exact_mod_cast (show (a.toNat : ℤ) ≤ (h : ℤ) by simpa [hcast] using haBounds.2)
  · intro radius hradius
    rfl

/-- Reindexacao dos raios naturais positivos pelo intervalo inteiro negativo. -/
lemma sum_neg_nat_radii_eq_sum_int_negative
    (h : ℕ) (g : ℤ → R) :
    (∑ radius ∈ Finset.Icc 1 h, g (-(radius : ℤ))) =
      ∑ a ∈ Finset.Icc (-(h : ℤ)) (-1), g a := by
  classical
  refine Finset.sum_bij (fun radius _ ↦ -(radius : ℤ)) ?_ ?_ ?_ ?_
  · intro radius hradius
    simp only [Finset.mem_Icc] at hradius ⊢
    have hlower : (1 : ℤ) ≤ (radius : ℤ) := by exact_mod_cast hradius.1
    have hupper : (radius : ℤ) ≤ (h : ℤ) := by exact_mod_cast hradius.2
    constructor <;> omega
  · intro radius₁ hradius₁ radius₂ hradius₂ heq
    have : (radius₁ : ℤ) = (radius₂ : ℤ) := neg_injective heq
    exact_mod_cast this
  · intro a ha
    have haBounds := Finset.mem_Icc.mp ha
    have hnegNonneg : 0 ≤ -a := by omega
    have hcast : (((-a).toNat : ℕ) : ℤ) = -a :=
      Int.toNat_of_nonneg hnegNonneg
    refine ⟨(-a).toNat, ?_, ?_⟩
    · apply Finset.mem_Icc.mpr
      constructor
      · exact_mod_cast (show (1 : ℤ) ≤ ((-a).toNat : ℤ) by
          rw [hcast]
          omega)
      · exact_mod_cast (show (((-a).toNat : ℕ) : ℤ) ≤ (h : ℤ) by
          rw [hcast]
          omega)
    · rw [hcast]
      omega
  · intro radius hradius
    rfl

/-- Um bloco completo e o centro seguido dos pares de raios positivos. -/
theorem centerBlock_eq_center_add_pairSum
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (f : ℤ → R) (center : ℤ) :
    centerBlock p f center =
      f center +
        ∑ radius ∈ Finset.Icc 1 (halfRange p),
          (f (center - (radius : ℤ)) + f (center + (radius : ℤ))) := by
  classical
  rcases hpodd with ⟨q, hq⟩
  have hp3 : 3 ≤ p := by
    have hp2 := hp.two_le
    omega
  have hh : 1 ≤ halfRange p := by
    unfold halfRange
    omega
  have hhInt : (1 : ℤ) ≤ (halfRange p : ℤ) := by
    exact_mod_cast hh
  have hneg : -(halfRange p : ℤ) ≤ -1 := by omega
  have hpos : (0 : ℤ) < halfRange p := by exact_mod_cast hh
  rw [centerBlock]
  unfold fullOffsets
  rw [sum_Icc_split_adjacent (fun a : ℤ ↦ f (center + a)) hneg (by omega)]
  rw [sum_Icc_split_adjacent (fun a : ℤ ↦ f (center + a)) (by omega) hpos]
  norm_num only [Int.reduceNeg, Int.reduceAdd, zero_add, add_zero]
  rw [← sum_neg_nat_radii_eq_sum_int_negative
    (R := R) (halfRange p) (fun a : ℤ ↦ f (center + a))]
  rw [← sum_nat_radii_eq_sum_int_positive
    (R := R) (halfRange p) (fun a : ℤ ↦ f (center + a))]
  simp [Finset.sum_add_distrib, sub_eq_add_neg]
  abel

/-- As pernas balanceadas sao exatamente a soma dos pares de raios positivos. -/
theorem legSum_eq_pairSum
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (f : ℤ → R) (center : ℤ) :
    legSum p f center =
      ∑ radius ∈ Finset.Icc 1 (halfRange p),
        (f (center - (radius : ℤ)) + f (center + (radius : ℤ))) := by
  have hblock := centerBlock_eq_center_add_pairSum p hp hpodd f center
  rw [centerBlock_eq_legSum_add_center] at hblock
  exact add_right_cancel (hblock.trans (add_comm _ _))

/-!
Identidade finita central: a definicao por pernas balanceadas e a definicao
por segundas diferencas saturadas sao o mesmo objeto.
-/
theorem bracket_eq_saturatedBracket
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (f : ℤ → R) (center : ℤ) :
    bracket p f center =
      NativeCarryGeometry.Internal.saturatedBracket (halfRange p) f center := by
  classical
  have hleg := legSum_eq_pairSum p hp hpodd f center
  have hpform := NativeCarryGeometry.Internal.Carry.Cp.two_mul_halfRange_add_one hpodd
  have hpminus : p - 1 = 2 * halfRange p := by omega
  have hcard : (Finset.Icc 1 (halfRange p)).card = halfRange p := by
    rw [Nat.card_Icc]
    omega
  unfold bracket NativeCarryGeometry.Internal.saturatedBracket NativeCarryGeometry.Internal.centeredSecondDifference
  rw [hleg]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [hcard, hpminus, nsmul_eq_mul]
  ring

end

end NativeCarryGeometry.Internal.Genuine.Cp

namespace NativeCarryGeometry.Bracket.Balanced

abbrev halfRange (camera : ℕ) : ℕ :=
  Internal.Genuine.Cp.halfRange camera

noncomputable abbrev balancedBracket
    {R : Type*} [CommRing R]
    (camera : ℕ) (f : ℤ → R) (center : ℤ) : R :=
  Internal.Genuine.Cp.bracket camera f center

abbrev alignedCenter (camera cutoffIndex : ℕ) : ℤ :=
  Internal.Genuine.Cp.alignedCenter camera cutoffIndex

noncomputable abbrev finiteBracketChart
    {R : Type*} [CommRing R]
    (camera cutoff : ℕ) (f : ℤ → R) : R :=
  Internal.Genuine.Cp.finiteChart camera cutoff f

/-- NCG-BRK-003: Centered Bracket Representation. -/
theorem balancedBracket_eq_saturatedBracket
    {R : Type*} [CommRing R]
    (camera : ℕ) (hprime : Nat.Prime camera) (hodd : Odd camera)
    (f : ℤ → R) (center : ℤ) :
    balancedBracket camera f center =
      Bracket.saturatedBracket (halfRange camera) f center :=
  Internal.Genuine.Cp.bracket_eq_saturatedBracket
    camera hprime hodd f center

/-- NCG-BRK-004: Finite Bracket Cancellation. -/
theorem finiteBracketCancellation
    {R : Type*} [CommRing R]
    (camera : ℕ) (centers : Finset ℤ)
    (weight : ℤ → R) (f : ℤ → R) :
    Internal.Genuine.Cp.finiteDirect camera centers weight f -
        Internal.Genuine.Cp.finiteBrackets camera centers weight f =
      Internal.Genuine.Cp.finiteCenters camera centers weight f :=
  Internal.Genuine.Cp.finite_genuine_cancellation
    camera centers weight f

/-- NCG-BRK-005: Finite Bracket-Chart Identity. -/
theorem finiteBracketChart_eq_intervalSum_sub_centerCorrection
    {R : Type*} [CommRing R]
    (camera : ℕ) (hprime : Nat.Prime camera) (hodd : Odd camera)
    (cutoff : ℕ) (f : ℤ → R) :
    finiteBracketChart camera cutoff f =
      (∑ n ∈ Finset.Icc (1 : ℤ)
        ((camera : ℤ) * (cutoff : ℤ) + (halfRange camera : ℤ)), f n) -
          (camera : R) * ∑ k ∈ Finset.range cutoff,
            f (alignedCenter camera k) :=
  Internal.Genuine.Cp.finiteChart_eq_positiveIntervalSum_sub_p_mul_centerSum
    camera hprime hodd cutoff f

end NativeCarryGeometry.Bracket.Balanced
