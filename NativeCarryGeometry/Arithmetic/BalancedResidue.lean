import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic


/-!
# Offsets balanceados da camera prima

Para um natural `p`, usamos o semialcance `(p-1)/2` e removemos o zero do
intervalo simetrico. As hipoteses "p primo e impar" entram nos teoremas de
cardinalidade e cobertura residual, que serao adicionados separadamente.
-/

namespace NativeCarryGeometry.Internal.Genuine.Cp

noncomputable section

/-- Semialcance da camera prima. -/
def halfRange (p : ℕ) : ℕ :=
  (p - 1) / 2

/-- Conjunto finito `{-h, ..., -1, 1, ..., h}`. -/
def balancedOffsets (p : ℕ) : Finset ℤ :=
  (Finset.Icc (-(halfRange p : ℤ)) (halfRange p : ℤ)).erase 0

@[simp] theorem zero_not_mem_balancedOffsets (p : ℕ) :
    (0 : ℤ) ∉ balancedOffsets p := by
  simp [balancedOffsets]

theorem mem_balancedOffsets_iff {p : ℕ} {a : ℤ} :
    a ∈ balancedOffsets p ↔
      a ≠ 0 ∧ (-(halfRange p : ℤ) ≤ a ∧ a ≤ (halfRange p : ℤ)) := by
  simp [balancedOffsets]

end
end NativeCarryGeometry.Internal.Genuine.Cp

/-!
# Residuos nao nulos e offsets balanceados Cp

Para um primo impar `p`, cada residuo nao nulo modulo `p` possui um unico
representante no intervalo balanceado

`[-(p-1)/2, (p-1)/2] \ {0}`.

Usamos `ZMod.valMinAbs` como representante canonico. Este e o passo finito que
identifica as `p-1` pernas da camera Cp com os residuos nao nulos.

Nao ha serie externa, limite ou zero analitico neste arquivo.
-/

namespace NativeCarryGeometry.Internal.Carry.Cp

open NativeCarryGeometry.Internal.Genuine.Cp

/-- Um offset que pertence a camera balanceada de base `p`. -/
def BalancedOffset (p : ℕ) :=
  {a : ℤ // a ∈ balancedOffsets p}

/-- Um residuo nao nulo modulo `p`. -/
def NonzeroResidue (p : ℕ) :=
  {x : ZMod p // x ≠ 0}

/-- Para `p` impar, o semialcance tambem e `p/2`. -/
theorem halfRange_eq_div_two {p : ℕ} (hpodd : Odd p) :
    halfRange p = p / 2 := by
  rcases hpodd with ⟨q, hq⟩
  unfold halfRange
  omega

/-- Forma aritmetica de um modulo impar em torno de seu semialcance. -/
theorem two_mul_halfRange_add_one {p : ℕ} (hpodd : Odd p) :
    2 * halfRange p + 1 = p := by
  rcases hpodd with ⟨q, hq⟩
  unfold halfRange
  omega

/--
O representante minimo de um offset que ja esta na camera e o proprio offset.
-/
theorem valMinAbs_intCast_of_mem
    {p : ℕ} (hp : Nat.Prime p) (hpodd : Odd p)
    {a : ℤ} (ha : a ∈ balancedOffsets p) :
    (a : ZMod p).valMinAbs = a := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hpformNat := two_mul_halfRange_add_one hpodd
  have hpformInt :
      (p : ℤ) = 2 * (halfRange p : ℤ) + 1 := by
    exact_mod_cast hpformNat.symm
  have habounds := (mem_balancedOffsets_iff.mp ha).2
  apply (ZMod.valMinAbs_spec (a : ZMod p) a).2
  refine ⟨rfl, ?_⟩
  constructor <;> omega

/-- Converter um offset balanceado produz um residuo nao nulo. -/
def residueOfBalanced
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) :
    BalancedOffset p → NonzeroResidue p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro a
  refine ⟨(a.1 : ZMod p), ?_⟩
  intro hzero
  have ha0 : a.1 = 0 := by
    calc
      a.1 = (a.1 : ZMod p).valMinAbs :=
        (valMinAbs_intCast_of_mem hp hpodd a.2).symm
      _ = (0 : ZMod p).valMinAbs :=
        congrArg (fun x : ZMod p => x.valMinAbs) hzero
      _ = 0 := ZMod.valMinAbs_zero p
  exact (mem_balancedOffsets_iff.mp a.2).1 ha0

/-- O representante minimo de um residuo nao nulo pertence a camera. -/
def balancedOfResidue
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) :
    NonzeroResidue p → BalancedOffset p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  intro x
  refine ⟨x.1.valMinAbs, ?_⟩
  apply mem_balancedOffsets_iff.mpr
  constructor
  · intro hzero
    exact x.2 ((ZMod.valMinAbs_eq_zero x.1).mp hzero)
  · have hpformNat := two_mul_halfRange_add_one hpodd
    have hpformInt :
        (p : ℤ) = 2 * (halfRange p : ℤ) + 1 := by
      exact_mod_cast hpformNat.symm
    have hwindow := ZMod.valMinAbs_mem_Ioc x.1
    have hlower : (-(p : ℤ)) < x.1.valMinAbs * 2 := hwindow.1
    have hupper : x.1.valMinAbs * 2 ≤ (p : ℤ) := hwindow.2
    constructor <;> omega

/--
Bijeção canonica entre as pernas balanceadas e os residuos nao nulos modulo
um primo impar.
-/
noncomputable def balancedOffsetEquivNonzeroResidue
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) :
    BalancedOffset p ≃ NonzeroResidue p where
  toFun := residueOfBalanced p hp hpodd
  invFun := balancedOfResidue p hp hpodd
  left_inv a := by
    apply Subtype.ext
    change (a.1 : ZMod p).valMinAbs = a.1
    exact valMinAbs_intCast_of_mem hp hpodd a.2
  right_inv x := by
    apply Subtype.ext
    change ((x.1.valMinAbs : ℤ) : ZMod p) = x.1
    exact ZMod.coe_valMinAbs x.1

/-- A camera balanceada de modulo impar possui exatamente `p-1` pernas. -/
theorem card_balancedOffsets {p : ℕ} (hpodd : Odd p) :
    (balancedOffsets p).card = p - 1 := by
  have hpformNat := two_mul_halfRange_add_one hpodd
  have hpformInt :
      (p : ℤ) = 2 * (halfRange p : ℤ) + 1 := by
    exact_mod_cast hpformNat.symm
  have hcard :
      (Finset.Icc (-(halfRange p : ℤ)) (halfRange p : ℤ)).card = p := by
    rw [Int.card_Icc]
    rw [show
      (halfRange p : ℤ) + 1 - (-(halfRange p : ℤ)) = (p : ℤ) by omega]
    simp
  unfold balancedOffsets
  rw [Finset.card_erase_of_mem]
  · rw [hcard]
  · simp

end NativeCarryGeometry.Internal.Carry.Cp

/-!
# Bijeção global centro--offset Cₚ

Fixe um primo ímpar `p`. Todo inteiro `n` não divisível por `p` admite uma
decomposição única

`n = c + a`,

na qual `p ∣ c` e `a` é um offset balanceado não nulo da câmera Cₚ. O offset
é o representante `ZMod.valMinAbs` da classe residual de `n`; o centro é
literalmente `n - a`.

Este arquivo prova a bijeção global entre pernas e incidências
`(centro múltiplo de p, offset balanceado)`. Não há série externa, limite ou
afirmação espectral aqui.
-/

namespace NativeCarryGeometry.Internal.Carry.Cp

open NativeCarryGeometry.Internal.Genuine.Cp

noncomputable section

/-- Inteiros que não pertencem à vertical de base `p`. -/
def Nonmultiple (p : ℕ) :=
  {n : ℤ // ¬ ((p : ℤ) ∣ n)}

/--
Uma incidência Cₚ guarda um centro múltiplo de `p` e um offset balanceado.
A perna correspondente é recuperada somando as duas coordenadas.
-/
def Incidence (p : ℕ) :=
  {x : ℤ × BalancedOffset p // (p : ℤ) ∣ x.1}

/-- A classe residual não nula de uma perna Cₚ. -/
def residueOfNonmultiple (p : ℕ) (n : Nonmultiple p) : NonzeroResidue p := by
  refine ⟨(n.1 : ZMod p), ?_⟩
  intro hzero
  exact n.2 ((ZMod.intCast_zmod_eq_zero_iff_dvd n.1 p).mp hzero)

/-- O único offset balanceado congruente à perna módulo `p`. -/
def offsetOfNonmultiple
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) : BalancedOffset p :=
  (balancedOffsetEquivNonzeroResidue p hp hpodd).symm
    (residueOfNonmultiple p n)

/-- O offset escolhido representa exatamente a classe residual da perna. -/
@[simp] theorem cast_offsetOfNonmultiple
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) :
    ((offsetOfNonmultiple p hp hpodd n).1 : ZMod p) = (n.1 : ZMod p) := by
  change
    (residueOfBalanced p hp hpodd
      (offsetOfNonmultiple p hp hpodd n)).1 =
      (residueOfNonmultiple p n).1
  exact congrArg Subtype.val
    ((balancedOffsetEquivNonzeroResidue p hp hpodd).apply_symm_apply
      (residueOfNonmultiple p n))

/-- O centro canônico é o que sobra depois de retirar o offset balanceado. -/
def centerOfNonmultiple
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) : ℤ :=
  n.1 - (offsetOfNonmultiple p hp hpodd n).1

/-- O centro canônico pertence à vertical de base `p`. -/
theorem dvd_centerOfNonmultiple
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) :
    (p : ℤ) ∣ centerOfNonmultiple p hp hpodd n := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd
    (centerOfNonmultiple p hp hpodd n) p).mp
  unfold centerOfNonmultiple
  rw [Int.cast_sub]
  rw [cast_offsetOfNonmultiple]
  simp

/-- A incidência determinada por uma perna não múltipla de `p`. -/
def incidenceOfNonmultiple
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) : Incidence p :=
  ⟨(centerOfNonmultiple p hp hpodd n,
      offsetOfNonmultiple p hp hpodd n),
    dvd_centerOfNonmultiple p hp hpodd n⟩

/-- A perna guardada por uma incidência continua não divisível por `p`. -/
def nonmultipleOfIncidence
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (x : Incidence p) : Nonmultiple p := by
  refine ⟨x.1.1 + x.1.2.1, ?_⟩
  intro hdiv
  have hsum : ((x.1.1 + x.1.2.1 : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd
      (x.1.1 + x.1.2.1) p).mpr hdiv
  have hcenter : (x.1.1 : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd x.1.1 p).mpr x.2
  have hoffset : (x.1.2.1 : ZMod p) = 0 := by
    simpa [hcenter] using hsum
  exact (residueOfBalanced p hp hpodd x.1.2).2 hoffset

/-- Retirar o offset e recolocá-lo recupera literalmente a perna. -/
@[simp] theorem incidenceOfNonmultiple_leg
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) :
    (incidenceOfNonmultiple p hp hpodd n).1.1 +
      (incidenceOfNonmultiple p hp hpodd n).1.2.1 = n.1 := by
  simp [incidenceOfNonmultiple, centerOfNonmultiple]

/--
Começar por uma incidência e recalcular o representante balanceado preserva
exatamente o offset original.
-/
theorem offsetOf_nonmultipleOfIncidence
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (x : Incidence p) :
    offsetOfNonmultiple p hp hpodd
      (nonmultipleOfIncidence p hp hpodd x) = x.1.2 := by
  let e := balancedOffsetEquivNonzeroResidue p hp hpodd
  change e.symm
    (residueOfNonmultiple p (nonmultipleOfIncidence p hp hpodd x)) = x.1.2
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  change ((x.1.1 + x.1.2.1 : ℤ) : ZMod p) = (x.1.2.1 : ZMod p)
  have hcenter : (x.1.1 : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd x.1.1 p).mpr x.2
  simp [hcenter]

/--
Bijeção global Cₚ: pernas não múltiplas de `p` correspondem exatamente às
incidências `(centro múltiplo de p, offset balanceado)`.
-/
noncomputable def nonmultipleEquivIncidence
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p) :
    Nonmultiple p ≃ Incidence p where
  toFun := incidenceOfNonmultiple p hp hpodd
  invFun := nonmultipleOfIncidence p hp hpodd
  left_inv n := by
    apply Subtype.ext
    exact incidenceOfNonmultiple_leg p hp hpodd n
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · change centerOfNonmultiple p hp hpodd
        (nonmultipleOfIncidence p hp hpodd x) = x.1.1
      unfold centerOfNonmultiple
      rw [congrArg Subtype.val
        (offsetOf_nonmultipleOfIncidence p hp hpodd x)]
      change (x.1.1 + x.1.2.1) - x.1.2.1 = x.1.1
      ring
    · exact offsetOf_nonmultipleOfIncidence p hp hpodd x

/--
Forma existencial e única da decomposição: para cada perna há exatamente uma
incidência cujo centro mais offset é essa perna.
-/
theorem existsUnique_incidence
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) :
    ∃! x : Incidence p, x.1.1 + x.1.2.1 = n.1 := by
  let e := nonmultipleEquivIncidence p hp hpodd
  refine ⟨e n, ?_, ?_⟩
  · exact incidenceOfNonmultiple_leg p hp hpodd n
  · intro x hx
    have hinv : e.symm x = n := by
      apply Subtype.ext
      change x.1.1 + x.1.2.1 = n.1
      exact hx
    calc
      x = e (e.symm x) := (e.apply_symm_apply x).symm
      _ = e n := congrArg e hinv

end

end NativeCarryGeometry.Internal.Carry.Cp

namespace NativeCarryGeometry.Arithmetic.Balanced

abbrev halfRange (b : ℕ) : ℕ :=
  Internal.Genuine.Cp.halfRange b

noncomputable abbrev balancedOffsets (b : ℕ) : Finset ℤ :=
  Internal.Genuine.Cp.balancedOffsets b

abbrev BalancedOffset (b : ℕ) :=
  Internal.Carry.Cp.BalancedOffset b

abbrev NonzeroResidue (b : ℕ) :=
  Internal.Carry.Cp.NonzeroResidue b

abbrev Nonmultiple (b : ℕ) :=
  Internal.Carry.Cp.Nonmultiple b

abbrev Incidence (b : ℕ) :=
  Internal.Carry.Cp.Incidence b

/-- NCG-BAL-001: Balanced Camera Cardinality. -/
theorem card_balancedOffsets {b : ℕ} (hbodd : Odd b) :
    (balancedOffsets b).card = b - 1 :=
  Internal.Carry.Cp.card_balancedOffsets hbodd

/-- NCG-BAL-002: Balanced Residue Representation. -/
noncomputable abbrev balancedOffset_equiv_nonzeroResidue
    (b : ℕ) (hb : Nat.Prime b) (hbodd : Odd b) :
    BalancedOffset b ≃ NonzeroResidue b :=
  Internal.Carry.Cp.balancedOffsetEquivNonzeroResidue b hb hbodd

/-- NCG-BAL-003: Canonical Center-Offset Decomposition. -/
theorem centerOffsetDecomposition_existsUnique
    (b : ℕ) (hb : Nat.Prime b) (hbodd : Odd b)
    (n : Nonmultiple b) :
    ∃! x : Incidence b, x.1.1 + x.1.2.1 = n.1 :=
  Internal.Carry.Cp.existsUnique_incidence b hb hbodd n

end NativeCarryGeometry.Arithmetic.Balanced
