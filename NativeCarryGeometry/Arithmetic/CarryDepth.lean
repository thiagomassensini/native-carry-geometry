import NativeCarryGeometry.Arithmetic.BalancedResidue
import Mathlib.NumberTheory.Padics.PadicVal.Basic


/-!
# Profundidade efetiva do carry Cₚ

Fixe um primo impar `p` e uma perna `n` que nao pertence a vertical de base
`p`. Cada offset balanceado `a` tenta produzir o centro candidato `n - a`.
A profundidade dessa tentativa e a valoracao `p`-adica de `n - a`, e a
profundidade efetiva da carta e o supremo finito sobre todos os offsets.

Este arquivo prova duas afirmacoes separadas:

1. somente o offset canonico da bijecao global produz um multiplo de `p`;
2. portanto, o supremo das profundidades de todas as pernas e exatamente a
   profundidade do centro canonico.

A definicao de `effectiveDepth` nao menciona o offset canonico nem o centro;
assim, a igualdade final e um teorema e nao uma calibracao circular.

Por convencao da `padicValInt` da Mathlib, a valoracao de `0` vale `0`. A
igualdade principal continua correta nesse caso degenerado. O teorema
`one_le_centerDepth` registra separadamente a profundidade positiva quando o
centro canonico e nao nulo.
-/

namespace NativeCarryGeometry.Internal.Carry.Cp

open NativeCarryGeometry.Internal.Genuine.Cp

noncomputable section

/-- Profundidade produzida por um offset candidato da carta `Cₚ`. -/
def offsetDepth (p : ℕ) (n a : ℤ) : ℕ :=
  padicValInt p (n - a)

/--
Profundidade efetiva vista pela carta: o maior carry entre todos os offsets
balanceados. Esta definicao e independente da escolha canonica da bijecao.
-/
def effectiveDepth (p : ℕ) (n : ℤ) : ℕ :=
  (balancedOffsets p).sup fun a => offsetDepth p n a

/-- Profundidade `p`-adica do centro escolhido pela bijecao global. -/
def centerDepth
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) : ℕ :=
  padicValInt p (centerOfNonmultiple p hp hpodd n)

/--
Um offset balanceado produz um multiplo de `p` se, e somente se, ele e o
offset canonico da perna. Esta e a forma aritmetica de "uma unica perna da
carta carrega".
-/
theorem dvd_sub_iff_eq_offset
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) (a : BalancedOffset p) :
    (p : ℤ) ∣ (n.1 - a.1) ↔
      a = offsetOfNonmultiple p hp hpodd n := by
  constructor
  · intro hdiv
    have hzero : ((n.1 - a.1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (n.1 - a.1) p).mpr hdiv
    have hcast : (a.1 : ZMod p) = (n.1 : ZMod p) := by
      have hsub : (n.1 : ZMod p) - (a.1 : ZMod p) = 0 := by
        simpa using hzero
      exact (sub_eq_zero.mp hsub).symm
    apply Subtype.ext
    calc
      a.1 = (a.1 : ZMod p).valMinAbs :=
        (valMinAbs_intCast_of_mem hp hpodd a.2).symm
      _ = (n.1 : ZMod p).valMinAbs :=
        congrArg (fun x : ZMod p => x.valMinAbs) hcast
      _ = ((offsetOfNonmultiple p hp hpodd n).1 : ZMod p).valMinAbs :=
        congrArg (fun x : ZMod p => x.valMinAbs)
          (cast_offsetOfNonmultiple p hp hpodd n).symm
      _ = (offsetOfNonmultiple p hp hpodd n).1 :=
        valMinAbs_intCast_of_mem hp hpodd
          (offsetOfNonmultiple p hp hpodd n).2
  · intro ha
    rw [ha]
    simpa [centerOfNonmultiple] using
      dvd_centerOfNonmultiple p hp hpodd n

/-- Todo offset nao canonico possui profundidade de carry igual a zero. -/
theorem offsetDepth_eq_zero_of_ne_offset
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) (a : BalancedOffset p)
    (ha : a ≠ offsetOfNonmultiple p hp hpodd n) :
    offsetDepth p n.1 a.1 = 0 := by
  apply padicValInt.eq_zero_of_not_dvd
  intro hdiv
  exact ha ((dvd_sub_iff_eq_offset p hp hpodd n a).mp hdiv)

/-- A profundidade do offset canonico e literalmente a do centro canonico. -/
theorem offsetDepth_canonical
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) :
    offsetDepth p n.1 (offsetOfNonmultiple p hp hpodd n).1 =
      centerDepth p hp hpodd n := by
  rfl

/--
Ponte peso--carry Cₚ: a maior profundidade entre todas as pernas balanceadas
e exatamente a profundidade `p`-adica do centro unico da bijecao global.
-/
theorem effectiveDepth_eq_centerDepth
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p) :
    effectiveDepth p n.1 = centerDepth p hp hpodd n := by
  apply Nat.le_antisymm
  · unfold effectiveDepth
    apply Finset.sup_le
    intro a ha
    let candidate : BalancedOffset p := ⟨a, ha⟩
    by_cases hcanonical :
        candidate = offsetOfNonmultiple p hp hpodd n
    · have haeq :
          a = (offsetOfNonmultiple p hp hpodd n).1 :=
        congrArg Subtype.val hcanonical
      simp [offsetDepth, centerDepth, centerOfNonmultiple, haeq]
    · have hzero : offsetDepth p n.1 a = 0 := by
        change offsetDepth p n.1 candidate.1 = 0
        exact offsetDepth_eq_zero_of_ne_offset
          p hp hpodd n candidate hcanonical
      rw [hzero]
      exact Nat.zero_le _
  · unfold effectiveDepth
    change
      offsetDepth p n.1 (offsetOfNonmultiple p hp hpodd n).1 ≤
        (balancedOffsets p).sup (fun a => offsetDepth p n.1 a)
    exact Finset.le_sup (offsetOfNonmultiple p hp hpodd n).2

/-- No caso degenerado `centro = 0`, a convencao finita da Mathlib da zero. -/
theorem centerDepth_eq_zero_of_center_eq_zero
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p)
    (hzero : centerOfNonmultiple p hp hpodd n = 0) :
    centerDepth p hp hpodd n = 0 := by
  simp [centerDepth, hzero]

/-- Um centro canonico nao nulo tem ao menos uma camada de carry em base `p`. -/
theorem one_le_centerDepth
    (p : ℕ) (hp : Nat.Prime p) (hpodd : Odd p)
    (n : Nonmultiple p)
    (hnonzero : centerOfNonmultiple p hp hpodd n ≠ 0) :
    1 ≤ centerDepth p hp hpodd n := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpow :
      ((p : ℤ) ^ (1 : ℕ)) ∣ centerOfNonmultiple p hp hpodd n := by
    simpa using dvd_centerOfNonmultiple p hp hpodd n
  have hcases :=
    (padicValInt_dvd_iff (p := p) 1
      (centerOfNonmultiple p hp hpodd n)).mp hpow
  exact hcases.resolve_left hnonzero

end

end NativeCarryGeometry.Internal.Carry.Cp

namespace NativeCarryGeometry.Arithmetic.Balanced

noncomputable abbrev canonicalOffset
    (b : ℕ) (hb : Nat.Prime b) (hbodd : Odd b)
    (n : Nonmultiple b) : BalancedOffset b :=
  Internal.Carry.Cp.offsetOfNonmultiple b hb hbodd n

noncomputable abbrev effectiveDepth (b : ℕ) (n : ℤ) : ℕ :=
  Internal.Carry.Cp.effectiveDepth b n

noncomputable abbrev centerDepth
    (b : ℕ) (hb : Nat.Prime b) (hbodd : Odd b)
    (n : Nonmultiple b) : ℕ :=
  Internal.Carry.Cp.centerDepth b hb hbodd n

/-- NCG-DEP-001: Unique Carrying Offset. -/
theorem offsetCarries_iff_eq_canonicalOffset
    (b : ℕ) (hb : Nat.Prime b) (hbodd : Odd b)
    (n : Nonmultiple b) (a : BalancedOffset b) :
    (b : ℤ) ∣ (n.1 - a.1) ↔
      a = canonicalOffset b hb hbodd n :=
  Internal.Carry.Cp.dvd_sub_iff_eq_offset b hb hbodd n a

/-- NCG-DEP-002: Carry-Depth Identification. -/
theorem effectiveDepth_eq_centerDepth
    (b : ℕ) (hb : Nat.Prime b) (hbodd : Odd b)
    (n : Nonmultiple b) :
    effectiveDepth b n.1 = centerDepth b hb hbodd n :=
  Internal.Carry.Cp.effectiveDepth_eq_centerDepth b hb hbodd n

end NativeCarryGeometry.Arithmetic.Balanced
