import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic


/-!
# Bijeção local de carry C2

Este arquivo contem apenas aritmetica finita: cada perna impar determina um
centro multiplo de quatro e uma incidencia perna--centro. Nenhum operador ou
predicado de zero e definido aqui.

Todo impar `n >= 3` possui exatamente um vizinho multiplo de quatro. Esse
vizinho e o centro C2 cuja perna e `n`. Esta e a camada combinatoria que liga o
canal direto, indexado por impares, ao canal bracketado, indexado por centros.
-/

namespace NativeCarryGeometry.Internal.Carry.C2

/-- O vizinho de um impar que ocupa a vertical C2 de profundidade pelo menos 2. -/
def adjacentCenter (n : ℕ) : ℕ :=
  if n % 4 = 1 then n - 1 else n + 1

theorem odd_mod_four {n : ℕ} (hn : Odd n) :
    n % 4 = 1 ∨ n % 4 = 3 :=
  Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn)

@[simp] theorem adjacentCenter_of_mod_one {n : ℕ} (h : n % 4 = 1) :
    adjacentCenter n = n - 1 := by
  simp [adjacentCenter, h]

@[simp] theorem adjacentCenter_of_mod_three {n : ℕ} (h : n % 4 = 3) :
    adjacentCenter n = n + 1 := by
  simp [adjacentCenter, h]

/-- O centro escolhido e sempre multiplo de quatro. -/
theorem four_dvd_adjacentCenter {n : ℕ} (hn : Odd n) :
    4 ∣ adjacentCenter n := by
  rw [Nat.dvd_iff_mod_eq_zero]
  rcases odd_mod_four hn with h | h
  · rw [adjacentCenter_of_mod_one h]
    omega
  · rw [adjacentCenter_of_mod_three h]
    omega

/-- Para as pernas binarias C2, o centro escolhido comeca em `4`. -/
theorem four_le_adjacentCenter {n : ℕ} (hn3 : 3 ≤ n) (hn : Odd n) :
    4 ≤ adjacentCenter n := by
  rcases odd_mod_four hn with h | h
  · rw [adjacentCenter_of_mod_one h]
    omega
  · rw [adjacentCenter_of_mod_three h]
    omega

/-- O impar original e literalmente uma das duas pernas do centro escolhido. -/
theorem leg_of_adjacentCenter {n : ℕ} (hn3 : 3 ≤ n) (hn : Odd n) :
    n = adjacentCenter n - 1 ∨ n = adjacentCenter n + 1 := by
  rcases odd_mod_four hn with h | h
  · right
    rw [adjacentCenter_of_mod_one h]
    omega
  · left
    rw [adjacentCenter_of_mod_three h]
    omega

/--
Unicidade do centro: qualquer multiplo de quatro que tenha `n` como perna e o
centro construido por `adjacentCenter`.
-/
theorem adjacentCenter_unique {n c : ℕ}
    (hn3 : 3 ≤ n) (hc : 4 ∣ c)
    (hleg : n = c - 1 ∨ n = c + 1) :
    adjacentCenter n = c := by
  have hcmod : c % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp hc
  unfold adjacentCenter
  split_ifs with h
  · rcases hleg with hleg | hleg <;> omega
  · rcases hleg with hleg | hleg <;> omega

/-- Dominio das pernas C2: impares a partir de `3`. -/
def OddLeg := {n : ℕ // 3 ≤ n ∧ Odd n}

/--
Uma incidencia C2 guarda um centro multiplo de quatro e uma de suas duas
pernas. A perna faz parte do dado: centros sozinhos nao estao em bijecao com
as pernas, pois cada centro possui duas delas.
-/
def Incidence :=
  {x : ℕ × ℕ //
    4 ≤ x.1 ∧ 4 ∣ x.1 ∧ (x.2 = x.1 - 1 ∨ x.2 = x.1 + 1)}

/-- A incidencia determinada por uma perna impar. -/
def incidenceOfOddLeg (n : OddLeg) : Incidence :=
  ⟨(adjacentCenter n.1, n.1),
    four_le_adjacentCenter n.2.1 n.2.2,
    four_dvd_adjacentCenter n.2.2,
    leg_of_adjacentCenter n.2.1 n.2.2⟩

/-- A perna guardada por uma incidencia C2 e impar e pelo menos `3`. -/
def oddLegOfIncidence (x : Incidence) : OddLeg := by
  refine ⟨x.1.2, ?_, ?_⟩
  · have hc4 : 4 ≤ x.1.1 := x.2.1
    rcases x.2.2.2 with h | h <;> omega
  · have htwoFour : 2 ∣ (4 : ℕ) := by norm_num
    have hc4 : 4 ≤ x.1.1 := x.2.1
    have hcTwo : 2 ∣ x.1.1 := htwoFour.trans x.2.2.1
    have hcEven : Even x.1.1 := even_iff_two_dvd.mpr hcTwo
    rcases x.2.2.2 with h | h
    · rw [h]
      exact Nat.Even.sub_odd (by omega) hcEven odd_one
    · rw [h]
      exact hcEven.add_one

/--
Bijeção combinatoria exata da ponte C2: cada perna impar `n >= 3` corresponde
a uma unica incidencia `(centro multiplo de 4, n)`, e reciprocamente.
-/
def oddLegEquivIncidence : OddLeg ≃ Incidence where
  toFun := incidenceOfOddLeg
  invFun := oddLegOfIncidence
  left_inv n := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · change adjacentCenter x.1.2 = x.1.1
      exact adjacentCenter_unique
        (oddLegOfIncidence x).2.1 x.2.2.1 x.2.2.2
    · rfl

end NativeCarryGeometry.Internal.Carry.C2

/-!
# Profundidade efetiva do carry C2

Este arquivo liga a definicao do documento

`k_eff(n) = max (v_2(n-1)) (v_2(n+1))`

ao centro combinatorio definido por `adjacentCenter` (publicamente `binaryCenter`). Para um impar `n >= 3`, um
dos vizinhos e congruente a `2 mod 4` e tem profundidade exatamente `1`; o
outro e o centro multiplo de quatro e tem profundidade pelo menos `2`.
-/

namespace NativeCarryGeometry.Internal.Carry.C2

/-- Profundidade efetiva apresentada pelo canal direto C2. -/
def effectiveDepth (n : ℕ) : ℕ :=
  max (padicValNat 2 (n - 1)) (padicValNat 2 (n + 1))

/-- Um natural congruente a `2 mod 4` possui profundidade 2-adica exatamente `1`. -/
theorem padicValNat_two_eq_one_of_mod_four_two {m : ℕ} (hm : m % 4 = 2) :
    padicValNat 2 m = 1 := by
  have hm0 : m ≠ 0 := by omega
  have htwo : 2 ∣ m := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hfour : ¬4 ∣ m := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hlo : 1 ≤ padicValNat 2 m :=
    one_le_padicValNat_of_dvd hm0 htwo
  have hhi : ¬2 ≤ padicValNat 2 m := by
    intro hdepth
    have hpow : 2 ^ 2 ∣ m :=
      (padicValNat_dvd_iff_le (p := 2) hm0).2 hdepth
    norm_num at hpow
    exact hfour hpow
  omega

/-- O centro C2 escolhido possui profundidade 2-adica pelo menos `2`. -/
theorem two_le_centerDepth {n : ℕ} (hn3 : 3 ≤ n) (hn : Odd n) :
    2 ≤ padicValNat 2 (adjacentCenter n) := by
  have hc4 := four_le_adjacentCenter hn3 hn
  have hc0 : adjacentCenter n ≠ 0 := by omega
  apply (padicValNat_dvd_iff_le (p := 2) hc0).1
  norm_num
  exact four_dvd_adjacentCenter hn

/--
Identificacao aritmetica carry--profundidade C2: a profundidade efetiva da perna e exatamente a
profundidade 2-adica do seu centro unico.
-/
theorem effectiveDepth_eq_centerDepth {n : ℕ} (hn3 : 3 ≤ n) (hn : Odd n) :
    effectiveDepth n = padicValNat 2 (adjacentCenter n) := by
  have hcenter := two_le_centerDepth hn3 hn
  rcases odd_mod_four hn with h | h
  · have hotherMod : (n + 1) % 4 = 2 := by omega
    have hother := padicValNat_two_eq_one_of_mod_four_two hotherMod
    rw [adjacentCenter_of_mod_one h] at hcenter
    rw [effectiveDepth, adjacentCenter_of_mod_one h]
    rw [hother, max_eq_left (by omega)]
  · have hotherMod : (n - 1) % 4 = 2 := by omega
    have hother := padicValNat_two_eq_one_of_mod_four_two hotherMod
    rw [adjacentCenter_of_mod_three h] at hcenter
    rw [effectiveDepth, adjacentCenter_of_mod_three h]
    rw [hother, max_eq_right (by omega)]

end NativeCarryGeometry.Internal.Carry.C2

namespace NativeCarryGeometry.Arithmetic.Binary

abbrev binaryCenter (n : ℕ) : ℕ :=
  Internal.Carry.C2.adjacentCenter n

abbrev OddLeg := Internal.Carry.C2.OddLeg
abbrev BinaryIncidence := Internal.Carry.C2.Incidence

/-- NCG-BIN-001: Binary Center Divisibility. -/
theorem four_dvd_binaryCenter {n : ℕ} (hn : Odd n) :
    4 ∣ binaryCenter n :=
  Internal.Carry.C2.four_dvd_adjacentCenter hn

/-- NCG-BIN-002: Binary Adjacent-Center Uniqueness. -/
theorem binaryCenter_unique {n c : ℕ}
    (hn3 : 3 ≤ n) (hc : 4 ∣ c)
    (hleg : n = c - 1 ∨ n = c + 1) :
    binaryCenter n = c :=
  Internal.Carry.C2.adjacentCenter_unique hn3 hc hleg

/-- NCG-BIN-003: Binary Leg-Incidence Bijection. -/
noncomputable abbrev oddLeg_equiv_binaryIncidence :
    OddLeg ≃ BinaryIncidence :=
  Internal.Carry.C2.oddLegEquivIncidence

abbrev binaryEffectiveDepth (n : ℕ) : ℕ :=
  Internal.Carry.C2.effectiveDepth n

/-- NCG-BIN-004: Binary Carry-Depth Identification. -/
theorem binaryEffectiveDepth_eq_centerDepth
    {n : ℕ} (hn3 : 3 ≤ n) (hn : Odd n) :
    binaryEffectiveDepth n =
      padicValNat 2 (binaryCenter n) :=
  Internal.Carry.C2.effectiveDepth_eq_centerDepth hn3 hn

end NativeCarryGeometry.Arithmetic.Binary
