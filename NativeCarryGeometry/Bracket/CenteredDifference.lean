import Mathlib.Tactic


/-!
# Pares simetricos em torno de um centro

Esta e a unidade combinatoria anterior ao bracket: duas pernas `c-r` e `c+r`
compartilham o mesmo centro.
-/

namespace NativeCarryGeometry.Internal

structure SymmetricPair where
  center : ℤ
  radius : ℤ
  deriving Repr, DecidableEq

namespace SymmetricPair

def left (pair : SymmetricPair) : ℤ :=
  pair.center - pair.radius

def right (pair : SymmetricPair) : ℤ :=
  pair.center + pair.radius

def reflected (pair : SymmetricPair) : SymmetricPair :=
  ⟨pair.center, -pair.radius⟩

@[simp] theorem left_add_right (pair : SymmetricPair) :
    pair.left + pair.right = 2 * pair.center := by
  simp [left, right]
  ring

@[simp] theorem reflected_left (pair : SymmetricPair) :
    pair.reflected.left = pair.right := by
  simp [reflected, left, right]

@[simp] theorem reflected_right (pair : SymmetricPair) :
    pair.reflected.right = pair.left := by
  simp [reflected, left, right, sub_eq_add_neg]

end SymmetricPair
end NativeCarryGeometry.Internal

/-!
# Bracket finito abstrato

Antes de introduzir `n^{-s}`, formalizamos a identidade puramente aditiva da
segunda diferenca. Isso separa cancelamento combinatorio de analise complexa.
-/

open scoped BigOperators

namespace NativeCarryGeometry.Internal

variable {A : Type*} [AddCommGroup A]

/-- Segunda diferenca centrada com centro e raio inteiros. -/
def centeredSecondDifference (f : ℤ → A) (center radius : ℤ) : A :=
  f (center - radius) - (2 • f center) + f (center + radius)

@[simp] theorem centeredSecondDifference_zero (center radius : ℤ) :
    centeredSecondDifference (fun _ : ℤ ↦ (0 : A)) center radius = 0 := by
  simp [centeredSecondDifference]

theorem centeredSecondDifference_neg_radius
    (f : ℤ → A) (center radius : ℤ) :
    centeredSecondDifference f center (-radius) =
      centeredSecondDifference f center radius := by
  simp [centeredSecondDifference, sub_eq_add_neg, add_comm, add_left_comm]

theorem centeredSecondDifference_add
    (f g : ℤ → A) (center radius : ℤ) :
    centeredSecondDifference (fun n ↦ f n + g n) center radius =
      centeredSecondDifference f center radius +
        centeredSecondDifference g center radius := by
  simp only [centeredSecondDifference, nsmul_add]
  abel

/-- Soma das segundas diferencas para raios `1, ..., h`. -/
def saturatedBracket (h : ℕ) (f : ℤ → A) (center : ℤ) : A :=
  ∑ radius ∈ Finset.Icc 1 h,
    centeredSecondDifference f center (radius : ℤ)

@[simp] theorem saturatedBracket_zero (h : ℕ) (center : ℤ) :
    saturatedBracket h (fun _ : ℤ ↦ (0 : A)) center = 0 := by
  simp [saturatedBracket]

theorem saturatedBracket_add
    (h : ℕ) (f g : ℤ → A) (center : ℤ) :
    saturatedBracket h (fun n ↦ f n + g n) center =
      saturatedBracket h f center + saturatedBracket h g center := by
  simp only [saturatedBracket, centeredSecondDifference_add]
  exact Finset.sum_add_distrib

end NativeCarryGeometry.Internal

namespace NativeCarryGeometry.Bracket

abbrev centeredSecondDifference
    {A : Type*} [AddCommGroup A]
    (f : ℤ → A) (center radius : ℤ) : A :=
  Internal.centeredSecondDifference f center radius

abbrev saturatedBracket
    {A : Type*} [AddCommGroup A]
    (halfWidth : ℕ) (f : ℤ → A) (center : ℤ) : A :=
  Internal.saturatedBracket halfWidth f center

/-- NCG-BRK-001: Radius Symmetry. -/
theorem centeredSecondDifference_neg_radius
    {A : Type*} [AddCommGroup A]
    (f : ℤ → A) (center radius : ℤ) :
    centeredSecondDifference f center (-radius) =
      centeredSecondDifference f center radius :=
  Internal.centeredSecondDifference_neg_radius f center radius

/-- NCG-BRK-002: Bracket Additivity. -/
theorem centeredSecondDifference_add
    {A : Type*} [AddCommGroup A]
    (f g : ℤ → A) (center radius : ℤ) :
    centeredSecondDifference (fun n => f n + g n) center radius =
      centeredSecondDifference f center radius +
        centeredSecondDifference g center radius :=
  Internal.centeredSecondDifference_add f g center radius

end NativeCarryGeometry.Bracket
