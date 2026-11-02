module

/- Adapted from the pinned OpenAI/selanavot field-generic sources. See Matrix/NOTICE.md. -/

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
Namespace and imports adapted for FockCircuits; see Matrix/NOTICE.md. Apache-2.0 retained in Matrix/Apache-2.0.txt.
-/

public import Lemmata.FockCircuits.Matrix.Character.Dot

public section

set_option autoImplicit false

@[expose] section

namespace Lemmata.FockCircuits.Matrix

/-!
# The six permuted tensor characters

Precomposing a character with a leg permutation gives another character. The
six resulting values multiply to the symmetrized product, and each singleton
leg exponent occurs twice among their first-leg exponents.
-/

noncomputable section

open Foundation
open scoped BigOperators

namespace Spectral.Character

variable {K : Type*} [Field K]

variable (χ : (Character K))

/-- The reflected character exchanges the second and third tensor legs. -/
def swap23Character : (Character K) where
  value T := χ.value (fun x z y => T x y z)
  nonneg T := χ.nonneg (fun x z y => T x y z)
  map_zero := χ.map_zero
  map_one := χ.map_one
  map_directSum T := by
    have heq : (fun x z y => Tensor.directSum T x y z) =
        Tensor.directSum (fun i x z y => T i x y z) := by
      funext x z y
      simp only [Tensor.directSum, and_comm]
    change χ.value (fun x z y => Tensor.directSum T x y z) = _
    rw [heq, χ.map_directSum]
  map_product T S := χ.map_product (fun x z y => T x y z) (fun x z y => S x y z)
  monotone T A B C := by
    have heq : (fun x z y => Tensor.restrict A B C T x y z) =
        Tensor.restrict A C B (fun x z y => T x y z) := by
      funext x z y
      simp only [Tensor.restrict]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro j hj
      ring
    change χ.value (fun x z y => Tensor.restrict A B C T x y z) ≤ _
    rw [heq]
    exact χ.monotone (fun x z y => T x y z) A C B

@[simp] theorem swap23Character_value {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor K X Y Z) :
    χ.swap23Character.value T = χ.value (fun x z y => T x y z) := rfl

@[simp] theorem cyclicCharacter_pX : χ.cyclicCharacter.pX = χ.pZ := by
  rfl

@[simp] theorem cyclicCharacter_pY : χ.cyclicCharacter.pY = χ.pX := rfl

@[simp] theorem cyclicCharacter_pZ : χ.cyclicCharacter.pZ = χ.pY := rfl

@[simp] theorem swap23Character_pX : χ.swap23Character.pX = χ.pX := by
  unfold pX pZ
  simp only [cyclicCharacter_value, swap23Character_value]
  congr 2
  apply congrArg χ.value
  funext x y z
  simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]

@[simp] theorem swap23Character_pY : χ.swap23Character.pY = χ.pZ := by
  unfold pY pZ
  simp only [cyclicCharacter_value, swap23Character_value]
  congr 2
  apply congrArg χ.value
  funext x y z
  simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]

@[simp] theorem swap23Character_pZ : χ.swap23Character.pZ = χ.pY := by
  unfold pY pZ
  simp only [cyclicCharacter_value, swap23Character_value]
  congr 2
  apply congrArg χ.value
  funext x y z
  simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]

end Spectral.Character

end

end Lemmata.FockCircuits.Matrix
