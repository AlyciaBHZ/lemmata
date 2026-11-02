module

/- Adapted from the pinned OpenAI/selanavot field-generic sources.
Namespace, imports, and selected scope changed; see Matrix/NOTICE.md.
Apache-2.0 license retained in Matrix/Apache-2.0.txt. -/

public import Lemmata.FockCircuits.Matrix.Foundation.DotPairing

public section

set_option autoImplicit false

@[expose] section

namespace Lemmata.FockCircuits.Matrix

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace Foundation
namespace Tensor

section DependentSum

variable {K S : Type*} [CommSemiring K] [DecidableEq S]
variable {X Y Z : S → Type*}

def dependentDirectSum (T : ∀ s, Tensor K (X s) (Y s) (Z s)) :
    Tensor K (Σ s, X s) (Σ s, Y s) (Σ s, Z s) :=
  fun x y z =>
    if hxy : y.1 = x.1 then
      if hxz : z.1 = x.1 then T x.1 x.2 (hxy ▸ y.2) (hxz ▸ z.2)
      else 0
    else 0

@[simp] theorem dependentDirectSum_matching
    (T : ∀ s, Tensor K (X s) (Y s) (Z s))
    (s : S) (x : X s) (y : Y s) (z : Z s) :
    dependentDirectSum T ⟨s, x⟩ ⟨s, y⟩ ⟨s, z⟩ = T s x y z := by
  simp [dependentDirectSum]

theorem dependentDirectSum_zero_of_left_ne
    (T : ∀ s, Tensor K (X s) (Y s) (Z s))
    (x : Σ s, X s) (y : Σ s, Y s) (z : Σ s, Z s)
    (h : x.1 ≠ y.1) : dependentDirectSum T x y z = 0 := by
  simp [dependentDirectSum, Ne.symm h]

def directSumCoordinateEquiv {A : Type*} (e : ∀ s, X s ≃ A) :
    (Σ s, X s) ≃ S × A where
  toFun x := (x.1, e x.1 x.2)
  invFun x := ⟨x.1, (e x.1).symm x.2⟩
  left_inv := by
    rintro ⟨s, x⟩
    simp
  right_inv := by
    rintro ⟨s, x⟩
    simp

theorem dependentDirectSum_reindex {A B C : Type*}
    (T : ∀ s, Tensor K (X s) (Y s) (Z s))
    (ex : ∀ s, X s ≃ A) (ey : ∀ s, Y s ≃ B) (ez : ∀ s, Z s ≃ C) :
    pullback (directSumCoordinateEquiv ex).symm
      (directSumCoordinateEquiv ey).symm (directSumCoordinateEquiv ez).symm
      (dependentDirectSum T) =
      directSum (fun s => pullback (ex s).symm (ey s).symm (ez s).symm (T s)) := by
  funext x y z
  rcases x with ⟨s, x⟩
  rcases y with ⟨t, y⟩
  rcases z with ⟨v, z⟩
  by_cases ht : t = s
  · subst t
    by_cases hv : v = s
    · subst v
      simp [pullback, directSumCoordinateEquiv, dependentDirectSum, directSum]
    · simp [pullback, directSumCoordinateEquiv, dependentDirectSum, directSum,
        hv, Ne.symm hv]
  · simp [pullback, directSumCoordinateEquiv, dependentDirectSum, directSum,
      ht, Ne.symm ht]

end DependentSum
end Tensor

end Foundation

end Lemmata.FockCircuits.Matrix
