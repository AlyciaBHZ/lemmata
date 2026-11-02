module

/- Adapted from the pinned OpenAI/selanavot field-generic sources.
See Matrix/NOTICE.md and Matrix/Apache-2.0.txt. -/

public import Lemmata.FockCircuits.Matrix.Foundation.DotPairing
public import Lemmata.FockCircuits.Matrix.Foundation.Symmetrization

public section

set_option autoImplicit false

@[expose] section

namespace Lemmata.FockCircuits.Matrix

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace Foundation
namespace Tensor

variable {K : Type*} [CommSemiring K]

def dotPairingMatrixX (U : Type*) : (Unit × U) ≃ U where
  toFun x := x.2
  invFun x := ((), x)
  left_inv := by rintro ⟨⟨⟩, x⟩; rfl
  right_inv x := rfl

def dotPairingMatrixY (U : Type*) : (U × Unit) ≃ U where
  toFun y := y.1
  invFun y := (y, ())
  left_inv := by rintro ⟨y, ⟨⟩⟩; rfl
  right_inv y := rfl

def dotPairingMatrixZ : (Unit × Unit) ≃ Unit where
  toFun _ := ()
  invFun _ := ((), ())
  left_inv := by rintro ⟨⟨⟩, ⟨⟩⟩; rfl
  right_inv := by rintro ⟨⟩; rfl

theorem dotPairing_matrixCoefficients (U : Type*) [DecidableEq U] :
    pullback (dotPairingMatrixX U) (dotPairingMatrixY U) dotPairingMatrixZ
      (dotPairing (K := K) U) = matrixCoefficients Unit U Unit := by
  funext x y z
  change (if x.2 = y.1 then (1 : K) else 0) =
    if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  have hguard : (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) ↔ x.2 = y.1 :=
    ⟨fun h => h.1, fun h => ⟨h, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  by_cases hxy : x.2 = y.1
  · calc
      (if x.2 = y.1 then (1 : K) else 0) = 1 := ite_eq_left hxy
      _ = (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0) :=
        (ite_eq_left (hguard.mpr hxy)).symm
  · have hfull : ¬ (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
      fun h => hxy (hguard.mp h)
    calc
      (if x.2 = y.1 then (1 : K) else 0) = 0 := ite_eq_right hxy
      _ = (if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0) :=
        (ite_eq_right hfull).symm

theorem matrixCoefficients_rank_of_dotPairing {U : Type*} [DecidableEq U] {r : ℕ}
    (h : RankAtMost (dotPairing (K := K) U) r) :
    RankAtMost (matrixCoefficients (K := K) Unit U Unit) r := by
  have h' := h.pullback (dotPairingMatrixX U) (dotPairingMatrixY U) dotPairingMatrixZ
  rw [dotPairing_matrixCoefficients] at h'
  exact h'


def pairingTriple (A B C : Type*) [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    Tensor K ((B × A) × Unit) ((B × Unit) × C) ((Unit × A) × C) :=
  product (product (dotPairing B) (cyclic (dotPairing A)))
    (cyclic (cyclic (dotPairing C)))

def pairingTripleMatrixX (A B : Type*) : (A × B) ≃ ((B × A) × Unit) where
  toFun x := ((x.2, x.1), ())
  invFun x := (x.1.2, x.1.1)
  left_inv x := rfl
  right_inv := by rintro ⟨⟨b, a⟩, ⟨⟩⟩; rfl

def pairingTripleMatrixY (B C : Type*) : (B × C) ≃ ((B × Unit) × C) where
  toFun y := ((y.1, ()), y.2)
  invFun y := (y.1.1, y.2)
  left_inv y := rfl
  right_inv := by rintro ⟨⟨b, ⟨⟩⟩, c⟩; rfl

def pairingTripleMatrixZ (C A : Type*) : (C × A) ≃ ((Unit × A) × C) where
  toFun z := (((), z.2), z.1)
  invFun z := (z.2, z.1.2)
  left_inv z := rfl
  right_inv := by rintro ⟨⟨⟨⟩, a⟩, c⟩; rfl

variable {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem pairingTriple_matrixCoefficients :
    pullback (pairingTripleMatrixX A B) (pairingTripleMatrixY B C)
      (pairingTripleMatrixZ C A) (pairingTriple (K := K) A B C) =
      matrixCoefficients A B C := by
  funext x y z
  change ((if x.2 = y.1 then (1 : K) else 0) *
    (if z.2 = x.1 then 1 else 0)) * (if y.2 = z.1 then 1 else 0) =
    if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0
  have hguard : ((x.2 = y.1 ∧ z.2 = x.1) ∧ y.2 = z.1) ↔
      (x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1) :=
    ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩
  simp only [ite_zero_mul_ite_zero, one_mul, hguard]

theorem matrixCoefficients_rank_of_pairingTriple {r : ℕ}
    (h : RankAtMost (pairingTriple (K := K) A B C) r) :
    RankAtMost (matrixCoefficients (K := K) A B C) r := by
  have h' := h.pullback (pairingTripleMatrixX A B) (pairingTripleMatrixY B C)
    (pairingTripleMatrixZ C A)
  rw [pairingTriple_matrixCoefficients] at h'
  exact h'


theorem matrixCoefficients_directSum_rank_of_pairingTriple
    {ι : Type*} [DecidableEq ι] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => pairingTriple (K := K) A B C)) r) :
    RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r := by
  have h' := h.directSum_pullback (pairingTripleMatrixX A B) (pairingTripleMatrixY B C)
    (pairingTripleMatrixZ C A)
  simpa only [pairingTriple_matrixCoefficients] using h'


end Tensor
end Foundation

end Lemmata.FockCircuits.Matrix
