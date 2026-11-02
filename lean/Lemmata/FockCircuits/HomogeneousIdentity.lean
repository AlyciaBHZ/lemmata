module

public import Lemmata.FockCircuits.StateIdentity

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lemmata.FockCircuits.FiniteIdentity

variable (R : Type*) [CommRing R]

/-- The vacuum coefficient after applying the kernel matrix to the second state. -/
noncomputable def vacuumPairing (L : ℕ) (ξ η : State R L) : R :=
  ∑ B, matrix R L ξ ⟨∅, by simp⟩ B * η B

theorem homogeneous_signed_identity (L E W : ℕ) (ξ η : State R L)
    (hW : 0 < W)
    (hξ : ∀ A, ξ A ≠ 0 → doubledEnergy A.val ≤ W ∧
      doubledEnergy A.val % 2 = W % 2)
    (hη : ∀ B, η B ≠ 0 → doubledEnergy B.val = W)
    (hcut : 2 * E + W ≤ 2 * L) (I J : Index L)
    (hJ : doubledEnergy J.val ≤ 2 * E) :
    (∑ k : Fin W,
      ((diagonal R L (-shift W k) η *
          diagonal R L (shift W k) (mark R L W k ξ)) I J -
        (sigma W : R) *
          (diagonal R L (shift W k) (mark R L W k ξ) *
            diagonal R L (-shift W k) η) I J)) =
      (if I = J then (1 : R) else 0) * vacuumPairing R L ξ η := by
  classical
  have hηsum (k : Fin W) :
      diagonal R L (-shift W k) η =
        ∑ B, η B • diagonal R L (-shift W k) (Pi.single B (1 : R)) :=
    diagonal_eq_sum_single R L (-shift W k) η
  calc
    _ = ∑ k : Fin W, ∑ B : Index L, η B *
        (((diagonal R L (-shift W k) (Pi.single B 1) *
            diagonal R L (shift W k) (mark R L W k ξ)) I J) -
          (sigma W : R) *
            ((diagonal R L (shift W k) (mark R L W k ξ) *
              diagonal R L (-shift W k) (Pi.single B 1)) I J)) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [hηsum k, Finset.sum_mul, Finset.mul_sum, Matrix.sum_apply,
        smul_mul_assoc, mul_smul_comm, Matrix.smul_apply, smul_eq_mul]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro B hB
      ring
    _ = ∑ B : Index L, η B * (∑ k : Fin W,
        (((diagonal R L (-shift W k) (Pi.single B 1) *
            diagonal R L (shift W k) (mark R L W k ξ)) I J) -
          (sigma W : R) *
            ((diagonal R L (shift W k) (mark R L W k ξ) *
              diagonal R L (-shift W k) (Pi.single B 1)) I J))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      rw [Finset.mul_sum]
    _ = ∑ B : Index L, η B *
        ((if I = J then (1 : R) else 0) * matrix R L ξ ⟨∅, by simp⟩ B) := by
      apply Finset.sum_congr rfl
      intro B hB
      by_cases hzero : η B = 0
      · simp only [hzero, zero_mul]
      · rw [state_signed_identity R L W ξ B I J hW (hη B hzero) hξ (by omega)]
    _ = _ := by
      simp only [vacuumPairing, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B hB
      ring

end Lemmata.FockCircuits.FiniteIdentity
