module

public import Lemmata.FockCircuits.MarkedIdentity

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.FiniteIdentity

variable (R : Type*) [CommRing R]

noncomputable def matrixEntry (L : ℕ) (I J : Index L) : Matrix (Index L) (Index L) R →ₗ[R] R where
  toFun M := M I J
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def signedEntry (L W : ℕ) (B I J : Index L) : State R L →ₗ[R] R :=
  ∑ k : Fin W, (matrixEntry R L I J).comp
    (((LinearMap.mulLeft R (diagonal R L (-shift W k) (Pi.single B 1))) -
        (sigma W : R) • LinearMap.mulRight R (diagonal R L (-shift W k) (Pi.single B 1))).comp
      ((diagonalLinear R L (shift W k)).comp (mark R L W k)))

theorem signedEntry_apply (L W : ℕ) (B I J : Index L) (v : State R L) :
    signedEntry R L W B I J v =
      ∑ k : Fin W,
        ((diagonal R L (-shift W k) (Pi.single B 1) *
            diagonal R L (shift W k) (mark R L W k v)) I J -
          (sigma W : R) *
            (diagonal R L (shift W k) (mark R L W k v) *
              diagonal R L (-shift W k) (Pi.single B 1)) I J) := by
  unfold signedEntry
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rfl

theorem state_signed_identity (L W : ℕ) (v : State R L) (B I J : Index L)
    (hW : 0 < W) (hB : doubledEnergy B.val = W)
    (hv : ∀ A, v A ≠ 0 → doubledEnergy A.val ≤ W ∧ doubledEnergy A.val % 2 = W % 2)
    (hcut : doubledEnergy J.val + W ≤ 2 * L) :
    (∑ k : Fin W,
      ((diagonal R L (-shift W k) (Pi.single B 1) *
          diagonal R L (shift W k) (mark R L W k v)) I J -
        (sigma W : R) *
          (diagonal R L (shift W k) (mark R L W k v) *
            diagonal R L (-shift W k) (Pi.single B 1)) I J)) =
      (if I = J then (1 : R) else 0) * matrix R L v ⟨∅, by simp⟩ B := by
  classical
  let rhsEntry : State R L →ₗ[R] R :=
    (LinearMap.mulLeft R (if I = J then (1 : R) else 0)).comp
      ((matrixEntry R L ⟨∅, by simp⟩ B).comp (matrixLinear R L))
  rw [← signedEntry_apply]
  change signedEntry R L W B I J v = rhsEntry v
  conv_lhs => rw [state_eq_sum_single R L v]
  conv_rhs => rw [state_eq_sum_single R L v]
  simp only [map_sum, map_smul, RingHom.id_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hzero : v A = 0
  · simp only [hzero, zero_mul]
  · have hsource := hv A hzero
    have he : signedEntry R L W B I J (Pi.single A 1) = rhsEntry (Pi.single A 1) := by
      rw [signedEntry_apply]
      exact singleton_signed_identity R L W A B I J hW hB hsource.1 hsource.2 hcut
    rw [he]

end Lemmata.FockCircuits.FiniteIdentity
