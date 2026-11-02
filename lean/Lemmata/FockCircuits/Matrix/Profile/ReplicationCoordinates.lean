module

public import Lemmata.FockCircuits.Matrix.Profile.ReplicationBasis

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Profile.Replication

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

def blockCoefficient (P : K[X]) (hP : P.Monic) (n : ℕ) : K[X] →ₗ[K] K where
  toFun p := (blockBasis P hP).repr p n
  map_add' p q := by simp
  map_smul' c p := by simp

@[simp] theorem blockCoefficient_basis (P : K[X]) (hP : P.Monic) (n m : ℕ) :
    blockCoefficient P hP n (blockPolynomial P m) = if m = n then 1 else 0 := by
  change (blockBasis P hP).repr (blockPolynomial P m) n = _
  rw [← blockBasis_apply P hP m]
  exact (blockBasis P hP).repr_self_apply m n

theorem blockCoefficient_product_two_blocks (P u v : K[X]) (hP : P.Monic) (a b n : ℕ) :
    blockCoefficient P hP n ((u * P ^ a) * (v * P ^ b)) =
      blockCoefficient P hP n ((u * v %ₘ P) * P ^ (a + b)) +
        blockCoefficient P hP n ((u * v /ₘ P) * P ^ (a + b + 1)) := by
  rw [product_two_blocks, map_add]

end

end Lemmata.FockCircuits.Matrix.Profile.Replication
