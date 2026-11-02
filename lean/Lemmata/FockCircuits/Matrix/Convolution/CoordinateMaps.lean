module

public import Lemmata.FockCircuits.Matrix.Convolution.Basic
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Spectral

open Polynomial Foundation
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

theorem polynomial_eq_sum_fin (p : K[X]) {A : ℕ} (hp : p.natDegree < A) :
    p = ∑ i : Fin A, p.coeff i.val • X ^ i.val := by
  calc
    p = ∑ i ∈ Finset.range A, p.coeff i • X ^ i := by
      simpa only [smul_eq_C_mul] using p.as_sum_range_C_mul_X_pow' hp
    _ = _ := (Fin.sum_univ_eq_sum_range (fun i => p.coeff i • X ^ i) A).symm

theorem polynomial_product_eq_sum_fin (p q : K[X]) {A B : ℕ}
    (hp : p.natDegree < A) (hq : q.natDegree < B) :
    p * q = ∑ i : Fin A, ∑ j : Fin B,
      (p.coeff i.val * q.coeff j.val) • X ^ (i.val + j.val) := by
  calc
    p * q = (∑ i : Fin A, p.coeff i.val • X ^ i.val) *
        (∑ j : Fin B, q.coeff j.val • X ^ j.val) := by
      rw [← polynomial_eq_sum_fin p hp, ← polynomial_eq_sum_fin q hq]
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [smul_mul_smul_comm, ← pow_add]

theorem linearMap_product_eq_sum (p q : K[X]) {A B : ℕ}
    (hp : p.natDegree < A) (hq : q.natDegree < B) (φ : K[X] →ₗ[K] K) :
    φ (p * q) = ∑ i : Fin A, ∑ j : Fin B,
      p.coeff i.val * q.coeff j.val * φ (X ^ (i.val + j.val)) := by
  conv_lhs => rw [polynomial_product_eq_sum_fin p q hp hq]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- Polynomial input coordinates and any linear output functional restrict convolution exactly. -/
theorem convolution_coordinate_restriction {X' Y' Z' : Type*} {A B : ℕ}
    (left : X' → K[X]) (middle : Y' → K[X]) (right : Z' → K[X] →ₗ[K] K)
    (hleft : ∀ x, (left x).natDegree < A)
    (hmiddle : ∀ y, (middle y).natDegree < B) :
    Tensor.restrict (fun x i => (left x).coeff i.val)
      (fun y j => (middle y).coeff j.val)
      (fun z k => right z (X ^ k.val)) (convolution A B) =
      fun x y z => right z (left x * middle y) := by
  classical
  funext x y z
  rw [linearMap_product_eq_sum (left x) (middle y) (hleft x) (hmiddle y) (right z)]
  unfold Tensor.restrict
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_eq_single (convolutionOutput i j)]
  · simp only [convolution, convolutionOutput, ite_true, mul_one]
  · intro k hk hne
    have hval : i.val + j.val ≠ k.val := by
      intro h
      apply hne
      exact Fin.ext h.symm
    simp only [convolution, if_neg hval, mul_zero]
  · intro hn
    exact (hn (Finset.mem_univ _)).elim

end

end Lemmata.FockCircuits.Matrix.Spectral
