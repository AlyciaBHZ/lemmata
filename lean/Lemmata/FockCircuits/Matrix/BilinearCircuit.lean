module

public import Lemmata.FockCircuits.Compiler
public import Lemmata.FockCircuits.Matrix.CircuitBuilders
public import Lemmata.FockCircuits.Matrix.Foundation.MatrixCoefficients

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix

open Foundation
open scoped BigOperators

noncomputable section

variable {K A B C : Type*} [CommSemiring K]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

structure BilinearScheme (K A B C : Type*) [CommSemiring K]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] where
  rank : ℕ
  left : Fin rank → A × B → K
  right : Fin rank → B × C → K
  output : Fin rank → C × A → K
  coefficient_identity : Tensor.matrixCoefficients (K := K) A B C =
    fun x y z => ∑ t, Tensor.rankOne (left t) (right t) (output t) x y z

namespace BilinearScheme

def ofRankAtMost {r : ℕ}
    (h : Tensor.RankAtMost (Tensor.matrixCoefficients (K := K) A B C) r) :
    BilinearScheme K A B C where
  rank := r
  left := h.choose
  right := h.choose_spec.choose
  output := h.choose_spec.choose_spec.choose
  coefficient_identity := h.choose_spec.choose_spec.choose_spec

/-- The coefficient identity is valid for ordered products in every algebra over the base ring. -/
theorem ordered_identity [Fintype A] [Fintype B] [Fintype C]
    (s : BilinearScheme K A B C) {D : Type*} [Semiring D] [Algebra K D]
    (left : A × B → D) (right : B × C → D) (i : A) (k : C) :
    (∑ t, s.output t (k, i) •
      ((∑ x, s.left t x • left x) * (∑ y, s.right t y • right y))) =
      ∑ j, left (i, j) * right (j, k) := by
  have hcoef (x : A × B) (y : B × C) :
      (∑ t, s.left t x * s.right t y * s.output t (k, i)) =
        Tensor.matrixCoefficients (K := K) A B C x y (k, i) :=
    (congrFun (congrFun (congrFun s.coefficient_identity x) y) (k, i)).symm
  calc
    _ = ∑ t, ∑ x, ∑ y,
        (s.left t x * s.right t y * s.output t (k, i)) • (left x * right y) := by
      simp only [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum,
        smul_mul_assoc, mul_smul_comm, smul_smul]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      congr 1
      ring
    _ = ∑ x, ∑ y, ∑ t,
        (s.left t x * s.right t y * s.output t (k, i)) • (left x * right y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = ∑ x, ∑ y, (Tensor.matrixCoefficients (K := K) A B C x y (k, i)) •
        (left x * right y) := by simp_rw [← Finset.sum_smul, hcoef]
    _ = _ := by
      simp [Tensor.matrixCoefficients, Fintype.sum_prod_type, ite_and, ite_smul]

end BilinearScheme

end

end Lemmata.FockCircuits.Matrix
