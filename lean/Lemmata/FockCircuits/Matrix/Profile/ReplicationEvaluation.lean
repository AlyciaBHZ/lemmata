module

public import Lemmata.FockCircuits.Matrix.Profile.ReplicationCoefficients
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Profile.Replication

open Polynomial
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

def blockEvaluation (P : K[X]) (hP : P.Monic) (c : ℕ) (x : K) : K[X] →ₗ[K] K :=
  ∑ f : Fin P.natDegree,
    (x ^ f.val) • blockCoefficient P hP (f.val + c * P.natDegree)

theorem eval_eq_sum_small (p : K[X]) (x : K) {q : ℕ} (hp : p.natDegree < q) :
    p.eval x = ∑ d : Fin q, p.coeff d.val * x ^ d.val := by
  have h := congrArg (Polynomial.eval x) (p.as_sum_range_C_mul_X_pow' hp)
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X] at h
  exact h.trans (Fin.sum_univ_eq_sum_range (fun d => p.coeff d * x ^ d) q).symm

theorem blockEvaluation_small_mul_power (P p : K[X]) (hP : P.Monic)
    (a c : ℕ) (x : K) (hp : p.natDegree < P.natDegree) :
    blockEvaluation P hP c x (p * P ^ a) = if a = c then p.eval x else 0 := by
  classical
  simp only [blockEvaluation, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  simp_rw [blockCoefficient_small_mul_power P p hP a c (Fin.isLt _) hp]
  split_ifs with hac
  · rw [eval_eq_sum_small p x hp]
    apply Finset.sum_congr rfl
    intro d hd
    exact mul_comm _ _
  · simp only [mul_zero, Finset.sum_const_zero]

theorem blockEvaluation_product (P u v : K[X]) (hP : P.Monic)
    (hq : 0 < P.natDegree) (a b c : ℕ) (x : K)
    (hu : u.natDegree < P.natDegree) (hv : v.natDegree < P.natDegree)
    (hx : P.eval x = 0) :
    blockEvaluation P hP c x ((u * P ^ a) * (v * P ^ b)) =
      (if a + b = c then u.eval x * v.eval x else 0) +
        (if a + b + 1 = c then (u * v /ₘ P).eval x else 0) := by
  rw [product_two_blocks, map_add,
    blockEvaluation_small_mul_power P (u * v %ₘ P) hP (a + b) c x
      (product_remainder_degree hP hq),
    blockEvaluation_small_mul_power P (u * v /ₘ P) hP (a + b + 1) c x
      (product_carry_degree hP hu hv), eval_product_remainder hx]

/-- Interpolation diagonalizes the no-carry component without dividing by the characteristic. -/
theorem lagrange_remainder_eval {q : ℕ} (nodes : Fin q → K)
    (hnodes : Function.Injective nodes) (P : K[X])
    (hroot : ∀ i, P.eval (nodes i) = 0) (i j k : Fin q) :
    (((Lagrange.basis Finset.univ nodes i * Lagrange.basis Finset.univ nodes j) %ₘ P).eval
      (nodes k)) = if i = k ∧ j = k then 1 else 0 := by
  rw [eval_product_remainder (hroot k)]
  have heval (a : Fin q) : (Lagrange.basis Finset.univ nodes a).eval (nodes k) =
      if a = k then 1 else 0 := by
    by_cases hak : a = k
    · subst a
      simp only [ite_true]
      exact Lagrange.eval_basis_self hnodes.injOn (Finset.mem_univ k)
    · rw [if_neg hak]
      exact Lagrange.eval_basis_of_ne hak (Finset.mem_univ k)
  rw [heval i, heval j]
  split_ifs <;> simp_all

end

end Lemmata.FockCircuits.Matrix.Profile.Replication
