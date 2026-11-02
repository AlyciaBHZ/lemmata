module

public import Lemmata.FockCircuits.Matrix.Profile.ReplicationCoordinates
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Profile.Replication

open Polynomial
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

theorem blockPolynomial_grid (P : K[X]) {a d : ℕ} (hd : d < P.natDegree) :
    blockPolynomial P (d + a * P.natDegree) = X ^ d * P ^ a := by
  simp only [blockPolynomial, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hd, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt hd),
    Nat.div_eq_of_lt hd, zero_add]

theorem grid_eq_iff {q a c d f : ℕ} (hd : d < q) (hf : f < q) :
    d + a * q = f + c * q ↔ a = c ∧ d = f := by
  constructor
  · intro h
    have hq : 0 < q := Nat.zero_lt_of_lt hd
    have hdiv := congrArg (fun n => n / q) h
    have hmod := congrArg (fun n => n % q) h
    simp only [Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt hd,
      Nat.div_eq_of_lt hf, zero_add] at hdiv
    simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd,
      Nat.mod_eq_of_lt hf] at hmod
    exact ⟨hdiv, hmod⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem small_mul_power_eq_sum (P p : K[X]) (a : ℕ)
    (hp : p.natDegree < P.natDegree) :
    p * P ^ a = ∑ d ∈ Finset.range P.natDegree,
      p.coeff d • blockPolynomial P (d + a * P.natDegree) := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' hp]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [blockPolynomial_grid P (Finset.mem_range.mp hd), smul_eq_C_mul, mul_assoc]

/-- A coefficient in one polynomial-division block ignores all other blocks. -/
theorem blockCoefficient_small_mul_power (P p : K[X]) (hP : P.Monic)
    (a c : ℕ) {f : ℕ} (hf : f < P.natDegree)
    (hp : p.natDegree < P.natDegree) :
    blockCoefficient P hP (f + c * P.natDegree) (p * P ^ a) =
      if a = c then p.coeff f else 0 := by
  classical
  rw [small_mul_power_eq_sum P p a hp, map_sum]
  by_cases hac : a = c
  · subst c
    rw [if_pos rfl, Finset.sum_eq_single f]
    · simp only [map_smul, blockCoefficient_basis, ite_true, smul_eq_mul, mul_one]
    · intro d hd hdf
      have hne : d + a * P.natDegree ≠ f + a * P.natDegree := by
        intro h
        exact hdf ((grid_eq_iff (Finset.mem_range.mp hd) hf).mp h).2
      simp only [map_smul, blockCoefficient_basis, if_neg hne, smul_zero]
    · intro hf'
      exact (hf' (Finset.mem_range.mpr hf)).elim
  · rw [if_neg hac]
    apply Finset.sum_eq_zero
    intro d hd
    have hne : d + a * P.natDegree ≠ f + c * P.natDegree := by
      intro h
      exact hac ((grid_eq_iff (Finset.mem_range.mp hd) hf).mp h).1
    simp only [map_smul, blockCoefficient_basis, if_neg hne, smul_zero]

/-- In block coordinates polynomial multiplication has only a remainder and one carry. -/
theorem blockCoefficient_product (P u v : K[X]) (hP : P.Monic)
    (hq : 0 < P.natDegree) (a b c : ℕ) {f : ℕ} (hf : f < P.natDegree)
    (hu : u.natDegree < P.natDegree) (hv : v.natDegree < P.natDegree) :
    blockCoefficient P hP (f + c * P.natDegree) ((u * P ^ a) * (v * P ^ b)) =
      (if a + b = c then (u * v %ₘ P).coeff f else 0) +
        (if a + b + 1 = c then (u * v /ₘ P).coeff f else 0) := by
  rw [blockCoefficient_product_two_blocks,
    blockCoefficient_small_mul_power P (u * v %ₘ P) hP (a + b) c hf
      (product_remainder_degree hP hq),
    blockCoefficient_small_mul_power P (u * v /ₘ P) hP (a + b + 1) c hf
      (product_carry_degree hP hu hv)]

end

end Lemmata.FockCircuits.Matrix.Profile.Replication
