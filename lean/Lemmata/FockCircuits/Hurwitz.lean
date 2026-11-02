module

public import Lemmata.FockCircuits.Compiler
public import Mathlib.Basic.Complex.Basic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lemmata.FockCircuits.Hurwitz

variable {R I J ρ : Type*} [CommRing R] [Fintype I] [Fintype J] [Fintype ρ]

def bilinear (a : I → J → R) (x : I → R) (y : J → R) : R :=
  ∑ i, ∑ j, a i j * x i * y j

theorem bilinear_add (a b : I → J → R) (x : I → R) (y : J → R) :
    bilinear (a + b) x y = bilinear a x y + bilinear b x y := by
  simp only [bilinear, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem bilinear_sub (a b : I → J → R) (x : I → R) (y : J → R) :
    bilinear (a - b) x y = bilinear a x y - bilinear b x y := by
  simp only [bilinear, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem bilinear_smul (c : R) (a : I → J → R) (x : I → R) (y : J → R) :
    bilinear (c • a) x y = c * bilinear a x y := by
  simp only [bilinear, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem bilinear_eq_row_sum (a : I → J → R) (x : I → R) (y : J → R) :
    bilinear a x y = ∑ j, coefficientRows (fun (_ : Unit) => a) x () j * y j := by
  simp only [bilinear, coefficientRows, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_comm

theorem commutative_assembly (a b c d : Matrix ρ J R) (y : J → R) :
    orderedAssembly a b c d (fun j (_ : Unit) => y j) (fun j (_ : Unit) => y j) =
      ∑ r, ((∑ j, a r j * y j) * (∑ j, b r j * y j) +
        (∑ j, c r j * y j) * (∑ j, d r j * y j)) := by
  rw [orderedAssembly_expansion]
  simp only [Fintype.sum_unique, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro j hj
    ring

theorem products_of_crossing [DecidableEq I] [DecidableEq J]
    (a b c d : ρ → I → J → R)
    (h : ∀ i j k l,
      (∑ r, a r i j * b r k l) + (∑ r, c r i l * d r k j) =
        if i = k then (if j = l then 1 else 0) else 0)
    (x : I → R) (y : J → R) :
    (∑ r, (bilinear (a r) x y * bilinear (b r) x y +
      bilinear (c r) x y * bilinear (d r) x y)) =
        (∑ i, x i ^ 2) * (∑ j, y j ^ 2) := by
  have hh := directAssembly_eq_crossing a b c d h x x
    (fun j (_ : Unit) => y j) (fun j (_ : Unit) => y j)
  rw [commutative_assembly] at hh
  have hbil (f : ρ → I → J → R) (r : ρ) :
      (∑ j, coefficientRows f x r j * y j) = bilinear (f r) x y := by
    simpa only [bilinear, coefficientRows, smul_eq_mul, Finset.sum_mul] using
      (Finset.sum_comm :
        (∑ j, ∑ i, f r i j * x i * y j) = ∑ i, ∑ j, f r i j * x i * y j)
  simp_rw [hbil] at hh
  rw [hh]
  simp only [batchedCrossing, Fintype.sum_unique, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem product_two_squares (u v : ℂ) :
    ((u + v) / 2) ^ 2 + ((u - v) * Complex.I / 2) ^ 2 = u * v := by
  have hI := Complex.I_sq
  calc
    _ = ((u + v) ^ 2 + (u - v) ^ 2 * Complex.I ^ 2) / 4 := by ring
    _ = _ := by rw [hI]; ring

noncomputable def squareCoefficients (a b : I → J → ℂ) (positive : Bool) : I → J → ℂ :=
  if positive then (2 : ℂ)⁻¹ • (a + b) else (Complex.I / 2) • (a - b)

theorem squares_of_product (a b : I → J → ℂ) (x : I → ℂ) (y : J → ℂ) :
    (∑ positive : Bool, bilinear (squareCoefficients a b positive) x y ^ 2) =
      bilinear a x y * bilinear b x y := by
  simp only [Fintype.sum_bool, squareCoefficients, Bool.false_eq_true, if_false, if_true,
    bilinear_smul, bilinear_add, bilinear_sub]
  convert product_two_squares (bilinear a x y) (bilinear b x y) using 1 <;> ring

theorem products_to_squares (a b : ρ → I → J → ℂ) :
    ∃ forms : (ρ × Bool) → I → J → ℂ,
      ∀ (x : I → ℂ) (y : J → ℂ),
        (∑ r, bilinear (forms r) x y ^ 2) = ∑ r, bilinear (a r) x y * bilinear (b r) x y := by
  refine ⟨fun r => squareCoefficients (a r.1) (b r.1) r.2, ?_⟩
  intro x y
  simp only [Fintype.sum_prod_type, squares_of_product]

theorem squares_of_crossing [DecidableEq I] [DecidableEq J]
    (a b c d : ρ → I → J → ℂ)
    (h : ∀ i j k l,
      (∑ r, a r i j * b r k l) + (∑ r, c r i l * d r k j) =
        if i = k then (if j = l then 1 else 0) else 0) :
    ∃ forms : ((ρ × Bool) × Bool) → I → J → ℂ,
      ∀ (x : I → ℂ) (y : J → ℂ),
        (∑ r, bilinear (forms r) x y ^ 2) = (∑ i, x i ^ 2) * (∑ j, y j ^ 2) := by
  let left : (ρ × Bool) → I → J → ℂ := fun r => if r.2 then a r.1 else c r.1
  let right : (ρ × Bool) → I → J → ℂ := fun r => if r.2 then b r.1 else d r.1
  obtain ⟨forms, hforms⟩ := products_to_squares left right
  refine ⟨forms, ?_⟩
  intro x y
  rw [hforms, Fintype.sum_prod_type]
  have hh : (∑ r : ρ, ∑ bit : Bool,
      bilinear (left (r, bit)) x y * bilinear (right (r, bit)) x y) =
      ∑ r, (bilinear (a r) x y * bilinear (b r) x y +
        bilinear (c r) x y * bilinear (d r) x y) := by
    apply Finset.sum_congr rfl
    intro r hr
    simp [left, right, Fintype.sum_bool, add_comm]
  rw [hh]
  exact products_of_crossing a b c d h x y

theorem square_index_card : Fintype.card ((ρ × Bool) × Bool) = 4 * Fintype.card ρ := by
  simp only [Fintype.card_prod, Fintype.card_bool]
  omega

theorem squares_of_integral_crossing [DecidableEq I] [DecidableEq J]
    (a b c d : ρ → I → J → ℤ)
    (h : ∀ i j k l,
      (∑ r, a r i j * b r k l) + (∑ r, c r i l * d r k j) =
        if i = k then (if j = l then 1 else 0) else 0) :
    ∃ forms : ((ρ × Bool) × Bool) → I → J → ℂ,
      ∀ (x : I → ℂ) (y : J → ℂ),
        (∑ r, bilinear (forms r) x y ^ 2) = (∑ i, x i ^ 2) * (∑ j, y j ^ 2) := by
  apply squares_of_crossing
    (fun r i j => (a r i j : ℂ)) (fun r i j => (b r i j : ℂ))
    (fun r i j => (c r i j : ℂ)) (fun r i j => (d r i j : ℂ))
  intro i j k l
  have hh := congrArg (fun z : ℤ => (z : ℂ)) (h i j k l)
  by_cases hik : i = k <;> by_cases hjl : j = l <;> simpa [hik, hjl] using hh

end Lemmata.FockCircuits.Hurwitz
