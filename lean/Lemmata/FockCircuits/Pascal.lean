module

public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.Algebra.Polynomial.Coeff
public import Lemmata.FockCircuits.Exterior

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits

theorem choose_convolution (m k : ℕ) :
    (∑ j ∈ Finset.range (m + 1), m.choose j * k.choose j) =
      (m + k).choose m := by
  symm
  calc
    (m + k).choose m = (k + m).choose m := by rw [Nat.add_comm m k]
    _ = ∑ j ∈ Finset.range (m + 1), k.choose j * m.choose (m - j) := by
      rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    _ = ∑ j ∈ Finset.range (m + 1), m.choose j * k.choose j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [Nat.choose_symm hjm, Nat.mul_comm]

def positiveCoefficient (m k : ℕ) : ℤ := k.choose m

def negativeCoefficient (m k : ℕ) : ℤ :=
  (-1 : ℤ) ^ m * ((k + m).choose m : ℤ)

def pascalCoefficient (m j : ℕ) : ℤ :=
  (-1 : ℤ) ^ m * (m.choose j : ℤ)

theorem pascal_convolution (m k : ℕ) :
    (∑ j ∈ Finset.range (m + 1),
      pascalCoefficient m j * positiveCoefficient j k) =
        negativeCoefficient m k := by
  have hc :
      (∑ j ∈ Finset.range (m + 1), (m.choose j : ℤ) * (k.choose j : ℤ)) =
        ((m + k).choose m : ℤ) := by
    exact_mod_cast choose_convolution m k
  unfold pascalCoefficient positiveCoefficient negativeCoefficient
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, hc, Nat.add_comm m k]

namespace Fock

variable (R : Type*) [CommRing R]

noncomputable def polynomialReflection : Polynomial R ≃ₐ[R] Polynomial R :=
  Polynomial.algEquivOfCompEqX (-(Polynomial.X + 1)) (-(Polynomial.X + 1))
    (by simp) (by simp)

@[simp] theorem polynomialReflection_pow (m : ℕ) :
    polynomialReflection R (Polynomial.X ^ m) = (-(Polynomial.X + 1)) ^ m := by
  simp [polynomialReflection]

theorem polynomialReflection_coeff (m j : ℕ) :
    (polynomialReflection R (Polynomial.X ^ m)).coeff j =
      (-1 : R) ^ m * (m.choose j : R) := by
  rw [polynomialReflection_pow, neg_eq_neg_one_mul, mul_pow]
  have hc : (-1 : Polynomial R) ^ m = Polynomial.C ((-1 : R) ^ m) := by simp
  rw [hc, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_one_pow]

noncomputable def polynomialCoordinates : OneParticle R ≃ₗ[R] Polynomial R :=
  (Polynomial.basisMonomials R).repr.symm

noncomputable def pascal : OneParticle R ≃ₗ[R] OneParticle R :=
  (polynomialCoordinates R).trans
    ((polynomialReflection R).toLinearEquiv.trans (polynomialCoordinates R).symm)

@[simp] theorem pascal_symm : (pascal R).symm = pascal R := by
  ext v
  rfl

@[simp] theorem polynomialCoordinates_single (m : ℕ) :
    polynomialCoordinates R (Finsupp.single m 1) = Polynomial.X ^ m := by
  simp [polynomialCoordinates, Polynomial.coe_basisMonomials,
    Polynomial.monomial_one_right_eq_X_pow]

@[simp] theorem polynomialCoordinates_coeff (v : OneParticle R) (j : ℕ) :
    (polynomialCoordinates R v).coeff j = v j := by
  rfl

theorem pascal_single_coordinates (m j : ℕ) :
    (polynomialCoordinates R (pascal R (Finsupp.single m 1))).coeff j =
      (-1 : R) ^ m * (m.choose j : R) := by
  simp only [pascal, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    AlgEquiv.toLinearEquiv_apply, polynomialCoordinates_single]
  exact polynomialReflection_coeff R m j

theorem pascal_single_apply (m j : ℕ) :
    pascal R (Finsupp.single m 1) j =
      (-1 : R) ^ m * (m.choose j : R) := by
  simpa only [polynomialCoordinates_coeff] using pascal_single_coordinates R m j

theorem pascal_single_eq_zero_of_lt {m j : ℕ} (hmj : m < j) :
    pascal R (Finsupp.single m 1) j = 0 := by
  rw [pascal_single_apply, Nat.choose_eq_zero_of_lt hmj, Nat.cast_zero, mul_zero]

theorem pascal_single_sum (m : ℕ) :
    pascal R (Finsupp.single m 1) =
      ∑ j ∈ Finset.range (m + 1), (pascalCoefficient m j : R) • Finsupp.single j 1 := by
  ext k
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hk : k < m + 1
  · simp [Finset.mem_range.mpr hk, pascal_single_apply, pascalCoefficient]
  · have hmk : m < k := by omega
    rw [pascal_single_eq_zero_of_lt R hmk]
    simp [hk]

noncomputable def pascalExterior : Fock R →ₐ[R] Fock R :=
  ExteriorAlgebra.map (pascal R).toLinearMap

noncomputable def pascalExteriorInverse : Fock R →ₐ[R] Fock R :=
  ExteriorAlgebra.map (pascal R).symm.toLinearMap

@[simp] theorem pascalExteriorInverse_eq : pascalExteriorInverse R = pascalExterior R := by
  rw [pascalExteriorInverse, pascal_symm]
  rfl

@[simp] theorem pascalExterior_inverse (x : Fock R) :
    pascalExterior R (pascalExteriorInverse R x) = x := by
  have h : (pascalExterior R).comp (pascalExteriorInverse R) = AlgHom.id R (Fock R) := by
    rw [pascalExterior, pascalExteriorInverse, ExteriorAlgebra.map_comp_map]
    have hi : (pascal R).toLinearMap.comp (pascal R).symm.toLinearMap =
        LinearMap.id := by
      apply LinearMap.ext
      intro v
      exact (pascal R).apply_symm_apply v
    rw [hi, ExteriorAlgebra.map_id]
  exact AlgHom.congr_fun h x

@[simp] theorem pascalExteriorInverse_apply (x : Fock R) :
    pascalExteriorInverse R (pascalExterior R x) = x := by
  have h : (pascalExteriorInverse R).comp (pascalExterior R) = AlgHom.id R (Fock R) := by
    rw [pascalExterior, pascalExteriorInverse, ExteriorAlgebra.map_comp_map]
    have hi : (pascal R).symm.toLinearMap.comp (pascal R).toLinearMap =
        LinearMap.id := by
      apply LinearMap.ext
      intro v
      exact (pascal R).symm_apply_apply v
    rw [hi, ExteriorAlgebra.map_id]
  exact AlgHom.congr_fun h x

theorem exterior_orientation
    (A B : OneParticle R →ₗ[R] OneParticle R) (v : Fock R) :
    ExteriorAlgebra.map (A + B.comp (pascal R).toLinearMap) v =
      ExteriorAlgebra.map (A.comp (pascal R).symm.toLinearMap + B)
        (pascalExterior R v) := by
  have h : (A.comp (pascal R).symm.toLinearMap + B).comp
        (pascal R).toLinearMap = A + B.comp (pascal R).toLinearMap := by
    ext x i
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  rw [pascalExterior, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, h]

end Fock

end Lemmata.FockCircuits
