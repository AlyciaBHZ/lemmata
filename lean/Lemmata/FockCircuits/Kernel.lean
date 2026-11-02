module

public import Lemmata.FockCircuits.Exterior
public import Lemmata.FockCircuits.Wick
public import Mathlib.Tactic.NoncommRing

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.TwoColour

variable (R : Type*) [CommRing R]

noncomputable def left (i : ℕ) : Fock R := Fock.generator R (2 * i)

noncomputable def right (i : ℕ) : Fock R := Fock.generator R (2 * i + 1)

noncomputable def factor (i : ℕ) : Fock R := 1 + left R i * right R i

noncomputable def kernel : ℕ → Fock R
  | 0 => 1
  | N + 1 => factor R N * kernel N

@[simp] theorem kernel_zero : kernel R 0 = 1 := rfl

@[simp] theorem kernel_succ (N : ℕ) :
    kernel R (N + 1) = factor R N * kernel R N := rfl

private theorem generator_swap (i j : ℕ) :
    Fock.generator R i * Fock.generator R j =
      -(Fock.generator R j * Fock.generator R i) :=
  eq_neg_iff_add_eq_zero.mpr (Fock.generator_anticommute R i j)

theorem factor_commutes_generator (i j : ℕ) :
    factor R i * Fock.generator R j = Fock.generator R j * factor R i := by
  have h : (left R i * right R i) * Fock.generator R j =
      Fock.generator R j * (left R i * right R i) := by
    calc
      _ = left R i * (right R i * Fock.generator R j) := mul_assoc _ _ _
      _ = left R i * -(Fock.generator R j * right R i) := by
        rw [right, generator_swap]
      _ = -((left R i * Fock.generator R j) * right R i) := by
        simp only [mul_neg, mul_assoc]
      _ = Fock.generator R j * (left R i * right R i) := by
        rw [left, generator_swap]
        simp only [neg_mul, neg_neg, mul_assoc]
  simp only [factor, add_mul, mul_add, one_mul, mul_one, h]

theorem factor_commutes_right (i j : ℕ) :
    factor R i * right R j = right R j * factor R i :=
  factor_commutes_generator R i (2 * j + 1)

@[simp] theorem right_mul_factor (i : ℕ) : right R i * factor R i = right R i := by
  have h : right R i * (left R i * right R i) = 0 := by
    rw [← mul_assoc, right, left, generator_swap]
    simp only [neg_mul, mul_assoc, Fock.generator_sq, mul_zero, neg_zero]
  simp only [factor, mul_add, mul_one, h, add_zero]

theorem contract_left_right (i j : ℕ) (x : Fock R) :
    Fock.contract R (2 * i) (right R j * x) =
      -(right R j * Fock.contract R (2 * i) x) := by
  have h : 2 * i ≠ 2 * j + 1 := by omega
  simpa only [Fock.create_apply, right, h, ite_false, zero_sub] using
    Fock.contract_create R (2 * i) (2 * j + 1) x

theorem contract_factor (i j : ℕ) (x : Fock R) :
    Fock.contract R (2 * i) (factor R j * x) =
      (if i = j then right R j * x else 0) +
        factor R j * Fock.contract R (2 * i) x := by
  have heq : 2 * i = 2 * j ↔ i = j := by omega
  have h := Fock.contract_create R (2 * i) (2 * j)
    (right R j * x)
  simp only [Fock.create_apply, heq, contract_left_right, mul_neg] at h
  simp only [factor, add_mul, one_mul, map_add, mul_assoc, left]
  rw [h]
  by_cases hij : i = j <;> simp only [hij, ite_true, ite_false] <;> noncomm_ring

theorem contract_kernel_of_le (N i : ℕ) (hNi : N ≤ i) :
    Fock.contract R (2 * i) (kernel R N) = 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [kernel_succ, contract_factor]
    have hne : i ≠ N := by omega
    simp only [hne, ite_false, ih (by omega), mul_zero, add_zero]

theorem contract_kernel (N i : ℕ) (hiN : i < N) :
    Fock.contract R (2 * i) (kernel R N) = right R i * kernel R N := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [kernel_succ, contract_factor]
    by_cases hi : i = N
    · subst i
      rw [ite_eq_left rfl, contract_kernel_of_le R N N le_rfl]
      simp only [mul_zero, add_zero, ← mul_assoc, right_mul_factor]
    · have hiN' : i < N := by omega
      rw [ite_eq_right hi, zero_add, ih hiN', ← mul_assoc,
        factor_commutes_right, mul_assoc]

noncomputable def leftVector (N : ℕ) (a : Fin N → R) : OneParticle R :=
  ∑ i, a i • Finsupp.single (2 * (i : ℕ)) 1

noncomputable def rightVector (N : ℕ) (a : Fin N → R) : OneParticle R :=
  ∑ i, a i • Finsupp.single (2 * (i : ℕ) + 1) 1

theorem rightVector_even (N : ℕ) (a : Fin N → R) (i : ℕ) :
    rightVector R N a (2 * i) = 0 := by
  simp only [rightVector, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro j hj
  have h : 2 * (j : ℕ) + 1 ≠ 2 * i := by omega
  simp only [Finsupp.single_apply, h, ite_false, mul_zero]

theorem coordinateDual_left_right (N : ℕ) (a b : Fin N → R) :
    Fock.coordinateDual R (leftVector R N a) (rightVector R N b) = 0 := by
  simp only [leftVector, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, Fock.coordinateDual_single, one_mul,
    rightVector_even, smul_zero, Finset.sum_const_zero]

theorem createVector_left (N : ℕ) (a : Fin N → R) :
    ExteriorAlgebra.ι R (leftVector R N a) = ∑ i, a i • left R i := by
  simp only [leftVector, map_sum, map_smul, left, Fock.generator]

theorem createVector_right (N : ℕ) (a : Fin N → R) :
    ExteriorAlgebra.ι R (rightVector R N a) = ∑ i, a i • right R i := by
  simp only [rightVector, map_sum, map_smul, right, Fock.generator]

theorem contractVector_left (N : ℕ) (a : Fin N → R) (x : Fock R) :
    Fock.contractVector R (leftVector R N a) x =
      ∑ i, a i • Fock.contract R (2 * (i : ℕ)) x := by
  let d : OneParticle R →ₗ[R] Fock R →ₗ[R] Fock R :=
    (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (OneParticle R)))).comp
      (Fock.coordinateDual R)
  change d (∑ i, a i • Finsupp.single (2 * (i : ℕ)) 1) x = _
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change a i • Fock.contractVector R (Finsupp.single (2 * (i : ℕ)) 1) x = _
  rw [Fock.contractVector_single]

theorem contractVector_kernel (N : ℕ) (a : Fin N → R) :
    Fock.contractVector R (leftVector R N a) (kernel R N) =
      ExteriorAlgebra.ι R (rightVector R N a) * kernel R N := by
  rw [contractVector_left, createVector_right, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [contract_kernel R N i i.isLt, smul_mul_assoc]

theorem normalList_create_of_orthogonal
    (L : List (OneParticle R × OneParticle R)) (y : OneParticle R) (x : Fock R)
    (h : ∀ a ∈ L, Fock.coordinateDual R a.2 y = 0) :
    Fock.normalList R L (Fock.createVector R y x) =
      (-1 : R) ^ L.length • Fock.createVector R y (Fock.normalList R L x) := by
  induction L generalizing x with
  | nil => simp
  | cons a L ih =>
    have ha : Fock.coordinateDual R a.2 y = 0 := h a (by simp)
    have hL : ∀ b ∈ L, Fock.coordinateDual R b.2 y = 0 :=
      fun b hb => h b (List.mem_cons_of_mem a hb)
    have hcc (z : Fock R) :
        Fock.createVector R a.1 (Fock.createVector R y z) =
          -Fock.createVector R y (Fock.createVector R a.1 z) :=
      eq_neg_iff_add_eq_zero.mpr (Fock.createVector_anticommute R a.1 y z)
    have hdc : Fock.contractVector R a.2 (Fock.createVector R y x) =
        -Fock.createVector R y (Fock.contractVector R a.2 x) := by
      rw [Fock.contractVector_createVector, ha, zero_smul, zero_sub]
    have hs : (-1 : R) ^ L.length * (-1 : R) ^ L.length = 1 := by
      rw [← mul_pow]
      simp
    simp only [Fock.normalList_cons, List.length_cons]
    rw [ih _ hL, hdc, map_neg, ih _ hL]
    simp only [map_smul, hcc, pow_succ, mul_neg, mul_one, neg_smul,
      smul_neg, smul_add, smul_smul, hs, one_smul, map_add]
    match_scalars <;>
      rcases neg_one_pow_eq_or R L.length with hsign | hsign <;>
      simp [hsign] <;> ring

noncomputable def colouredList (N : ℕ) (L : List ((Fin N → R) × (Fin N → R))) :
    List (OneParticle R × OneParticle R) :=
  L.map fun a => (leftVector R N a.1, leftVector R N a.2)

noncomputable def colouredProduct (N : ℕ) (L : List ((Fin N → R) × (Fin N → R))) :
    Fock R :=
  (L.map fun a => ExteriorAlgebra.ι R (leftVector R N a.1) +
    ExteriorAlgebra.ι R (rightVector R N a.2)).prod

theorem normalList_kernel (N : ℕ) (L : List ((Fin N → R) × (Fin N → R))) :
    Fock.normalList R (colouredList R N L) (kernel R N) =
      colouredProduct R N L * kernel R N := by
  induction L with
  | nil => simp [colouredList, colouredProduct]
  | cons a L ih =>
    have horth : ∀ b ∈ colouredList R N L,
        Fock.coordinateDual R b.2 (rightVector R N a.2) = 0 := by
      intro b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
      exact coordinateDual_left_right R N c.2 a.2
    have hmove := normalList_create_of_orthogonal R (colouredList R N L)
      (rightVector R N a.2) (kernel R N) horth
    have hs : (-1 : R) ^ L.length * (-1 : R) ^ L.length = 1 := by
      rw [← mul_pow]
      simp
    simp only [colouredList, List.map_cons, Fock.normalList_cons, List.length_map]
    rw [contractVector_kernel]
    change ExteriorAlgebra.ι R (leftVector R N a.1) *
        Fock.normalList R (colouredList R N L) (kernel R N) +
      (-1 : R) ^ L.length • Fock.normalList R (colouredList R N L)
        (Fock.createVector R (rightVector R N a.2) (kernel R N)) = _
    rw [hmove]
    simp only [colouredList, List.length_map] at hs ⊢
    rw [smul_smul, hs, one_smul]
    simp only [Fock.createVector_apply]
    simp only [colouredList] at ih
    rw [← add_mul, ih]
    simp only [colouredProduct, List.map_cons, List.prod_cons, mul_assoc]

end Lemmata.FockCircuits.TwoColour
