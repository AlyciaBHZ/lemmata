module

public import Lemmata.FockCircuits.BasisAction
public import Mathlib.Tactic.Module

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Fock

variable (R : Type*) [CommRing R]

noncomputable def shearLinear (a : R) (i j : ℕ) : OneParticle R →ₗ[R] OneParticle R :=
  LinearMap.id + a • ((Finsupp.lsingle j).comp (Finsupp.lapply i))

theorem shearLinear_apply (a : R) (i j : ℕ) (v : OneParticle R) :
    shearLinear R a i j v = v + (a * v i) • Finsupp.single j 1 := by
  ext k
  by_cases hj : j = k <;>
    simp [shearLinear, Finsupp.lsingle_apply, Finsupp.lapply_apply,
      Finsupp.single_apply, hj, smul_eq_mul, mul_assoc]

noncomputable def shear (a : R) (i j : ℕ) : Fock R →ₐ[R] Fock R :=
  ExteriorAlgebra.map (shearLinear R a i j)

theorem shear_ι (a : R) (i j : ℕ) (v : OneParticle R) :
    shear R a i j (ExteriorAlgebra.ι R v) =
      ExteriorAlgebra.ι R v + (a * v i) • generator R j := by
  simp only [shear, ExteriorAlgebra.map_apply_ι, shearLinear_apply, map_add,
    map_smul, generator]

theorem shear_apply (a : R) (i j : ℕ) (x : Fock R) :
    shear R a i j x = x + a • (generator R j * contract R i x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp [contract, CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy =>
    simp only [map_add, hx, hy, mul_add, smul_add]
    abel
  | ι_mul x v ih =>
    have hd : contract R i (ExteriorAlgebra.ι R v * x) =
        v i • x - ExteriorAlgebra.ι R v * contract R i x := by
      simpa only [contract, Finsupp.lapply_apply] using
        (CliffordAlgebra.contractLeft_ι_mul
          (Q := (0 : QuadraticForm R (OneParticle R))) (Finsupp.lapply i) v x)
    have hc : generator R j * ExteriorAlgebra.ι R v =
        -(ExteriorAlgebra.ι R v * generator R j) := by
      apply eq_neg_iff_add_eq_zero.mpr
      exact ExteriorAlgebra.ι_add_mul_swap (R := R) (Finsupp.single j 1) v
    rw [map_mul, shear_ι, ih, hd]
    simp only [add_mul, mul_add, mul_sub, smul_add, smul_sub,
      smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc,
      generator_sq, zero_mul, smul_zero, add_zero, hc, neg_mul, smul_neg]
    module

theorem doubledEnergy_replace {i j : ℕ} {I : Finset ℕ}
    (hi : i ∈ I) (hj : j ∉ I.erase i) :
    doubledEnergy (insert j (I.erase i)) + 2 * i =
      doubledEnergy I + 2 * j := by
  have he : doubledEnergy (I.erase i) + (2 * i + 1) = doubledEnergy I := by
    exact Finset.sum_erase_add _ _ hi
  have hin : doubledEnergy (insert j (I.erase i)) =
      (2 * j + 1) + doubledEnergy (I.erase i) := by
    exact Finset.sum_insert hj
  omega

theorem shear_basis_sparse_energy (a : R) (i j : ℕ) (I : Finset ℕ) :
    ∃ (J : Finset ℕ) (c : R),
      shear R a i j (basis R I) = basis R I + c • basis R J ∧
      (c = 0 ∨ doubledEnergy J + 2 * i = doubledEnergy I + 2 * j) := by
  rw [shear_apply]
  by_cases hi : i ∈ I
  · obtain ⟨ε, hε⟩ := contract_basis_of_mem R hi
    rw [hε, mul_smul_comm]
    by_cases hj : j ∈ I.erase i
    · refine ⟨I, 0, ?_, Or.inl rfl⟩
      have hz := create_basis_of_mem R hj
      simp only [create_apply] at hz
      rw [hz]
      simp
    · obtain ⟨η, hη⟩ := create_basis_of_not_mem R hj
      simp only [create_apply] at hη
      rw [hη]
      refine ⟨insert j (I.erase i), a * (ε : ℤ) * (η : ℤ), ?_,
        Or.inr (doubledEnergy_replace hi hj)⟩
      simp [Units.smul_def, ← Int.cast_smul_eq_zsmul R, smul_smul, mul_assoc]
  · refine ⟨I, 0, ?_, Or.inl rfl⟩
    rw [contract_basis_of_not_mem R hi]
    simp

theorem shear_basis_lowering (a : R) {i j : ℕ} (hji : j ≤ i) (I : Finset ℕ) :
    ∃ (J : Finset ℕ) (c : R),
      shear R a i j (basis R I) = basis R I + c • basis R J ∧
      doubledEnergy J ≤ doubledEnergy I := by
  obtain ⟨J, c, h, hc⟩ := shear_basis_sparse_energy R a i j I
  rcases hc with rfl | hc
  · exact ⟨I, 0, by simpa using h, le_rfl⟩
  · exact ⟨J, c, h, by omega⟩

theorem shear_basis_raising (a : R) {i j : ℕ} (hij : i ≤ j) (I : Finset ℕ) :
    ∃ (J : Finset ℕ) (c : R),
      shear R a i j (basis R I) = basis R I + c • basis R J ∧
      doubledEnergy I ≤ doubledEnergy J := by
  obtain ⟨J, c, h, hc⟩ := shear_basis_sparse_energy R a i j I
  rcases hc with rfl | hc
  · exact ⟨I, 0, by simpa using h, le_rfl⟩
  · exact ⟨J, c, h, by omega⟩

end Lemmata.FockCircuits.Fock
