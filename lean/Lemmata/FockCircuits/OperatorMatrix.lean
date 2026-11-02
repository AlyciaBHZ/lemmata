module

public import Lemmata.FockCircuits.KernelOperators
public import Lemmata.FockCircuits.KernelRectangle

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lemmata.FockCircuits.FiniteIdentity

open scoped BigOperators

noncomputable section

variable (R : Type*) [CommRing R]

def finiteProjection (L : ℕ) : Fock R →ₗ[R] Fock R :=
  KernelRectangle.projection (Fock.basis R) (fun I : Index L => I.val)

theorem finiteProjection_basis {L : ℕ} (I : Finset ℕ) (hI : I ⊆ Finset.range L) :
    finiteProjection R L (Fock.basis R I) = Fock.basis R I :=
  KernelRectangle.projection_basis (Fock.basis R) (fun I : Index L => I.val)
    Subtype.val_injective ⟨I, Finset.mem_powerset.mpr hI⟩

theorem finiteProjection_create_basis {L i : ℕ} (hi : i < L) (I : Index L) :
    finiteProjection R L (Fock.create R i (Fock.basis R I.val)) =
      Fock.create R i (Fock.basis R I.val) := by
  by_cases hmem : i ∈ I.val
  · simp only [Fock.create_basis_of_mem R hmem, map_zero]
  · obtain ⟨ε, hε⟩ := Fock.create_basis_of_not_mem R hmem
    rw [hε, Units.smul_def, map_zsmul]
    rw [finiteProjection_basis R (insert i I.val)
      (Finset.insert_subset (Finset.mem_range.mpr hi) (Finset.mem_powerset.mp I.property))]

theorem finiteProjection_contract_basis {L : ℕ} (i : ℕ) (I : Index L) :
    finiteProjection R L (Fock.contract R i (Fock.basis R I.val)) =
      Fock.contract R i (Fock.basis R I.val) := by
  by_cases hmem : i ∈ I.val
  · obtain ⟨ε, hε⟩ := Fock.contract_basis_of_mem R hmem
    rw [hε, Units.smul_def, map_zsmul]
    rw [finiteProjection_basis R (I.val.erase i)
      ((Finset.erase_subset i I.val).trans (Finset.mem_powerset.mp I.property))]
  · simp only [Fock.contract_basis_of_not_mem R hmem, map_zero]

theorem finiteProjection_operator {L : ℕ} (T : Fock R →ₗ[R] Fock R)
    (hT : ∀ I : Index L,
      finiteProjection R L (T (Fock.basis R I.val)) = T (Fock.basis R I.val))
    (v : Fock R) (hv : finiteProjection R L v = v) :
    finiteProjection R L (T v) = T v := by
  have hh := congrArg T hv
  calc
    finiteProjection R L (T v) = finiteProjection R L (T (finiteProjection R L v)) :=
      congrArg (finiteProjection R L) hh.symm
    _ = T (finiteProjection R L v) := by
      change finiteProjection R L (T (∑ I : Index L,
        (Fock.basis R).repr v I.val • Fock.basis R I.val)) =
        T (∑ I : Index L, (Fock.basis R).repr v I.val • Fock.basis R I.val)
      simp only [map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro I hI
      rw [hT I]
    _ = T v := hh

theorem finiteProjection_create {L i : ℕ} (hi : i < L) (v : Fock R)
    (hv : finiteProjection R L v = v) :
    finiteProjection R L (Fock.create R i v) = Fock.create R i v :=
  finiteProjection_operator R (Fock.create R i) (finiteProjection_create_basis R hi) v hv

theorem finiteProjection_contract {L : ℕ} (i : ℕ) (v : Fock R)
    (hv : finiteProjection R L v = v) :
    finiteProjection R L (Fock.contract R i v) = Fock.contract R i v :=
  finiteProjection_operator R (Fock.contract R i) (finiteProjection_contract_basis R i) v hv

theorem createVector_finiteVector (L : ℕ) (a : Fin L → R) (v : Fock R) :
    Fock.createVector R (finiteVector R L a) v = ∑ i, a i • Fock.create R i v := by
  simp only [Fock.createVector_apply, finiteVector, map_sum, map_smul,
    Finset.sum_mul, smul_mul_assoc, Fock.create_apply, Fock.generator]

theorem finiteProjection_createVector {L : ℕ} (a : Fin L → R) (v : Fock R)
    (hv : finiteProjection R L v = v) :
    finiteProjection R L (Fock.createVector R (finiteVector R L a) v) =
      Fock.createVector R (finiteVector R L a) v := by
  simp only [createVector_finiteVector, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [finiteProjection_create R i.isLt v hv]

theorem finiteProjection_contractVector {L : ℕ} (a : Fin L → R) (v : Fock R)
    (hv : finiteProjection R L v = v) :
    finiteProjection R L (Fock.contractVector R (finiteVector R L a) v) =
      Fock.contractVector R (finiteVector R L a) v := by
  simp only [contractVector_finiteVector, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [finiteProjection_contract R i v hv]

theorem finiteProjection_normalList {L : ℕ}
    (S : List ((Fin L → R) × (Fin L → R))) (v : Fock R)
    (hv : finiteProjection R L v = v) :
    finiteProjection R L (Fock.normalList R (plainList R L S) v) =
      Fock.normalList R (plainList R L S) v := by
  induction S generalizing v with
  | nil => simpa only [plainList, List.map_nil, Fock.normalList_nil, LinearMap.id_apply] using hv
  | cons a S ih =>
      simp only [plainList] at ih
      simp only [plainList, List.map_cons, Fock.normalList_cons, List.length_map, map_add, map_smul]
      rw [finiteProjection_createVector R a.1 _ (ih v hv)]
      rw [ih _ (finiteProjection_contractVector R a.2 v hv)]

def plainOperator (L : ℕ) (A : Index L) : Fock R →ₗ[R] Fock R :=
  Fock.normalList R (plainList R L (sourceWord R L A))

theorem finiteProjection_plainOperator {L : ℕ} (A : Index L) (v : Fock R)
    (hv : finiteProjection R L v = v) :
    finiteProjection R L (plainOperator R L A v) = plainOperator R L A v :=
  finiteProjection_normalList R _ v hv

theorem matrix_single_one_eq_operator {L : ℕ} (A I J : Index L) :
    matrix R L (Pi.single A 1) I J =
      (Fock.basis R).repr (plainOperator R L A (Fock.basis R J.val)) I.val := by
  simpa only [plainOperator, one_mul] using matrix_single_eq_normalList R L A I J 1

theorem matrix_single_mul {L : ℕ} (A B I J : Index L) :
    (matrix R L (Pi.single A 1) * matrix R L (Pi.single B 1)) I J =
      (Fock.basis R).repr
        (plainOperator R L A (plainOperator R L B (Fock.basis R J.val))) I.val := by
  classical
  rw [Matrix.mul_apply]
  simp_rw [matrix_single_one_eq_operator]
  have hcomp := KernelRectangle.coefficientMatrix_comp_projection (Fock.basis R)
    (fun I : Index L => I.val) (plainOperator R L B) (plainOperator R L A) I J
  have hfixed := finiteProjection_plainOperator R B (Fock.basis R J.val)
    (finiteProjection_basis R J.val (Finset.mem_powerset.mp J.property))
  change (Fock.basis R).repr (plainOperator R L A
    (finiteProjection R L (plainOperator R L B (Fock.basis R J.val)))) I.val = _ at hcomp
  rw [hfixed] at hcomp
  rw [hcomp]
  apply Finset.sum_congr rfl
  intro k hk
  exact mul_comm _ _

end

end Lemmata.FockCircuits.FiniteIdentity
