module

public import Lemmata.FockCircuits.Exterior
public import Mathlib.Data.List.OfFn

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Fock

variable (R : Type*) [CommRing R]

@[simp] theorem basis_empty : basis R ∅ = 1 := by
  change (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).ExteriorAlgebra ∅ = 1
  rw [ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_empty)]
  simp [ExteriorAlgebra.ιMulti_family]

@[simp] theorem basis_singleton (i : ℕ) : basis R {i} = generator R i := by
  change (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).ExteriorAlgebra {i} = _
  rw [ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton i)]
  simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, generator]

theorem exteriorBasis_eq_sorted_prod {M ι : Type*} [AddCommGroup M] [Module R M]
    [LinearOrder ι] (b : Module.Basis ι R M) (I : Finset ι) :
    b.ExteriorAlgebra I =
      (I.sort.map fun i => ExteriorAlgebra.ι R (b i)).prod := by
  rw [ExteriorAlgebra.basis_apply]
  change ExteriorAlgebra.ιMulti R I.card (fun j => b (I.orderEmbOfFin rfl j)) = _
  rw [ExteriorAlgebra.ιMulti_apply,
    List.ofFn_comp' (I.orderEmbOfFin rfl) (fun i => ExteriorAlgebra.ι R (b i))]
  have hsort : List.ofFn (I.orderEmbOfFin rfl) = I.sort := by
    rw [List.ofFn_eq_map]
    exact Finset.listMap_orderEmbOfFin_finRange I rfl
  rw [hsort]

theorem basis_eq_sorted_prod (I : Finset ℕ) :
    basis R I = (I.sort.map (generator R)).prod := by
  change (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).ExteriorAlgebra I =
    (I.sort.map fun i => ExteriorAlgebra.ι R (Finsupp.single i 1)).prod
  simpa only [Finsupp.coe_basisSingleOne] using
    exteriorBasis_eq_sorted_prod R
      (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)) I

theorem basis_mul_of_not_disjoint {I J : Finset ℕ} (h : ¬Disjoint I J) :
    basis R I * basis R J = 0 := by
  exact ExteriorAlgebra.basis_mul_of_not_disjoint
    (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R))
    (Set.powersetCard.ofCard (s := I) rfl) (Set.powersetCard.ofCard (s := J) rfl) h

theorem basis_mul_of_disjoint {I J : Finset ℕ} (h : Disjoint I J) :
    ∃ ε : ℤˣ, basis R I * basis R J = ε • basis R (I ∪ J) := by
  have hd : Disjoint
      (Set.powersetCard.ofCard (s := I) rfl).val
      (Set.powersetCard.ofCard (s := J) rfl).val := h
  refine ⟨(Set.powersetCard.permOfDisjoint hd).sign, ?_⟩
  simpa only [basis, Set.powersetCard.coe_disjUnion, Finset.disjUnion_eq_union,
    Set.powersetCard.val_ofCard] using
    ExteriorAlgebra.basis_mul_of_disjoint
      (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R))
      (Set.powersetCard.ofCard (s := I) rfl)
      (Set.powersetCard.ofCard (s := J) rfl) hd

theorem create_basis_of_mem {i : ℕ} {I : Finset ℕ} (hi : i ∈ I) :
    create R i (basis R I) = 0 := by
  rw [create_apply, ← basis_singleton]
  exact basis_mul_of_not_disjoint R (by simpa using hi)

theorem create_basis_of_not_mem {i : ℕ} {I : Finset ℕ} (hi : i ∉ I) :
    ∃ ε : ℤˣ, create R i (basis R I) = ε • basis R (insert i I) := by
  obtain ⟨ε, hε⟩ := basis_mul_of_disjoint R
    (I := {i}) (J := I) (by simpa using hi)
  exact ⟨ε, by simpa only [basis_singleton, create_apply, Finset.singleton_union] using hε⟩

theorem contract_basis_of_not_mem {i : ℕ} {I : Finset ℕ} (hi : i ∉ I) :
    contract R i (basis R I) = 0 := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert j I hj ih =>
    have hiI : i ∉ I := fun h => hi (Finset.mem_insert_of_mem h)
    have hij : i ≠ j := by
      intro h
      apply hi
      simp [h]
    obtain ⟨ε, hε⟩ := create_basis_of_not_mem R hj
    have hb : basis R (insert j I) = ε⁻¹ • create R j (basis R I) := by
      rw [hε]
      exact (inv_smul_smul ε (basis R (insert j I))).symm
    rw [hb, Units.smul_def, map_zsmul, contract_create, ite_eq_right hij, ih hiI]
    simp

theorem contract_basis_of_mem {i : ℕ} {I : Finset ℕ} (hi : i ∈ I) :
    ∃ ε : ℤˣ, contract R i (basis R I) = ε • basis R (I.erase i) := by
  obtain ⟨ε, hε⟩ := create_basis_of_not_mem R (Finset.notMem_erase i I)
  have hb : basis R I = ε⁻¹ • create R i (basis R (I.erase i)) := by
    rw [hε, Finset.insert_erase hi]
    exact (inv_smul_smul ε (basis R I)).symm
  refine ⟨ε⁻¹, ?_⟩
  rw [hb, Units.smul_def, map_zsmul, contract_create]
  simp [contract_basis_of_not_mem R (Finset.notMem_erase i I), Units.smul_def]

end Lemmata.FockCircuits.Fock
