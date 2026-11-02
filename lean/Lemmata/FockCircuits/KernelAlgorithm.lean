module

public import Lemmata.FockCircuits.KernelRectangle
public import Lemmata.FockCircuits.Shear
public import Lemmata.FockCircuits.PascalShears

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.KernelAlgorithm

open FiniteIdentity KernelRectangle

noncomputable section

variable (R : Type*) [CommRing R]

def particleEmbedding (rho : ℕ → ℕ) : OneParticle R →ₗ[R] OneParticle R :=
  Finsupp.linearCombination R fun i => Finsupp.single (rho i) 1

@[simp] theorem particleEmbedding_single (rho : ℕ → ℕ) (i : ℕ) :
    particleEmbedding R rho (Finsupp.single i 1) = Finsupp.single (rho i) 1 := by
  simp [particleEmbedding]

def algebraEmbedding (rho : ℕ → ℕ) : Fock R →ₐ[R] Fock R :=
  ExteriorAlgebra.map (particleEmbedding R rho)

@[simp] theorem algebraEmbedding_generator (rho : ℕ → ℕ) (i : ℕ) :
    algebraEmbedding R rho (Fock.generator R i) = Fock.generator R (rho i) := by
  simp [algebraEmbedding, Fock.generator]

theorem embedding_shear (rho : ℕ → ℕ) (hrho : Function.Injective rho)
    (a : R) (i j : ℕ) (v : Fock R) :
    Fock.shear R a (rho i) (rho j) (algebraEmbedding R rho v) =
      algebraEmbedding R rho (Fock.shear R a i j v) := by
  have hlinear : (Fock.shearLinear R a (rho i) (rho j)).comp (particleEmbedding R rho) =
      (particleEmbedding R rho).comp (Fock.shearLinear R a i j) := by
    apply (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).ext
    intro m
    simp only [Finsupp.coe_basisSingleOne, LinearMap.comp_apply, particleEmbedding_single,
      Fock.shearLinear_apply, map_add, map_smul, Finsupp.single_apply, hrho.eq_iff]
  have hhom : (Fock.shear R a (rho i) (rho j)).comp (algebraEmbedding R rho) =
      (algebraEmbedding R rho).comp (Fock.shear R a i j) := by
    simp only [Fock.shear, algebraEmbedding, ExteriorAlgebra.map_comp_map, hlinear]
  exact AlgHom.congr_fun hhom v

theorem embedding_shear_fixed (rho tau : ℕ → ℕ) (hdisj : ∀ i j, rho i ≠ tau j)
    (a : R) (i j : ℕ) (v : Fock R) :
    Fock.shear R a (rho i) (rho j) (algebraEmbedding R tau v) = algebraEmbedding R tau v := by
  have hlinear : (Fock.shearLinear R a (rho i) (rho j)).comp (particleEmbedding R tau) =
      particleEmbedding R tau := by
    apply (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).ext
    intro m
    simp only [Finsupp.coe_basisSingleOne, LinearMap.comp_apply, particleEmbedding_single,
      Fock.shearLinear_apply, Finsupp.single_apply, ite_eq_right (hdisj i m).symm,
      mul_zero, zero_smul, add_zero]
  have hhom : (Fock.shear R a (rho i) (rho j)).comp (algebraEmbedding R tau) =
      algebraEmbedding R tau := by
    simp only [Fock.shear, algebraEmbedding, ExteriorAlgebra.map_comp_map, hlinear]
  exact AlgHom.congr_fun hhom v

def rightInclusion : Fock R →ₐ[R] Fock R := algebraEmbedding R (fun i => 2 * i + 1)

theorem algebraEmbedding_even : algebraEmbedding R (fun i => 2 * i) = leftInclusion R := rfl

theorem algebraEmbedding_odd : algebraEmbedding R (fun i => 2 * i + 1) = rightInclusion R := rfl

@[simp] theorem rightInclusion_generator (i : ℕ) :
    rightInclusion R (Fock.generator R i) = TwoColour.right R i := by
  simp [rightInclusion, TwoColour.right]

theorem rightInclusion_basis (I : Finset ℕ) :
    rightInclusion R (Fock.basis R I) = colourBasis R (colourIndex ∅ I) := by
  rw [Fock.basis_eq_sorted_prod, map_list_prod, colourBasis_right_word, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  exact rightInclusion_generator R i

theorem colourBasis_product (I J : Finset ℕ) :
    colourBasis R (colourIndex I J) = leftInclusion R (Fock.basis R I) *
      rightInclusion R (Fock.basis R J) := by
  rw [leftInclusion_basis, rightInclusion_basis, colourBasis_split]

theorem left_shear_colourBasis (a : R) (i j : ℕ) (I J : Finset ℕ) :
    Fock.shear R a (2 * i) (2 * j) (colourBasis R (colourIndex I J)) =
      leftInclusion R (Fock.shear R a i j (Fock.basis R I)) *
        rightInclusion R (Fock.basis R J) := by
  rw [colourBasis_product, map_mul]
  have hleft := embedding_shear R (fun i => 2 * i)
    (fun p q h => by change 2 * p = 2 * q at h; omega) a i j (Fock.basis R I)
  have hright := embedding_shear_fixed R (fun i => 2 * i) (fun i => 2 * i + 1)
    (fun _ _ => by omega) a i j (Fock.basis R J)
  change Fock.shear R a (2 * i) (2 * j) (algebraEmbedding R (fun i => 2 * i) (Fock.basis R I)) *
    Fock.shear R a (2 * i) (2 * j) (algebraEmbedding R (fun i => 2 * i + 1) (Fock.basis R J)) = _
  rw [hleft, hright, algebraEmbedding_even, algebraEmbedding_odd]

theorem right_shear_colourBasis (a : R) (i j : ℕ) (I J : Finset ℕ) :
    Fock.shear R a (2 * i + 1) (2 * j + 1) (colourBasis R (colourIndex I J)) =
      leftInclusion R (Fock.basis R I) *
        rightInclusion R (Fock.shear R a i j (Fock.basis R J)) := by
  rw [colourBasis_product, map_mul]
  have hleft := embedding_shear_fixed R (fun i => 2 * i + 1) (fun i => 2 * i)
    (fun _ _ => by omega) a i j (Fock.basis R I)
  have hright := embedding_shear R (fun i => 2 * i + 1)
    (fun p q h => by change 2 * p + 1 = 2 * q + 1 at h; omega)
    a i j (Fock.basis R J)
  change Fock.shear R a (2 * i + 1) (2 * j + 1) (algebraEmbedding R (fun i => 2 * i) (Fock.basis R I)) *
    Fock.shear R a (2 * i + 1) (2 * j + 1) (algebraEmbedding R (fun i => 2 * i + 1) (Fock.basis R J)) = _
  rw [hleft, hright, algebraEmbedding_even, algebraEmbedding_odd]

theorem left_shear_basis_sparse (a : R) (i j : ℕ) (I J : Finset ℕ) :
    ∃ I' : Finset ℕ, ∃ c : R,
      Fock.shear R a (2 * i) (2 * j) (colourBasis R (colourIndex I J)) =
        colourBasis R (colourIndex I J) + c • colourBasis R (colourIndex I' J) ∧
      (c = 0 ∨ doubledEnergy I' + 2 * i = doubledEnergy I + 2 * j) := by
  obtain ⟨I', c, h, henergy⟩ := Fock.shear_basis_sparse_energy R a i j I
  refine ⟨I', c, ?_, henergy⟩
  rw [left_shear_colourBasis, h, map_add, map_smul, add_mul, smul_mul_assoc]
  simp only [← colourBasis_product]

theorem right_shear_basis_sparse (a : R) (i j : ℕ) (I J : Finset ℕ) :
    ∃ J' : Finset ℕ, ∃ c : R,
      Fock.shear R a (2 * i + 1) (2 * j + 1) (colourBasis R (colourIndex I J)) =
        colourBasis R (colourIndex I J) + c • colourBasis R (colourIndex I J') ∧
      (c = 0 ∨ doubledEnergy J' + 2 * i = doubledEnergy J + 2 * j) := by
  obtain ⟨J', c, h, henergy⟩ := Fock.shear_basis_sparse_energy R a i j J
  refine ⟨J', c, ?_, henergy⟩
  rw [right_shear_colourBasis, h, map_add, map_smul, mul_add, mul_smul_comm]
  simp only [← colourBasis_product]

theorem algebraEmbedding_basis (rho : ℕ → ℕ) (hrho : StrictMono rho) (I : Finset ℕ) :
    algebraEmbedding R rho (Fock.basis R I) = Fock.basis R (I.image rho) := by
  rw [Fock.basis_eq_sorted_prod, map_list_prod, Fock.basis_eq_sorted_prod,
    sort_image_strictMono rho hrho]
  simp only [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  exact algebraEmbedding_generator R rho i

def rawIndex (I J : Finset ℕ) : Finset ℕ :=
  I.image (fun i => 2 * i) ∪ J.image (fun j => 2 * j + 1)

theorem colourBasis_unit_raw (I J : Finset ℕ) :
    ∃ u : ℤˣ, colourBasis R (colourIndex I J) =
      (((u : ℤ) : R)) • Fock.basis R (rawIndex I J) := by
  have hleft : leftInclusion R (Fock.basis R I) = Fock.basis R (I.image (fun i => 2 * i)) :=
    algebraEmbedding_basis R (fun i => 2 * i) (fun p q h => by change 2 * p < 2 * q; omega) I
  have hright : rightInclusion R (Fock.basis R J) = Fock.basis R (J.image (fun j => 2 * j + 1)) :=
    algebraEmbedding_basis R (fun i => 2 * i + 1)
      (fun p q h => by change 2 * p + 1 < 2 * q + 1; omega) J
  have hdisj : Disjoint (I.image (fun i => 2 * i)) (J.image (fun j => 2 * j + 1)) := by
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hk
    obtain ⟨j, hj, ho⟩ := Finset.mem_image.mp hk'
    omega
  rw [colourBasis_product, hleft, hright]
  obtain ⟨u, hu⟩ := Fock.basis_mul_of_disjoint R hdisj
  refine ⟨u, ?_⟩
  simpa only [rawIndex, Units.smul_def, ← Int.cast_smul_eq_zsmul R] using hu

theorem transfer_raw_sparse (T : Fock R →ₗ[R] Fock R)
    (I J I' J' : Finset ℕ) (c : R)
    (hT : T (Fock.basis R (rawIndex I J)) =
      Fock.basis R (rawIndex I J) + c • Fock.basis R (rawIndex I' J')) :
    ∃ c' : R, T (colourBasis R (colourIndex I J)) =
      colourBasis R (colourIndex I J) + c' • colourBasis R (colourIndex I' J') := by
  obtain ⟨u, hu⟩ := colourBasis_unit_raw R I J
  obtain ⟨v, hv⟩ := colourBasis_unit_raw R I' J'
  let a : R := ((u : ℤ) : R)
  let b : R := (((v⁻¹ : ℤˣ) : ℤ) : R)
  have hcancel : b * ((v : ℤ) : R) = 1 := by
    dsimp [b]
    rw [← Int.cast_mul, ← Units.val_mul]
    simp
  have hinv : Fock.basis R (rawIndex I' J') = b • colourBasis R (colourIndex I' J') := by
    rw [hv, smul_smul, hcancel, one_smul]
  refine ⟨a * c * b, ?_⟩
  calc
    T (colourBasis R (colourIndex I J)) = a • T (Fock.basis R (rawIndex I J)) := by
      rw [hu, map_smul]
    _ = a • Fock.basis R (rawIndex I J) +
        (a * c) • Fock.basis R (rawIndex I' J') := by rw [hT, smul_add, smul_smul]
    _ = colourBasis R (colourIndex I J) +
        (a * c) • (b • colourBasis R (colourIndex I' J')) := by rw [← hu, hinv]
    _ = _ := by rw [smul_smul]

@[simp] theorem mem_rawIndex_even (I J : Finset ℕ) (m : ℕ) :
    2 * m ∈ rawIndex I J ↔ m ∈ I := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp h
      have : i = m := by omega
      simpa only [this] using hi
    · obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
      omega
  · intro h
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨m, h, rfl⟩))

@[simp] theorem mem_rawIndex_odd (I J : Finset ℕ) (m : ℕ) :
    2 * m + 1 ∈ rawIndex I J ↔ m ∈ J := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp h
      omega
    · obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
      have : j = m := by omega
      simpa only [this] using hj
  · intro h
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨m, h, rfl⟩))

theorem rawIndex_right_split (I J : Finset ℕ) (m : ℕ) :
    insert (2 * m) ((rawIndex I J).erase (2 * m + 1)) = rawIndex (insert m I) (J.erase m) := by
  have heven : 2 * m + 1 ∉ I.image (fun i => 2 * i) := by
    intro h
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp h
    omega
  simp only [rawIndex, Finset.erase_union_distrib, Finset.erase_eq_of_notMem heven,
    ← Finset.image_erase (fun p q h => by change 2 * p + 1 = 2 * q + 1 at h; omega :
      Function.Injective (fun i : ℕ => 2 * i + 1)),
    Finset.image_insert, Finset.insert_union]

theorem rawIndex_left_split (I J : Finset ℕ) (m : ℕ) :
    insert (2 * m + 1) ((rawIndex I J).erase (2 * m)) = rawIndex (I.erase m) (insert m J) := by
  have hodd : 2 * m ∉ J.image (fun j => 2 * j + 1) := by
    intro h
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
    omega
  simp only [rawIndex, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hodd,
    ← Finset.image_erase (fun p q h => by change 2 * p = 2 * q at h; omega :
      Function.Injective (fun i : ℕ => 2 * i)),
    Finset.image_insert, Finset.union_insert]

theorem shear_basis_replacement (a : R) {i j : ℕ} {I : Finset ℕ}
    (hi : i ∈ I) (hj : j ∉ I.erase i) :
    ∃ c : R, Fock.shear R a i j (Fock.basis R I) =
      Fock.basis R I + c • Fock.basis R (insert j (I.erase i)) := by
  rw [Fock.shear_apply]
  obtain ⟨u, hu⟩ := Fock.contract_basis_of_mem R hi
  rw [hu, mul_smul_comm]
  obtain ⟨v, hv⟩ := Fock.create_basis_of_not_mem R hj
  simp only [Fock.create_apply] at hv
  rw [hv]
  refine ⟨a * (u : ℤ) * (v : ℤ), ?_⟩
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul R, smul_smul, mul_assoc]

theorem shear_basis_fixed_of_absent (a : R) {i : ℕ} (j : ℕ) {I : Finset ℕ}
    (hi : i ∉ I) : Fock.shear R a i j (Fock.basis R I) = Fock.basis R I := by
  rw [Fock.shear_apply, Fock.contract_basis_of_not_mem R hi]
  simp

theorem shear_basis_fixed_of_present (a : R) {i j : ℕ} {I : Finset ℕ}
    (hi : i ∈ I) (hj : j ∈ I.erase i) :
    Fock.shear R a i j (Fock.basis R I) = Fock.basis R I := by
  rw [Fock.shear_apply]
  obtain ⟨u, hu⟩ := Fock.contract_basis_of_mem R hi
  rw [hu, mul_smul_comm]
  have hz := Fock.create_basis_of_mem R hj
  simp only [Fock.create_apply] at hz
  rw [hz]
  simp

theorem split_right_sparse (m : ℕ) (I J : Finset ℕ) :
    ∃ I' J' : Finset ℕ, ∃ c : R,
      Fock.shear R 1 (2 * m + 1) (2 * m) (colourBasis R (colourIndex I J)) =
        colourBasis R (colourIndex I J) + c • colourBasis R (colourIndex I' J') ∧
      doubledEnergy I ≤ doubledEnergy I' ∧ doubledEnergy J' ≤ doubledEnergy J := by
  by_cases hmJ : m ∈ J
  · by_cases hmI : m ∈ I
    · have hi : 2 * m + 1 ∈ rawIndex I J := (mem_rawIndex_odd I J m).mpr hmJ
      have hj : 2 * m ∈ (rawIndex I J).erase (2 * m + 1) :=
        Finset.mem_erase.mpr ⟨by omega, (mem_rawIndex_even I J m).mpr hmI⟩
      have hfix := shear_basis_fixed_of_present R 1 hi hj
      obtain ⟨c, hc⟩ := transfer_raw_sparse R
        (Fock.shear R 1 (2 * m + 1) (2 * m)).toLinearMap I J I J 0 (by simpa using hfix)
      exact ⟨I, J, c, hc, le_rfl, le_rfl⟩
    · have hi : 2 * m + 1 ∈ rawIndex I J := (mem_rawIndex_odd I J m).mpr hmJ
      have hj : 2 * m ∉ (rawIndex I J).erase (2 * m + 1) := by
        intro h
        exact hmI ((mem_rawIndex_even I J m).mp (Finset.mem_erase.mp h).2)
      obtain ⟨c, hc⟩ := shear_basis_replacement R 1 hi hj
      rw [rawIndex_right_split] at hc
      obtain ⟨c', hc'⟩ := transfer_raw_sparse R
        (Fock.shear R 1 (2 * m + 1) (2 * m)).toLinearMap I J (insert m I) (J.erase m) c hc
      refine ⟨insert m I, J.erase m, c', hc', ?_, ?_⟩
      · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert _ _) (fun _ _ _ => Nat.zero_le _)
      · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => Nat.zero_le _)
  · have hi : 2 * m + 1 ∉ rawIndex I J := by simpa only [mem_rawIndex_odd] using hmJ
    have hfix := shear_basis_fixed_of_absent R 1 (2 * m) hi
    obtain ⟨c, hc⟩ := transfer_raw_sparse R
      (Fock.shear R 1 (2 * m + 1) (2 * m)).toLinearMap I J I J 0 (by simpa using hfix)
    exact ⟨I, J, c, hc, le_rfl, le_rfl⟩

theorem split_left_sparse (m : ℕ) (I J : Finset ℕ) :
    ∃ I' J' : Finset ℕ, ∃ c : R,
      Fock.shear R 1 (2 * m) (2 * m + 1) (colourBasis R (colourIndex I J)) =
        colourBasis R (colourIndex I J) + c • colourBasis R (colourIndex I' J') ∧
      doubledEnergy I' ≤ doubledEnergy I ∧ doubledEnergy J ≤ doubledEnergy J' := by
  by_cases hmI : m ∈ I
  · by_cases hmJ : m ∈ J
    · have hi : 2 * m ∈ rawIndex I J := (mem_rawIndex_even I J m).mpr hmI
      have hj : 2 * m + 1 ∈ (rawIndex I J).erase (2 * m) :=
        Finset.mem_erase.mpr ⟨by omega, (mem_rawIndex_odd I J m).mpr hmJ⟩
      have hfix := shear_basis_fixed_of_present R 1 hi hj
      obtain ⟨c, hc⟩ := transfer_raw_sparse R
        (Fock.shear R 1 (2 * m) (2 * m + 1)).toLinearMap I J I J 0 (by simpa using hfix)
      exact ⟨I, J, c, hc, le_rfl, le_rfl⟩
    · have hi : 2 * m ∈ rawIndex I J := (mem_rawIndex_even I J m).mpr hmI
      have hj : 2 * m + 1 ∉ (rawIndex I J).erase (2 * m) := by
        intro h
        exact hmJ ((mem_rawIndex_odd I J m).mp (Finset.mem_erase.mp h).2)
      obtain ⟨c, hc⟩ := shear_basis_replacement R 1 hi hj
      rw [rawIndex_left_split] at hc
      obtain ⟨c', hc'⟩ := transfer_raw_sparse R
        (Fock.shear R 1 (2 * m) (2 * m + 1)).toLinearMap I J (I.erase m) (insert m J) c hc
      refine ⟨I.erase m, insert m J, c', hc', ?_, ?_⟩
      · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => Nat.zero_le _)
      · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert _ _) (fun _ _ _ => Nat.zero_le _)
  · have hi : 2 * m ∉ rawIndex I J := by simpa only [mem_rawIndex_even] using hmI
    have hfix := shear_basis_fixed_of_absent R 1 (2 * m + 1) hi
    obtain ⟨c, hc⟩ := transfer_raw_sparse R
      (Fock.shear R 1 (2 * m) (2 * m + 1)).toLinearMap I J I J 0 (by simpa using hfix)
    exact ⟨I, J, c, hc, le_rfl, le_rfl⟩

theorem exists_left_shear_circuit {X : Type*} (U V : ℕ) (a : R) (i j : ℕ)
    (bank : CircuitFamily R X (Index U V)) :
    ∃ p : CircuitFamily R X (Index U V),
      p.size = bank.size + 2 * stateCount U * stateCount V ∧
      Represents (colourBasis R) (basisIndex (U := U) (V := V)) bank p
        ((projection (colourBasis R) (basisIndex (U := U) (V := V))).comp (Fock.shear R a (2 * i) (2 * j)).toLinearMap) := by
  obtain ⟨p, hsize, hp⟩ := exists_projected_sparse_circuit (colourBasis R) (basisIndex (U := U) (V := V))
    (basisIndex_injective U V) (Fock.shear R a (2 * i) (2 * j)).toLinearMap bank (by
      intro d
      obtain ⟨I', c, hc, _⟩ := left_shear_basis_sparse R a i j d.1.val d.2.val
      exact ⟨colourIndex I' d.2.val, c, hc⟩)
  exact ⟨p, by simpa only [card_index, Nat.mul_assoc] using hsize, hp⟩

theorem exists_right_shear_circuit {X : Type*} (U V : ℕ) (a : R) (i j : ℕ)
    (bank : CircuitFamily R X (Index U V)) :
    ∃ p : CircuitFamily R X (Index U V),
      p.size = bank.size + 2 * stateCount U * stateCount V ∧
      Represents (colourBasis R) (basisIndex (U := U) (V := V)) bank p
        ((projection (colourBasis R) (basisIndex (U := U) (V := V))).comp
          (Fock.shear R a (2 * i + 1) (2 * j + 1)).toLinearMap) := by
  obtain ⟨p, hsize, hp⟩ := exists_projected_sparse_circuit (colourBasis R) (basisIndex (U := U) (V := V))
    (basisIndex_injective U V) (Fock.shear R a (2 * i + 1) (2 * j + 1)).toLinearMap bank (by
      intro d
      obtain ⟨J', c, hc, _⟩ := right_shear_basis_sparse R a i j d.1.val d.2.val
      exact ⟨colourIndex d.1.val J', c, hc⟩)
  exact ⟨p, by simpa only [card_index, Nat.mul_assoc] using hsize, hp⟩

theorem exists_right_split_circuit {X : Type*} (U V m : ℕ)
    (bank : CircuitFamily R X (Index U V)) :
    ∃ p : CircuitFamily R X (Index U V),
      p.size = bank.size + 2 * stateCount U * stateCount V ∧
      Represents (colourBasis R) (basisIndex (U := U) (V := V)) bank p
        ((projection (colourBasis R) (basisIndex (U := U) (V := V))).comp
          (Fock.shear R 1 (2 * m + 1) (2 * m)).toLinearMap) := by
  obtain ⟨p, hsize, hp⟩ := exists_projected_sparse_circuit (colourBasis R) (basisIndex (U := U) (V := V))
    (basisIndex_injective U V) (Fock.shear R 1 (2 * m + 1) (2 * m)).toLinearMap bank (by
      intro d
      obtain ⟨I', J', c, hc, _, _⟩ := split_right_sparse R m d.1.val d.2.val
      exact ⟨colourIndex I' J', c, hc⟩)
  exact ⟨p, by simpa only [card_index, Nat.mul_assoc] using hsize, hp⟩

theorem exists_left_split_circuit {X : Type*} (U V m : ℕ)
    (bank : CircuitFamily R X (Index U V)) :
    ∃ p : CircuitFamily R X (Index U V),
      p.size = bank.size + 2 * stateCount U * stateCount V ∧
      Represents (colourBasis R) (basisIndex (U := U) (V := V)) bank p
        ((projection (colourBasis R) (basisIndex (U := U) (V := V))).comp
          (Fock.shear R 1 (2 * m) (2 * m + 1)).toLinearMap) := by
  obtain ⟨p, hsize, hp⟩ := exists_projected_sparse_circuit (colourBasis R) (basisIndex (U := U) (V := V))
    (basisIndex_injective U V) (Fock.shear R 1 (2 * m) (2 * m + 1)).toLinearMap bank (by
      intro d
      obtain ⟨I', J', c, hc, _, _⟩ := split_left_sparse R m d.1.val d.2.val
      exact ⟨colourIndex I' J', c, hc⟩)
  exact ⟨p, by simpa only [card_index, Nat.mul_assoc] using hsize, hp⟩

theorem rawIndex_pair_insert (I J : Finset ℕ) (m : ℕ) :
    insert (2 * m) (insert (2 * m + 1) (rawIndex I J)) = rawIndex (insert m I) (insert m J) := by
  simp only [rawIndex, Finset.image_insert, Finset.insert_union, Finset.union_insert,
    Finset.insert_comm]

theorem factor_basis_formula (m : ℕ) (K : Finset ℕ) :
    Fock.basis R K * TwoColour.factor R m = Fock.basis R K +
      TwoColour.left R m * (TwoColour.right R m * Fock.basis R K) := by
  have hcomm : Commute (TwoColour.factor R m) (Fock.basis R K) := by
    rw [Fock.basis_eq_sorted_prod]
    apply Commute.list_prod_right
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact TwoColour.factor_commutes_generator R m i
  rw [← hcomm.eq]
  simp only [TwoColour.factor, add_mul, one_mul, mul_assoc]

theorem factor_basis_raw (m : ℕ) (K : Finset ℕ)
    (ho : 2 * m + 1 ∉ K) (he : 2 * m ∉ K) :
    ∃ c : R, (LinearMap.mulRight R (TwoColour.factor R m)) (Fock.basis R K) =
      Fock.basis R K + c • Fock.basis R (insert (2 * m) (insert (2 * m + 1) K)) := by
  obtain ⟨u, hu⟩ := Fock.create_basis_of_not_mem R ho
  have hnew : 2 * m ∉ insert (2 * m + 1) K := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · omega
    · exact he h
  obtain ⟨v, hv⟩ := Fock.create_basis_of_not_mem R hnew
  change TwoColour.right R m * Fock.basis R K = u • Fock.basis R (insert (2 * m + 1) K) at hu
  change TwoColour.left R m * Fock.basis R (insert (2 * m + 1) K) =
    v • Fock.basis R (insert (2 * m) (insert (2 * m + 1) K)) at hv
  refine ⟨((u : ℤ) : R) * ((v : ℤ) : R), ?_⟩
  change Fock.basis R K * TwoColour.factor R m = _
  rw [factor_basis_formula, hu, mul_smul_comm, hv]
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul R, smul_smul]

theorem factor_basis_fixed_of_odd (m : ℕ) {K : Finset ℕ} (ho : 2 * m + 1 ∈ K) :
    (LinearMap.mulRight R (TwoColour.factor R m)) (Fock.basis R K) = Fock.basis R K := by
  have hz := Fock.create_basis_of_mem R ho
  change TwoColour.right R m * Fock.basis R K = 0 at hz
  change Fock.basis R K * TwoColour.factor R m = _
  rw [factor_basis_formula, hz]
  simp

theorem factor_basis_fixed_of_even (m : ℕ) {K : Finset ℕ}
    (ho : 2 * m + 1 ∉ K) (he : 2 * m ∈ K) :
    (LinearMap.mulRight R (TwoColour.factor R m)) (Fock.basis R K) = Fock.basis R K := by
  obtain ⟨u, hu⟩ := Fock.create_basis_of_not_mem R ho
  have he' : 2 * m ∈ insert (2 * m + 1) K := Finset.mem_insert_of_mem he
  have hz := Fock.create_basis_of_mem R he'
  change TwoColour.right R m * Fock.basis R K = u • Fock.basis R (insert (2 * m + 1) K) at hu
  change TwoColour.left R m * Fock.basis R (insert (2 * m + 1) K) = 0 at hz
  change Fock.basis R K * TwoColour.factor R m = _
  rw [factor_basis_formula, hu, mul_smul_comm, hz]
  simp

theorem factor_sparse (m : ℕ) (I J : Finset ℕ) :
    ∃ I' J' : Finset ℕ, ∃ c : R,
      (LinearMap.mulRight R (TwoColour.factor R m)) (colourBasis R (colourIndex I J)) =
        colourBasis R (colourIndex I J) + c • colourBasis R (colourIndex I' J') ∧
      doubledEnergy I ≤ doubledEnergy I' ∧ doubledEnergy J ≤ doubledEnergy J' := by
  by_cases hmJ : m ∈ J
  · have hfix := factor_basis_fixed_of_odd R m ((mem_rawIndex_odd I J m).mpr hmJ)
    obtain ⟨c, hc⟩ := transfer_raw_sparse R (LinearMap.mulRight R (TwoColour.factor R m))
      I J I J 0 (by simpa using hfix)
    exact ⟨I, J, c, hc, le_rfl, le_rfl⟩
  · by_cases hmI : m ∈ I
    · have hfix := factor_basis_fixed_of_even R m
        (by simpa only [mem_rawIndex_odd] using hmJ) ((mem_rawIndex_even I J m).mpr hmI)
      obtain ⟨c, hc⟩ := transfer_raw_sparse R (LinearMap.mulRight R (TwoColour.factor R m))
        I J I J 0 (by simpa using hfix)
      exact ⟨I, J, c, hc, le_rfl, le_rfl⟩
    · obtain ⟨c, hc⟩ := factor_basis_raw R m (rawIndex I J)
        (by simpa only [mem_rawIndex_odd] using hmJ) (by simpa only [mem_rawIndex_even] using hmI)
      rw [rawIndex_pair_insert] at hc
      obtain ⟨c', hc'⟩ := transfer_raw_sparse R (LinearMap.mulRight R (TwoColour.factor R m))
        I J (insert m I) (insert m J) c hc
      refine ⟨insert m I, insert m J, c', hc', ?_, ?_⟩
      · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert _ _) (fun _ _ _ => Nat.zero_le _)
      · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert _ _) (fun _ _ _ => Nat.zero_le _)

theorem exists_factor_circuit {X : Type*} (U V m : ℕ)
    (bank : CircuitFamily R X (Index U V)) :
    ∃ p : CircuitFamily R X (Index U V),
      p.size = bank.size + 2 * stateCount U * stateCount V ∧
      Represents (colourBasis R) (basisIndex (U := U) (V := V)) bank p
        ((projection (colourBasis R) (basisIndex (U := U) (V := V))).comp
          (LinearMap.mulRight R (TwoColour.factor R m))) := by
  obtain ⟨p, hsize, hp⟩ := exists_projected_sparse_circuit (colourBasis R)
    (basisIndex (U := U) (V := V)) (basisIndex_injective U V)
    (LinearMap.mulRight R (TwoColour.factor R m)) bank (by
      intro d
      obtain ⟨I', J', c, hc, _, _⟩ := factor_sparse R m d.1.val d.2.val
      exact ⟨colourIndex I' J', c, hc⟩)
  exact ⟨p, by simpa only [card_index, Nat.mul_assoc] using hsize, hp⟩

def diagonalParticle (a : ℕ → R) : OneParticle R →ₗ[R] OneParticle R :=
  Finsupp.linearCombination R fun i => a i • Finsupp.single i 1

@[simp] theorem diagonalParticle_single (a : ℕ → R) (i : ℕ) :
    diagonalParticle R a (Finsupp.single i 1) = a i • Finsupp.single i 1 := by
  simp [diagonalParticle]

def diagonalMap (a : ℕ → R) : Fock R →ₐ[R] Fock R := ExteriorAlgebra.map (diagonalParticle R a)

@[simp] theorem diagonalMap_generator (a : ℕ → R) (i : ℕ) :
    diagonalMap R a (Fock.generator R i) = a i • Fock.generator R i := by
  simp only [diagonalMap, Fock.generator, ExteriorAlgebra.map_apply_ι,
    diagonalParticle_single, map_smul]

theorem scalar_word (a : ℕ → R) (b : ℕ → Fock R) (L : List ℕ) :
    (L.map fun i => a i • b i).prod = (L.map a).prod • (L.map b).prod := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.prod_cons, ih, smul_mul_assoc, mul_smul_comm,
      smul_smul, mul_comm]

theorem diagonalMap_basis (a : ℕ → R) (I : Finset ℕ) :
    diagonalMap R a (Fock.basis R I) = (I.sort.map a).prod • Fock.basis R I := by
  simpa only [Fock.basis_eq_sorted_prod, map_list_prod, List.map_map,
    Function.comp_def, diagonalMap_generator] using scalar_word R a (Fock.generator R) I.sort

theorem diagonal_embedding (a : ℕ → R) (rho : ℕ → ℕ) (v : Fock R) :
    diagonalMap R a (algebraEmbedding R rho v) =
      algebraEmbedding R rho (diagonalMap R (a ∘ rho) v) := by
  have hlinear : (diagonalParticle R a).comp (particleEmbedding R rho) =
      (particleEmbedding R rho).comp (diagonalParticle R (a ∘ rho)) := by
    apply (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).ext
    intro i
    simp only [Finsupp.coe_basisSingleOne, LinearMap.comp_apply, particleEmbedding_single,
      diagonalParticle_single, map_smul, Function.comp_apply]
  have hhom : (diagonalMap R a).comp (algebraEmbedding R rho) =
      (algebraEmbedding R rho).comp (diagonalMap R (a ∘ rho)) := by
    simp only [diagonalMap, algebraEmbedding, ExteriorAlgebra.map_comp_map, hlinear]
  exact AlgHom.congr_fun hhom v

theorem diagonalMap_one : diagonalMap R (fun _ => 1) = AlgHom.id R (Fock R) := by
  have hlinear : diagonalParticle R (fun _ => 1) = LinearMap.id := by
    apply (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).ext
    intro i
    simp
  rw [diagonalMap, hlinear, ExteriorAlgebra.map_id]

theorem diagonalMap_sign : diagonalMap R (fun i => (-1 : R) ^ i) =
    ExteriorAlgebra.map (Fock.signDiagonal R) := rfl

def colourSignCoefficient (right : Bool) (k : ℕ) : R :=
  if k % 2 = (if right then 1 else 0) then (-1 : R) ^ (k / 2) else 1

@[simp] theorem colourSignCoefficient_even (right : Bool) (i : ℕ) :
    colourSignCoefficient R right (2 * i) = if right then 1 else (-1 : R) ^ i := by
  have hmod : (2 * i) % 2 = 0 := by omega
  have hdiv : (2 * i) / 2 = i := by omega
  cases right <;> simp [colourSignCoefficient, hmod, hdiv]

@[simp] theorem colourSignCoefficient_odd (right : Bool) (i : ℕ) :
    colourSignCoefficient R right (2 * i + 1) = if right then (-1 : R) ^ i else 1 := by
  have hmod : (2 * i + 1) % 2 = 1 := by omega
  have hdiv : (2 * i + 1) / 2 = i := by omega
  cases right <;> simp [colourSignCoefficient, hmod, hdiv]

def colourSign (right : Bool) : Fock R →ₐ[R] Fock R := diagonalMap R (colourSignCoefficient R right)

theorem colourSign_left (v : Fock R) :
    colourSign R false (leftInclusion R v) =
      leftInclusion R (ExteriorAlgebra.map (Fock.signDiagonal R) v) := by
  have h := diagonal_embedding R (colourSignCoefficient R false) (fun i => 2 * i) v
  have hcoef : colourSignCoefficient R false ∘ (fun i => 2 * i) = fun i => (-1 : R) ^ i := by
    funext i
    simp [Function.comp_def]
  rw [hcoef, algebraEmbedding_even, diagonalMap_sign] at h
  exact h

theorem colourSign_left_fixes_right (v : Fock R) :
    colourSign R false (rightInclusion R v) = rightInclusion R v := by
  have h := diagonal_embedding R (colourSignCoefficient R false) (fun i => 2 * i + 1) v
  have hcoef : colourSignCoefficient R false ∘ (fun i => 2 * i + 1) = fun _ => 1 := by
    funext i
    simp [Function.comp_def]
  rw [hcoef, algebraEmbedding_odd, diagonalMap_one, AlgHom.id_apply] at h
  exact h

theorem colourSign_right (v : Fock R) :
    colourSign R true (rightInclusion R v) =
      rightInclusion R (ExteriorAlgebra.map (Fock.signDiagonal R) v) := by
  have h := diagonal_embedding R (colourSignCoefficient R true) (fun i => 2 * i + 1) v
  have hcoef : colourSignCoefficient R true ∘ (fun i => 2 * i + 1) = fun i => (-1 : R) ^ i := by
    funext i
    simp [Function.comp_def]
  rw [hcoef, algebraEmbedding_odd, diagonalMap_sign] at h
  exact h

theorem colourSign_right_fixes_left (v : Fock R) :
    colourSign R true (leftInclusion R v) = leftInclusion R v := by
  have h := diagonal_embedding R (colourSignCoefficient R true) (fun i => 2 * i) v
  have hcoef : colourSignCoefficient R true ∘ (fun i => 2 * i) = fun _ => 1 := by
    funext i
    simp [Function.comp_def]
  rw [hcoef, algebraEmbedding_even, diagonalMap_one, AlgHom.id_apply] at h
  exact h

theorem diagonal_sparse (a : ℕ → R) (I J : Finset ℕ) :
    ∃ c : R, diagonalMap R a (colourBasis R (colourIndex I J)) =
      colourBasis R (colourIndex I J) + c • colourBasis R (colourIndex I J) := by
  apply transfer_raw_sparse R (diagonalMap R a).toLinearMap I J I J
    (((rawIndex I J).sort.map a).prod - 1)
  change diagonalMap R a (Fock.basis R (rawIndex I J)) = _
  rw [diagonalMap_basis]
  module

theorem exists_diagonal_circuit {X : Type*} (U V : ℕ) (a : ℕ → R)
    (bank : CircuitFamily R X (Index U V)) :
    ∃ p : CircuitFamily R X (Index U V),
      p.size = bank.size + 2 * stateCount U * stateCount V ∧
      Represents (colourBasis R) (basisIndex (U := U) (V := V)) bank p
        ((projection (colourBasis R) (basisIndex (U := U) (V := V))).comp
          (diagonalMap R a).toLinearMap) := by
  obtain ⟨p, hsize, hp⟩ := exists_projected_sparse_circuit (colourBasis R)
    (basisIndex (U := U) (V := V)) (basisIndex_injective U V) (diagonalMap R a).toLinearMap bank (by
      intro d
      obtain ⟨c, hc⟩ := diagonal_sparse R a d.1.val d.2.val
      exact ⟨colourIndex d.1.val d.2.val, c, hc⟩)
  exact ⟨p, by simpa only [card_index, Nat.mul_assoc] using hsize, hp⟩

end

end Lemmata.FockCircuits.KernelAlgorithm
