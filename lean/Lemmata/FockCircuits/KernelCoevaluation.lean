module

public import Lemmata.FockCircuits.FiniteIdentity
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lemmata.FockCircuits.FiniteIdentity

variable (R : Type*) [CommRing R]

theorem exteriorBasis_mul_ordered {M D : Type*} [AddCommGroup M] [Module R M]
    [LinearOrder D] (b : Module.Basis D R M) (I J : Finset D)
    (hIJ : ∀ i ∈ I, ∀ j ∈ J, i < j) :
    b.ExteriorAlgebra I * b.ExteriorAlgebra J = b.ExteriorAlgebra (I ∪ J) := by
  have hsort : (I ∪ J).sort = I.sort ++ J.sort := by
    apply (Finset.sortedLT_sort _).eq_of_mem_iff
    · exact List.sortedLT_append.mpr ⟨I.sortedLT_sort, J.sortedLT_sort,
        by simpa only [Finset.mem_sort] using hIJ⟩
    · intro d
      simp
  rw [Fock.exteriorBasis_eq_sorted_prod R b,
    Fock.exteriorBasis_eq_sorted_prod R b,
    Fock.exteriorBasis_eq_sorted_prod R b, hsort, List.map_append, List.prod_append]

@[simp] theorem colourBasis_empty : colourBasis R ∅ = 1 := by
  exact (Fock.exteriorBasis_eq_sorted_prod R _ ∅).trans (by simp)

theorem colourBasis_split (I J : Finset ℕ) :
    colourBasis R (colourIndex I ∅) * colourBasis R (colourIndex ∅ J) =
      colourBasis R (colourIndex I J) := by
  unfold colourBasis
  have hIJ : ∀ i ∈ colourIndex I ∅, ∀ j ∈ colourIndex ∅ J, i < j := by
    intro i hi j hj
    simp only [colourIndex, Finset.image_empty, Finset.union_empty,
      Finset.empty_union] at hi hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
    exact Sum.Lex.sep a b
  simpa only [colourIndex, Finset.image_empty, Finset.union_empty,
    Finset.empty_union] using exteriorBasis_mul_ordered R
      ((Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).reindex
        (Equiv.natSumNatEquivNat.symm.trans toLex))
      (colourIndex I ∅) (colourIndex ∅ J) hIJ

theorem sort_image_strictMono {D E : Type*} [LinearOrder D] [LinearOrder E]
    (f : D → E) (hf : StrictMono f) (I : Finset D) :
    (I.image f).sort = I.sort.map f := by
  apply (I.image f).sortedLT_sort.eq_of_mem_iff
    (hf.sortedLT_listMap.mpr I.sortedLT_sort)
  intro d
  simp

theorem colourBasis_left_word (I : Finset ℕ) :
    colourBasis R (colourIndex I ∅) = (I.sort.map (TwoColour.left R)).prod := by
  unfold colourBasis
  rw [Fock.exteriorBasis_eq_sorted_prod]
  simp only [colourIndex, Finset.image_empty, Finset.union_empty]
  rw [sort_image_strictMono (fun i : ℕ => toLex (Sum.inl i : ℕ ⊕ ℕ))
    (fun _ _ h => Sum.Lex.inl h) I]
  simp [List.map_map, Function.comp_def, Module.Basis.reindex_apply,
    Finsupp.coe_basisSingleOne, Equiv.natSumNatEquivNat_apply,
    TwoColour.left, Fock.generator]
  rfl

theorem colourBasis_right_word (I : Finset ℕ) :
    colourBasis R (colourIndex ∅ I) = (I.sort.map (TwoColour.right R)).prod := by
  unfold colourBasis
  rw [Fock.exteriorBasis_eq_sorted_prod]
  simp only [colourIndex, Finset.image_empty, Finset.empty_union]
  rw [sort_image_strictMono (fun i : ℕ => toLex (Sum.inr i : ℕ ⊕ ℕ))
    (fun _ _ h => Sum.Lex.inr h) I]
  simp [List.map_map, Function.comp_def, Module.Basis.reindex_apply,
    Finsupp.coe_basisSingleOne, Equiv.natSumNatEquivNat_apply,
    TwoColour.right, Fock.generator]
  rfl

noncomputable def leftParticle : OneParticle R →ₗ[R] OneParticle R :=
  Finsupp.linearCombination R fun i : ℕ => Finsupp.single (2 * i) 1

noncomputable def leftInclusion : Fock R →ₐ[R] Fock R :=
  ExteriorAlgebra.map (leftParticle R)

@[simp] theorem leftInclusion_generator (i : ℕ) :
    leftInclusion R (Fock.generator R i) = TwoColour.left R i := by
  simp [leftInclusion, leftParticle, Fock.generator, TwoColour.left]

theorem leftInclusion_basis (I : Finset ℕ) :
    leftInclusion R (Fock.basis R I) = colourBasis R (colourIndex I ∅) := by
  rw [Fock.basis_eq_sorted_prod, map_list_prod, colourBasis_left_word,
    List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  exact leftInclusion_generator R i

theorem colourIndex_eq_iff (I J K L : Finset ℕ) :
    colourIndex I J = colourIndex K L ↔ I = K ∧ J = L := by
  constructor
  · intro h
    constructor
    · apply Finset.ext
      intro i
      calc
        i ∈ I ↔ toLex (Sum.inl i : ℕ ⊕ ℕ) ∈ colourIndex I J := by simp [colourIndex]
        _ ↔ toLex (Sum.inl i : ℕ ⊕ ℕ) ∈ colourIndex K L := by rw [h]
        _ ↔ i ∈ K := by simp [colourIndex]
    · apply Finset.ext
      intro i
      calc
        i ∈ J ↔ toLex (Sum.inr i : ℕ ⊕ ℕ) ∈ colourIndex I J := by simp [colourIndex]
        _ ↔ toLex (Sum.inr i : ℕ ⊕ ℕ) ∈ colourIndex K L := by rw [h]
        _ ↔ i ∈ L := by simp [colourIndex]
  · rintro ⟨rfl, rfl⟩
    rfl

theorem leftInclusion_right_coefficient (x : Fock R) (I J K : Finset ℕ) :
    (colourBasis R).repr
        (leftInclusion R x * colourBasis R (colourIndex ∅ J)) (colourIndex I K) =
      if J = K then (Fock.basis R).repr x I else 0 := by
  classical
  let F : Fock R →ₗ[R] R :=
    ((Finsupp.lapply (colourIndex I K)).comp (colourBasis R).repr.toLinearMap).comp
      ((LinearMap.mulRight R (colourBasis R (colourIndex ∅ J))).comp
        (leftInclusion R).toLinearMap)
  let G : Fock R →ₗ[R] R :=
    if J = K then (Finsupp.lapply I).comp (Fock.basis R).repr.toLinearMap else 0
  have h : F = G := by
    apply (Fock.basis R).ext
    intro A
    by_cases hJK : J = K <;>
      simp [F, G, hJK, leftInclusion_basis, colourBasis_split, colourIndex_eq_iff,
        Finsupp.single_apply]
  by_cases hJK : J = K <;> simpa [F, G, hJK] using LinearMap.congr_fun h x

theorem right_word_move (j : ℕ) (I : List ℕ) :
    TwoColour.right R j * (I.map (TwoColour.left R)).prod =
      (-1 : R) ^ I.length •
        ((I.map (TwoColour.left R)).prod * TwoColour.right R j) := by
  induction I with
  | nil => simp
  | cons i I ih =>
    have hc : TwoColour.right R j * TwoColour.left R i =
        -(TwoColour.left R i * TwoColour.right R j) := by
      apply eq_neg_iff_add_eq_zero.mpr
      exact Fock.generator_anticommute R _ _
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [← mul_assoc, hc]
    simp only [neg_mul, mul_assoc, ih, mul_smul_comm, ← smul_neg,
      pow_succ, mul_neg, mul_one, neg_smul]

theorem paired_word_ordering (I : List ℕ) :
    (I.map fun i => TwoColour.left R i * TwoColour.right R i).prod =
      (-1 : R) ^ (I.length.choose 2) •
        ((I.map (TwoColour.left R)).prod * (I.map (TwoColour.right R)).prod) := by
  induction I with
  | nil => simp
  | cons i I ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [ih]
    calc
      _ = (-1 : R) ^ (I.length.choose 2) •
          (TwoColour.left R i *
            ((TwoColour.right R i * (I.map (TwoColour.left R)).prod) *
              (I.map (TwoColour.right R)).prod)) := by
        simp only [mul_smul_comm, mul_assoc]
      _ = (-1 : R) ^ (I.length.choose 2) •
          ((-1 : R) ^ I.length •
            ((TwoColour.left R i * (I.map (TwoColour.left R)).prod) *
              (TwoColour.right R i * (I.map (TwoColour.right R)).prod))) := by
        rw [right_word_move]
        simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
      _ = _ := by
        rw [smul_smul, ← pow_add]
        congr 2
        simp [Nat.choose_succ_succ, Nat.add_comm]

theorem paired_word_basis (I : Finset ℕ) :
    (I.sort.map fun i => TwoColour.left R i * TwoColour.right R i).prod =
      (dualSign I : R) • colourBasis R (colourIndex I I) := by
  rw [paired_word_ordering, ← colourBasis_left_word, ← colourBasis_right_word,
    colourBasis_split]
  congr 1
  simp [dualSign, Nat.choose_two_right]

noncomputable def pairedWord (I : Finset ℕ) : Fock R :=
  (I.sort.map fun i => TwoColour.left R i * TwoColour.right R i).prod

theorem pairedWord_insert_max {I : Finset ℕ} {j : ℕ}
    (hI : ∀ i ∈ I, i < j) :
    pairedWord R (insert j I) =
      pairedWord R I * (TwoColour.left R j * TwoColour.right R j) := by
  have hsort : (insert j I).sort = I.sort ++ [j] := by
    apply (insert j I).sortedLT_sort.eq_of_mem_iff
    · exact List.sortedLT_append.mpr ⟨I.sortedLT_sort, by simp [List.sortedLT_nil],
        by simpa using hI⟩
    · intro i
      simp [or_comm]
  simp only [pairedWord, hsort, List.map_append, List.map_singleton,
    List.prod_append, List.prod_singleton]

theorem pair_commutes_pairedWord (j : ℕ) (I : Finset ℕ) :
    (TwoColour.left R j * TwoColour.right R j) * pairedWord R I =
      pairedWord R I * (TwoColour.left R j * TwoColour.right R j) := by
  have h : Commute (TwoColour.factor R j) (pairedWord R I) := by
    apply Commute.list_prod_right
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact (show Commute (TwoColour.factor R j) (TwoColour.left R i) from
      TwoColour.factor_commutes_generator R j (2 * i)).mul_right
        (show Commute (TwoColour.factor R j) (TwoColour.right R i) from
          TwoColour.factor_commutes_generator R j (2 * i + 1))
  have he : pairedWord R I +
      (TwoColour.left R j * TwoColour.right R j) * pairedWord R I =
      pairedWord R I + pairedWord R I * (TwoColour.left R j * TwoColour.right R j) := by
    simpa only [TwoColour.factor, add_mul, one_mul, mul_add, mul_one] using h.eq
  exact add_left_cancel he

theorem kernel_pairedWord (L : ℕ) :
    TwoColour.kernel R L = ∑ I ∈ (Finset.range L).powerset, pairedWord R I := by
  induction L with
  | zero => simp [pairedWord]
  | succ L ih =>
    rw [TwoColour.kernel_succ, ih, Finset.mul_sum, Finset.range_add_one,
      Finset.sum_powerset_insert (by simp), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro I hI
    have hIL : ∀ i ∈ I, i < L := fun i hi =>
      Finset.mem_range.mp (Finset.mem_powerset.mp hI hi)
    rw [pairedWord_insert_max R hIL]
    simp only [TwoColour.factor, add_mul, one_mul, pair_commutes_pairedWord]

theorem kernel_coevaluation (L : ℕ) :
    TwoColour.kernel R L = ∑ I ∈ (Finset.range L).powerset,
      (dualSign I : R) • colourBasis R (colourIndex I I) := by
  rw [kernel_pairedWord]
  apply Finset.sum_congr rfl
  intro I hI
  exact paired_word_basis R I

theorem kernel_diagonal_coefficient (L : ℕ) (I J : Finset ℕ) :
    (colourBasis R).repr (TwoColour.kernel R L) (colourIndex I J) =
      if I = J ∧ I ⊆ Finset.range L then (dualSign I : R) else 0 := by
  rw [kernel_coevaluation]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, Module.Basis.repr_self_apply, colourIndex_eq_iff]
  by_cases hIJ : I = J
  · subst J
    simp [Finset.mem_powerset]
  · have hz (K : Finset ℕ) : ¬(K = I ∧ K = J) := by
      rintro ⟨rfl, rfl⟩
      exact hIJ rfl
    simp [hIJ, hz]

theorem matrix_vacuum (L : ℕ) :
    matrix R L (Pi.single (⟨∅, by simp⟩ : Index L) (1 : R)) = 1 := by
  classical
  have hkernel : kernel R L (Pi.single (⟨∅, by simp⟩ : Index L) (1 : R)) =
      TwoColour.kernel R L := by
    simp [kernel]
  ext I J
  simp only [matrix, hkernel, kernel_diagonal_coefficient]
  by_cases hIJ : I = J
  · subst J
    have hsub := Finset.mem_powerset.mp I.property
    have hs : (dualSign I.val : R) * (dualSign I.val : R) = 1 := by
      have h := congrArg (fun z : ℤ => (z : R)) (dualSign_mul_self I.val)
      simpa only [Int.cast_mul, Int.cast_one] using h
    simp [Matrix.one_apply, hsub, hs]
  · have hval : I.val ≠ J.val := fun h => hIJ (Subtype.ext h)
    simp [Matrix.one_apply, hIJ, hval]

end Lemmata.FockCircuits.FiniteIdentity
