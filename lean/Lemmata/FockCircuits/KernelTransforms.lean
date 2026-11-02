module

public import Lemmata.FockCircuits.KernelStages

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.KernelTransforms

open FiniteIdentity KernelRectangle KernelAlgorithm KernelTruncation KernelSupports KernelStages

noncomputable section

variable (R : Type*) [CommRing R]

def colourShear (right : Bool) (s : ℕ × ℕ × R) : Fock R →ₐ[R] Fock R :=
  if right then Fock.shear R s.2.2 (2*s.1+1) (2*s.2.1+1)
  else Fock.shear R s.2.2 (2*s.1) (2*s.2.1)

def colourSteps (right : Bool) (S : List (ℕ × ℕ × R)) : List (Fock R →ₗ[R] Fock R) :=
  S.map fun s => (colourShear R right s).toLinearMap

theorem left_shear_product (a : R) (i j : ℕ) (v w : Fock R) :
    Fock.shear R a (2*i) (2*j) (leftInclusion R v * rightInclusion R w) =
      leftInclusion R (Fock.shear R a i j v) * rightInclusion R w := by
  rw [map_mul]
  have hl := embedding_shear R (fun i => 2*i)
    (fun p q h => by change 2*p=2*q at h; omega) a i j v
  have hr := embedding_shear_fixed R (fun i => 2*i) (fun i => 2*i+1)
    (fun _ _ => by omega) a i j w
  rw [algebraEmbedding_even] at hl
  rw [algebraEmbedding_odd] at hr
  rw [hl, hr]

theorem right_shear_product (a : R) (i j : ℕ) (v w : Fock R) :
    Fock.shear R a (2*i+1) (2*j+1) (leftInclusion R v * rightInclusion R w) =
      leftInclusion R v * rightInclusion R (Fock.shear R a i j w) := by
  rw [map_mul]
  have hl := embedding_shear_fixed R (fun i => 2*i+1) (fun i => 2*i)
    (fun _ _ => by omega) a i j v
  have hr := embedding_shear R (fun i => 2*i+1)
    (fun p q h => by change 2*p+1=2*q+1 at h; omega) a i j w
  rw [algebraEmbedding_even] at hl
  rw [algebraEmbedding_odd] at hr
  rw [hl, hr]

theorem colourSteps_left_product (S : List (ℕ × ℕ × R)) (v w : Fock R) :
    actualSteps (colourSteps R false S) (leftInclusion R v * rightInclusion R w) =
      leftInclusion R (ExteriorAlgebra.map (Fock.linearShears R S) v) * rightInclusion R w := by
  induction S with
  | nil => simp only [colourSteps, List.map_nil, actualSteps, LinearMap.id_apply,
      Fock.linearShears, ExteriorAlgebra.map_id, AlgHom.id_apply]
  | cons s S ih =>
    simp only [colourSteps, List.map_cons, actualSteps, LinearMap.comp_apply] at ih ⊢
    rw [ih]
    change Fock.shear R s.2.2 (2*s.1) (2*s.2.1)
      (leftInclusion R (ExteriorAlgebra.map (Fock.linearShears R S) v) * rightInclusion R w) = _
    rw [left_shear_product]
    rw [Fock.linearShears, ← ExteriorAlgebra.map_comp_map]
    rfl

theorem colourSteps_right_product (S : List (ℕ × ℕ × R)) (v w : Fock R) :
    actualSteps (colourSteps R true S) (leftInclusion R v * rightInclusion R w) =
      leftInclusion R v * rightInclusion R (ExteriorAlgebra.map (Fock.linearShears R S) w) := by
  induction S with
  | nil => simp only [colourSteps, List.map_nil, actualSteps, LinearMap.id_apply,
      Fock.linearShears, ExteriorAlgebra.map_id, AlgHom.id_apply]
  | cons s S ih =>
    simp only [colourSteps, List.map_cons, actualSteps, LinearMap.comp_apply] at ih ⊢
    rw [ih]
    change Fock.shear R s.2.2 (2*s.1+1) (2*s.2.1+1)
      (leftInclusion R v * rightInclusion R (ExteriorAlgebra.map (Fock.linearShears R S) w)) = _
    rw [right_shear_product]
    rw [Fock.linearShears, ← ExteriorAlgebra.map_comp_map]
    rfl

theorem exists_colourSteps_circuit {X : Type*} (U V : ℕ) (right : Bool)
    (S : List (ℕ × ℕ × R)) (bank : CircuitFamily R X (Index U V)) :
    ∃ p : CircuitFamily R X (Index U V),
      p.size = bank.size + 2 * stateCount U * stateCount V * S.length ∧
      Represents (colourBasis R) (basisIndex (U := U) (V := V)) bank p
        (maskedSteps (projection (colourBasis R) (basisIndex (U := U) (V := V)))
          (colourSteps R right S)) := by
  obtain ⟨p, hsize, hp⟩ := exists_stage_circuit (colourBasis R)
    (basisIndex (U := U) (V := V)) (basisIndex_injective U V) (colourSteps R right S)
    (fun _ => 2 * stateCount U * stateCount V) (by
      intro T hT bank
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hT
      cases right with
      | false => exact exists_left_shear_circuit R U V s.2.2 s.1 s.2.1 bank
      | true => exact exists_right_shear_circuit R U V s.2.2 s.1 s.2.1 bank) bank
  refine ⟨p, ?_, hp⟩
  rw [hsize]
  congr 1
  clear hsize hp p bank
  simp only [colourSteps, List.map_map, Function.comp_def]
  induction S with
  | nil => simp
  | cons s S ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

theorem left_shear_preserves_right (V : ℕ) (a : R) (i j : ℕ) :
    (rightFilter R V).comp ((Fock.shear R a (2*i) (2*j)).toLinearMap.comp (rightFilter R V)) =
      (Fock.shear R a (2*i) (2*j)).toLinearMap.comp (rightFilter R V) := by
  apply preserves_colourFilter
  intro I J
  obtain ⟨I', c, h, _⟩ := left_shear_basis_sparse R a i j I J
  exact ⟨I', J, c, h, fun hp => hp⟩

theorem left_shear_no_return_right (V : ℕ) (a : R) (i j : ℕ) :
    (rightFilter R V).comp ((Fock.shear R a (2*i) (2*j)).toLinearMap.comp (rightFilter R V)) =
      (rightFilter R V).comp (Fock.shear R a (2*i) (2*j)).toLinearMap := by
  apply no_return_colourFilter
  intro I J
  obtain ⟨I', c, h, _⟩ := left_shear_basis_sparse R a i j I J
  exact ⟨I', J, c, h, fun hp => hp⟩

theorem right_shear_preserves_left (U : ℕ) (a : R) (i j : ℕ) :
    (leftFilter R U).comp ((Fock.shear R a (2*i+1) (2*j+1)).toLinearMap.comp (leftFilter R U)) =
      (Fock.shear R a (2*i+1) (2*j+1)).toLinearMap.comp (leftFilter R U) := by
  apply preserves_colourFilter
  intro I J
  obtain ⟨J', c, h, _⟩ := right_shear_basis_sparse R a i j I J
  exact ⟨I, J', c, h, fun hp => hp⟩

theorem right_shear_no_return_left (U : ℕ) (a : R) (i j : ℕ) :
    (leftFilter R U).comp ((Fock.shear R a (2*i+1) (2*j+1)).toLinearMap.comp (leftFilter R U)) =
      (leftFilter R U).comp (Fock.shear R a (2*i+1) (2*j+1)).toLinearMap := by
  apply no_return_colourFilter
  intro I J
  obtain ⟨J', c, h, _⟩ := right_shear_basis_sparse R a i j I J
  exact ⟨I, J', c, h, fun hp => hp⟩

def rawSteps (S : List (ℕ × ℕ × R)) : List (Fock R →ₗ[R] Fock R) :=
  S.map fun s => (Fock.shear R s.2.2 s.1 s.2.1).toLinearMap

theorem rawSteps_map (S : List (ℕ × ℕ × R)) :
    actualSteps (rawSteps R S) = (ExteriorAlgebra.map (Fock.linearShears R S)).toLinearMap := by
  induction S with
  | nil => simp [rawSteps, actualSteps, Fock.linearShears, ExteriorAlgebra.map_id]
  | cons s S ih =>
    ext v
    simp only [rawSteps, List.map_cons, actualSteps, LinearMap.comp_apply] at ih ⊢
    rw [ih, Fock.linearShears, ← ExteriorAlgebra.map_comp_map]
    rfl

def rightSplitTriples (S : List ℕ) : List (ℕ × ℕ × R) :=
  S.map fun m => (2*m+1, 2*m, 1)

def leftSplitTriples (S : List ℕ) : List (ℕ × ℕ × R) :=
  S.map fun m => (2*m, 2*m+1, 1)

theorem rightSplit_even_single (S : List ℕ) (m : ℕ) :
    Fock.linearShears R (rightSplitTriples R S) (Finsupp.single (2*m) 1) =
      Finsupp.single (2*m) 1 := by
  induction S with
  | nil => rfl
  | cons k S ih =>
    simp only [rightSplitTriples, List.map_cons, Fock.linearShears, LinearMap.comp_apply] at ih ⊢
    rw [ih]
    simp [Fock.shearLinear_apply, Finsupp.single_apply, show 2*m ≠ 2*k+1 by omega]

theorem leftSplit_odd_single (S : List ℕ) (m : ℕ) :
    Fock.linearShears R (leftSplitTriples R S) (Finsupp.single (2*m+1) 1) =
      Finsupp.single (2*m+1) 1 := by
  induction S with
  | nil => rfl
  | cons k S ih =>
    simp only [leftSplitTriples, List.map_cons, Fock.linearShears, LinearMap.comp_apply] at ih ⊢
    rw [ih]
    simp [Fock.shearLinear_apply, Finsupp.single_apply, show 2*m+1 ≠ 2*k by omega]

theorem rightSplit_odd_single (S : List ℕ) (hS : S.Nodup) (m : ℕ) :
    Fock.linearShears R (rightSplitTriples R S) (Finsupp.single (2*m+1) 1) =
      Finsupp.single (2*m+1) 1 + if m ∈ S then Finsupp.single (2*m) 1 else 0 := by
  induction S with
  | nil => simp [rightSplitTriples, Fock.linearShears]
  | cons k S ih =>
    have hrest := List.nodup_cons.mp hS
    simp only [rightSplitTriples, List.map_cons, Fock.linearShears, LinearMap.comp_apply] at ih ⊢
    rw [ih hrest.2]
    by_cases hm : m = k
    · subst m
      simp [hrest.1, Fock.shearLinear_apply, Finsupp.single_apply]
    · have hodd : 2*m+1 ≠ 2*k+1 := by omega
      have heven : 2*m ≠ 2*k+1 := by omega
      by_cases hmS : m ∈ S <;>
        simp [hm, hmS, Fock.shearLinear_apply, Finsupp.single_apply, hodd, heven]

theorem leftSplit_even_single (S : List ℕ) (hS : S.Nodup) (m : ℕ) :
    Fock.linearShears R (leftSplitTriples R S) (Finsupp.single (2*m) 1) =
      Finsupp.single (2*m) 1 + if m ∈ S then Finsupp.single (2*m+1) 1 else 0 := by
  induction S with
  | nil => simp [leftSplitTriples, Fock.linearShears]
  | cons k S ih =>
    have hrest := List.nodup_cons.mp hS
    simp only [leftSplitTriples, List.map_cons, Fock.linearShears, LinearMap.comp_apply] at ih ⊢
    rw [ih hrest.2]
    by_cases hm : m = k
    · subst m
      simp [hrest.1, Fock.shearLinear_apply, Finsupp.single_apply]
    · have heven : 2*m ≠ 2*k := by omega
      have hodd : 2*m+1 ≠ 2*k := by omega
      by_cases hmS : m ∈ S <;>
        simp [hm, hmS, Fock.shearLinear_apply, Finsupp.single_apply, heven, hodd]

theorem exterior_maps_basis_of_single (f g : OneParticle R →ₗ[R] OneParticle R) (I : Finset ℕ)
    (h : ∀ i ∈ I, f (Finsupp.single i 1) = g (Finsupp.single i 1)) :
    ExteriorAlgebra.map f (Fock.basis R I) = ExteriorAlgebra.map g (Fock.basis R I) := by
  simp only [Fock.basis_eq_sorted_prod, map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_def, Fock.generator, ExteriorAlgebra.map_apply_ι,
    h i (by simpa only [Finset.mem_sort] using hi)]

theorem rightSplit_basis (L : ℕ) (I : Finset ℕ) (hI : ∀ i ∈ I, i < L) :
    actualSteps (rawSteps R (rightSplitTriples R (Finset.range L).toList))
      (rightInclusion R (Fock.basis R I)) =
      ExteriorAlgebra.map (leftParticle R + particleEmbedding R (fun i => 2*i+1)) (Fock.basis R I) := by
  rw [rawSteps_map]
  change ((ExteriorAlgebra.map (Fock.linearShears R (rightSplitTriples R (Finset.range L).toList))).comp
    (ExteriorAlgebra.map (particleEmbedding R (fun i => 2*i+1)))) (Fock.basis R I) = _
  rw [ExteriorAlgebra.map_comp_map]
  apply exterior_maps_basis_of_single
  intro i hi
  simp only [LinearMap.comp_apply, particleEmbedding_single, LinearMap.add_apply,
    leftParticle, Finsupp.linearCombination_single, one_smul]
  simpa only [Finset.mem_toList, Finset.mem_range, ite_eq_left (hI i hi), add_comm] using
    rightSplit_odd_single R (Finset.range L).toList (Finset.nodup_toList _) i

theorem leftSplit_basis (L : ℕ) (I : Finset ℕ) (hI : ∀ i ∈ I, i < L) :
    actualSteps (rawSteps R (leftSplitTriples R (Finset.range L).toList))
      (leftInclusion R (Fock.basis R I)) =
      ExteriorAlgebra.map (leftParticle R + particleEmbedding R (fun i => 2*i+1)) (Fock.basis R I) := by
  rw [rawSteps_map]
  change ((ExteriorAlgebra.map (Fock.linearShears R (leftSplitTriples R (Finset.range L).toList))).comp
    (ExteriorAlgebra.map (particleEmbedding R (fun i => 2*i)))) (Fock.basis R I) = _
  rw [ExteriorAlgebra.map_comp_map]
  apply exterior_maps_basis_of_single
  intro i hi
  simp only [LinearMap.comp_apply, particleEmbedding_single,
    leftSplit_even_single R _ (Finset.nodup_toList _), Finset.mem_toList,
    Finset.mem_range, if_pos (hI i hi), LinearMap.add_apply, leftParticle,
    Finsupp.linearCombination_single, one_smul]

end

end Lemmata.FockCircuits.KernelTransforms
