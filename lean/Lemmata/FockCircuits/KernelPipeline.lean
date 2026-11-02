module

public import Lemmata.FockCircuits.KernelTransforms
public import Lemmata.FockCircuits.KernelA
public import Lemmata.FockCircuits.KernelTranspose

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.KernelPipeline

open FiniteIdentity KernelRectangle KernelAlgorithm KernelTruncation KernelSupports KernelStages
open KernelTransforms
open scoped BigOperators

noncomputable section

variable (R : Type*) [CommRing R]

def colourTriples (right : Bool) (S : List (ℕ × ℕ × R)) : List (ℕ × ℕ × R) :=
  S.map fun s => if right then (2*s.1+1, 2*s.2.1+1, s.2.2)
    else (2*s.1, 2*s.2.1, s.2.2)

def colourLinear (right : Bool) (S : List (ℕ × ℕ × R)) : OneParticle R →ₗ[R] OneParticle R :=
  Fock.linearShears R (colourTriples R right S)

theorem colourSteps_map (right : Bool) (S : List (ℕ × ℕ × R)) :
    actualSteps (colourSteps R right S) = (ExteriorAlgebra.map (colourLinear R right S)).toLinearMap := by
  have h : colourSteps R right S = rawSteps R (colourTriples R right S) := by
    cases right <;> simp only [colourSteps, colourTriples, rawSteps, colourShear,
      Bool.false_eq_true, ite_false, ite_true, List.map_map, Function.comp_def]
  rw [h, rawSteps_map]
  rfl

theorem leftLinear_left (S : List (ℕ × ℕ × R)) (v : OneParticle R) :
    colourLinear R false S (particleEmbedding R (fun i => 2*i) v) =
      particleEmbedding R (fun i => 2*i) (Fock.linearShears R S v) := by
  have h := colourSteps_left_product R S (ExteriorAlgebra.ι R v) 1
  rw [colourSteps_map] at h
  apply (ExteriorAlgebra.ι_inj R _ _).mp
  simpa only [map_one, mul_one, leftInclusion, leftParticle, algebraEmbedding, particleEmbedding,
    ExteriorAlgebra.map_apply_ι, AlgHom.toLinearMap_apply] using h

theorem leftLinear_right (S : List (ℕ × ℕ × R)) (v : OneParticle R) :
    colourLinear R false S (particleEmbedding R (fun i => 2*i+1) v) =
      particleEmbedding R (fun i => 2*i+1) v := by
  have h := colourSteps_left_product R S 1 (ExteriorAlgebra.ι R v)
  rw [colourSteps_map] at h
  apply (ExteriorAlgebra.ι_inj R _ _).mp
  simpa only [map_one, one_mul, rightInclusion, algebraEmbedding,
    ExteriorAlgebra.map_apply_ι, AlgHom.toLinearMap_apply] using h

theorem rightLinear_left (S : List (ℕ × ℕ × R)) (v : OneParticle R) :
    colourLinear R true S (particleEmbedding R (fun i => 2*i) v) =
      particleEmbedding R (fun i => 2*i) v := by
  have h := colourSteps_right_product R S (ExteriorAlgebra.ι R v) 1
  rw [colourSteps_map] at h
  apply (ExteriorAlgebra.ι_inj R _ _).mp
  simpa only [map_one, mul_one, leftInclusion, leftParticle, algebraEmbedding, particleEmbedding,
    ExteriorAlgebra.map_apply_ι, AlgHom.toLinearMap_apply] using h

theorem rightLinear_right (S : List (ℕ × ℕ × R)) (v : OneParticle R) :
    colourLinear R true S (particleEmbedding R (fun i => 2*i+1) v) =
      particleEmbedding R (fun i => 2*i+1) (Fock.linearShears R S v) := by
  have h := colourSteps_right_product R S 1 (ExteriorAlgebra.ι R v)
  rw [colourSteps_map] at h
  apply (ExteriorAlgebra.ι_inj R _ _).mp
  simpa only [map_one, one_mul, rightInclusion, algebraEmbedding,
    ExteriorAlgebra.map_apply_ι, AlgHom.toLinearMap_apply] using h

theorem diagonalParticle_embedding (a : ℕ → R) (rho : ℕ → ℕ) (v : OneParticle R) :
    diagonalParticle R a (particleEmbedding R rho v) =
      particleEmbedding R rho (diagonalParticle R (a ∘ rho) v) := by
  have h := diagonal_embedding R a rho (ExteriorAlgebra.ι R v)
  apply (ExteriorAlgebra.ι_inj R _ _).mp
  simpa only [diagonalMap, algebraEmbedding, ExteriorAlgebra.map_apply_ι] using h

def lowerColour (right : Bool) (L : ℕ) : OneParticle R →ₗ[R] OneParticle R :=
  (colourLinear R right (Fock.transposedSteps R (Fock.raisingSteps R L))).comp
    (diagonalParticle R (colourSignCoefficient R right))

theorem lowerRight_left_single (L m : ℕ) :
    lowerColour R true L (Finsupp.single (2*m) 1) = Finsupp.single (2*m) 1 := by
  change colourLinear R true _
    (diagonalParticle R (colourSignCoefficient R true) (Finsupp.single (2*m) 1)) = _
  rw [diagonalParticle_single, colourSignCoefficient_even]
  simp only [ite_true, one_smul]
  simpa only [particleEmbedding_single] using
    rightLinear_left R (Fock.transposedSteps R (Fock.raisingSteps R L)) (Finsupp.single m 1)

theorem lowerLeft_right_single (L m : ℕ) :
    lowerColour R false L (Finsupp.single (2*m+1) 1) = Finsupp.single (2*m+1) 1 := by
  change colourLinear R false _
    (diagonalParticle R (colourSignCoefficient R false) (Finsupp.single (2*m+1) 1)) = _
  rw [diagonalParticle_single, colourSignCoefficient_odd]
  simp only [Bool.false_eq_true, ite_false, one_smul]
  simpa only [particleEmbedding_single] using
    leftLinear_right R (Fock.transposedSteps R (Fock.raisingSteps R L)) (Finsupp.single m 1)

theorem lowerRight_right_single {L m : ℕ} (hm : m < L) :
    lowerColour R true L (Finsupp.single (2*m+1) 1) =
      particleEmbedding R (fun i => 2*i+1) (Fock.pascal R (Finsupp.single m 1)) := by
  change colourLinear R true _
    (diagonalParticle R (colourSignCoefficient R true) (Finsupp.single (2*m+1) 1)) = _
  rw [diagonalParticle_single, colourSignCoefficient_odd]
  simp only [ite_true, map_smul]
  have h := rightLinear_right R (Fock.transposedSteps R (Fock.raisingSteps R L))
    (Finsupp.single m 1)
  rw [particleEmbedding_single] at h
  rw [h, Fock.loweringSteps_pascal_single R hm, map_smul]

theorem lowerLeft_left_single {L m : ℕ} (hm : m < L) :
    lowerColour R false L (Finsupp.single (2*m) 1) =
      particleEmbedding R (fun i => 2*i) (Fock.pascal R (Finsupp.single m 1)) := by
  change colourLinear R false _
    (diagonalParticle R (colourSignCoefficient R false) (Finsupp.single (2*m) 1)) = _
  rw [diagonalParticle_single, colourSignCoefficient_even]
  simp only [Bool.false_eq_true, ite_false, map_smul]
  have h := leftLinear_left R (Fock.transposedSteps R (Fock.raisingSteps R L))
    (Finsupp.single m 1)
  rw [particleEmbedding_single] at h
  rw [h, Fock.loweringSteps_pascal_single R hm, map_smul]

theorem finitePascal_pascal_right {L m : ℕ} (hm : m < L) :
    particleEmbedding R (fun i => 2*i+1)
      (Fock.finitePascal R L (Fock.pascal R (Finsupp.single m 1))) =
      negativeRight R L (Finsupp.single m 1) := by
  have hcoeff : particleEmbedding R (fun i => 2*i+1)
      (Fock.finitePascal R L (Fock.pascal R (Finsupp.single m 1))) =
      positiveRight R L (Fock.pascal R (Finsupp.single m 1)) := by
    rw [Fock.pascal_single_sum]
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [particleEmbedding_finitePascal_right R (by have := Finset.mem_range.mp hj; omega)]
  rw [hcoeff]
  exact LinearMap.congr_fun (positiveRight_comp_pascal R L) (Finsupp.single m 1)

def raiseColour (right : Bool) (L : ℕ) : OneParticle R →ₗ[R] OneParticle R :=
  colourLinear R right (Fock.raisingSteps R L)

def rightPipelineLinear (L : ℕ) : OneParticle R →ₗ[R] OneParticle R :=
  (raiseColour R false L).comp ((raiseColour R true L).comp
    ((lowerColour R true L).comp (Fock.linearShears R (rightSplitTriples R (Finset.range L).toList))))

theorem rightPipeline_single {L m : ℕ} (hm : m < L) :
    rightPipelineLinear R L (Finsupp.single (2*m+1) 1) =
      substitution R L (Finsupp.single m 1) := by
  have hsplit := rightSplit_odd_single R (Finset.range L).toList (Finset.nodup_toList _) m
  simp only [Finset.mem_toList, Finset.mem_range, ite_eq_left hm] at hsplit
  have hrightFix : raiseColour R true L (Finsupp.single (2*m) 1) = Finsupp.single (2*m) 1 := by
    simpa only [raiseColour, particleEmbedding_single] using
      rightLinear_left R (Fock.raisingSteps R L) (Finsupp.single m 1)
  have hleftRaise : raiseColour R false L (Finsupp.single (2*m) 1) =
      positiveLeft R L (Finsupp.single m 1) := by
    have h := leftLinear_left R (Fock.raisingSteps R L) (Finsupp.single m 1)
    simpa only [raiseColour, particleEmbedding_single, Fock.raisingSteps_factorization,
      particleEmbedding_finitePascal_left R hm] using h
  simp only [rightPipelineLinear, LinearMap.comp_apply, hsplit, map_add,
    lowerRight_right_single R hm, lowerRight_left_single, hrightFix]
  rw [show raiseColour R true L = colourLinear R true (Fock.raisingSteps R L) from rfl,
    rightLinear_right, Fock.raisingSteps_factorization]
  rw [show raiseColour R false L = colourLinear R false (Fock.raisingSteps R L) from rfl,
    leftLinear_right, finitePascal_pascal_right R hm]
  change negativeRight R L (Finsupp.single m 1) +
    raiseColour R false L (Finsupp.single (2*m) 1) = _
  rw [hleftRaise, substitution_eq, positiveRight_comp_pascal]
  simp only [LinearMap.add_apply, add_comm]

def lowerColourSteps (right : Bool) (L : ℕ) : List (Fock R →ₗ[R] Fock R) :=
  colourSteps R right (Fock.transposedSteps R (Fock.raisingSteps R L)) ++
    [(colourSign R right).toLinearMap]

theorem lowerColourSteps_map (right : Bool) (L : ℕ) :
    actualSteps (lowerColourSteps R right L) = (ExteriorAlgebra.map (lowerColour R right L)).toLinearMap := by
  rw [lowerColourSteps, actualSteps_append, colourSteps_map]
  simp only [actualSteps, LinearMap.comp_id, colourSign, diagonalMap]
  apply LinearMap.ext
  intro v
  change ((ExteriorAlgebra.map (colourLinear R right (Fock.transposedSteps R (Fock.raisingSteps R L)))).comp
    (ExteriorAlgebra.map (diagonalParticle R (colourSignCoefficient R right)))) v = _
  rw [ExteriorAlgebra.map_comp_map]
  rfl

def rightPipelineSteps (L : ℕ) : List (Fock R →ₗ[R] Fock R) :=
  colourSteps R false (Fock.raisingSteps R L) ++ colourSteps R true (Fock.raisingSteps R L) ++
    lowerColourSteps R true L ++ rawSteps R (rightSplitTriples R (Finset.range L).toList)

theorem rightPipelineSteps_map (L : ℕ) :
    actualSteps (rightPipelineSteps R L) = (ExteriorAlgebra.map (rightPipelineLinear R L)).toLinearMap := by
  simp only [rightPipelineSteps, actualSteps_append, colourSteps_map, lowerColourSteps_map, rawSteps_map]
  apply LinearMap.ext
  intro v
  change ((ExteriorAlgebra.map (raiseColour R false L)).comp
    ((ExteriorAlgebra.map (raiseColour R true L)).comp
      ((ExteriorAlgebra.map (lowerColour R true L)).comp
        (ExteriorAlgebra.map (Fock.linearShears R (rightSplitTriples R (Finset.range L).toList)))))) v = _
  simp only [ExteriorAlgebra.map_comp_map]
  rfl

theorem rightPipeline_basis (L : ℕ) (I : Finset ℕ) (hI : ∀ i ∈ I, i < L) :
    actualSteps (rightPipelineSteps R L) (rightInclusion R (Fock.basis R I)) =
      ExteriorAlgebra.map (substitution R L) (Fock.basis R I) := by
  rw [rightPipelineSteps_map]
  change ((ExteriorAlgebra.map (rightPipelineLinear R L)).comp
    (ExteriorAlgebra.map (particleEmbedding R (fun i => 2*i+1)))) (Fock.basis R I) = _
  rw [ExteriorAlgebra.map_comp_map]
  apply exterior_maps_basis_of_single
  intro i hi
  simpa only [LinearMap.comp_apply, particleEmbedding_single] using rightPipeline_single R (hI i hi)

def factorSteps (L : ℕ) : List (Fock R →ₗ[R] Fock R) :=
  (List.range L).map fun m => LinearMap.mulRight R (TwoColour.factor R m)

theorem factorSteps_map (L : ℕ) :
    actualSteps (factorSteps R L) = LinearMap.mulRight R (TwoColour.kernel R L) := by
  induction L with
  | zero =>
    apply LinearMap.ext
    intro v
    simp [factorSteps, actualSteps]
  | succ L ih =>
    rw [factorSteps, List.range_succ, List.map_append, actualSteps_append]
    change (actualSteps (factorSteps R L)).comp (LinearMap.mulRight R (TwoColour.factor R L)) = _
    rw [ih]
    apply LinearMap.ext
    intro v
    change (v * TwoColour.factor R L) * TwoColour.kernel R L = v * TwoColour.kernel R (L+1)
    rw [TwoColour.kernel_succ, mul_assoc]

def rightKernelSteps (L : ℕ) : List (Fock R →ₗ[R] Fock R) :=
  factorSteps R L ++ rightPipelineSteps R L

theorem rightKernel_basis (L : ℕ) (I : Finset ℕ) (hI : ∀ i ∈ I, i < L) :
    actualSteps (rightKernelSteps R L) (rightInclusion R (Fock.basis R I)) =
      ExteriorAlgebra.map (substitution R L) (Fock.basis R I) * TwoColour.kernel R L := by
  rw [rightKernelSteps, actualSteps_append]
  simp only [LinearMap.comp_apply, factorSteps_map, rightPipeline_basis R L I hI,
    LinearMap.mulRight_apply]

theorem length_rightKernelSteps (L : ℕ) :
    (rightKernelSteps R L).length = 3 * (Fock.raisingSteps R L).length + 2*L + 1 := by
  simp only [rightKernelSteps, rightPipelineSteps, lowerColourSteps, colourSteps, rawSteps,
    rightSplitTriples, factorSteps, List.length_append, List.length_map, List.length_singleton,
    List.length_range, Fock.transposedSteps, List.length_reverse, Finset.length_toList,
    Finset.card_range]
  omega

def SparseColumns (T : Fock R →ₗ[R] Fock R) : Prop :=
  ∀ K : Finset (ℕ ⊕ₗ ℕ), ∃ K' : Finset (ℕ ⊕ₗ ℕ), ∃ c : R,
    T (colourBasis R K) = colourBasis R K + c • colourBasis R K'

theorem colourSteps_sparse (right : Bool) (S : List (ℕ × ℕ × R)) :
    ∀ T ∈ colourSteps R right S, SparseColumns R T := by
  intro T hT K
  obtain ⟨I, J, rfl⟩ := colourIndex_surjective K
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hT
  cases right with
  | false =>
    obtain ⟨I', c, h, _⟩ := left_shear_basis_sparse R s.2.2 s.1 s.2.1 I J
    exact ⟨colourIndex I' J, c, h⟩
  | true =>
    obtain ⟨J', c, h, _⟩ := right_shear_basis_sparse R s.2.2 s.1 s.2.1 I J
    exact ⟨colourIndex I J', c, h⟩

theorem lowerColourSteps_sparse (right : Bool) (L : ℕ) :
    ∀ T ∈ lowerColourSteps R right L, SparseColumns R T := by
  intro T hT
  rcases List.mem_append.mp hT with hT | hT
  · exact colourSteps_sparse R right _ T hT
  · have hTeq := List.mem_singleton.mp hT
    subst T
    intro K
    obtain ⟨I, J, rfl⟩ := colourIndex_surjective K
    obtain ⟨c, h⟩ := diagonal_sparse R (colourSignCoefficient R right) I J
    exact ⟨colourIndex I J, c, h⟩

theorem rightSplitSteps_sparse (L : ℕ) :
    ∀ T ∈ rawSteps R (rightSplitTriples R (Finset.range L).toList), SparseColumns R T := by
  intro T hT K
  obtain ⟨I, J, rfl⟩ := colourIndex_surjective K
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hT
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hs
  obtain ⟨I', J', c, h, _, _⟩ := split_right_sparse R m I J
  exact ⟨colourIndex I' J', c, h⟩

theorem factorSteps_sparse (L : ℕ) :
    ∀ T ∈ factorSteps R L, SparseColumns R T := by
  intro T hT K
  obtain ⟨I, J, rfl⟩ := colourIndex_surjective K
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hT
  obtain ⟨I', J', c, h, _, _⟩ := factor_sparse R m I J
  exact ⟨colourIndex I' J', c, h⟩

theorem rightKernelSteps_sparse (L : ℕ) :
    ∀ T ∈ rightKernelSteps R L, SparseColumns R T := by
  intro T hT
  simp only [rightKernelSteps, rightPipelineSteps, List.append_assoc, List.mem_append] at hT
  rcases hT with hT | hT | hT | hT | hT
  · exact factorSteps_sparse R L T hT
  · exact colourSteps_sparse R false _ T hT
  · exact colourSteps_sparse R true _ T hT
  · exact lowerColourSteps_sparse R true L T hT
  · exact rightSplitSteps_sparse R L T hT

theorem exists_rightKernel_masked_circuit {X : Type*} (U V L : ℕ)
    (bank : CircuitFamily R X (KernelRectangle.Index U V)) :
    ∃ p : CircuitFamily R X (KernelRectangle.Index U V),
      p.size = bank.size + 2 * stateCount U * stateCount V * (rightKernelSteps R L).length ∧
      Represents (colourBasis R) (basisIndex (U := U) (V := V)) bank p
        (maskedSteps (projection (colourBasis R) (basisIndex (U := U) (V := V))) (rightKernelSteps R L)) := by
  have hsparse (T) (hT : T ∈ rightKernelSteps R L) (d : KernelRectangle.Index U V) :
      ∃ K' : Finset (ℕ ⊕ₗ ℕ), ∃ c : R,
        T (colourBasis R (basisIndex d)) = colourBasis R (basisIndex d) + c • colourBasis R K' :=
    rightKernelSteps_sparse R L T hT (basisIndex d)
  obtain ⟨p, hsize, hp⟩ := exists_stage_circuit (colourBasis R) (basisIndex (U := U) (V := V))
    (basisIndex_injective U V) (rightKernelSteps R L) (fun _ => 2 * stateCount U * stateCount V)
    (fun T hT bank => by
      obtain ⟨p, hsize, hp⟩ := exists_projected_sparse_circuit (colourBasis R)
        (basisIndex (U := U) (V := V)) (basisIndex_injective U V) T bank (hsparse T hT)
      exact ⟨p, by simpa only [card_index, Nat.mul_assoc] using hsize, hp⟩) bank
  refine ⟨p, ?_, hp⟩
  rw [hsize]
  congr 1
  clear hsize hp p bank hsparse
  generalize rightKernelSteps R L = S
  induction S with
  | nil => simp
  | cons s S ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

theorem exists_rightKernel_masked_transpose (U V L : ℕ) :
    ∃ ta : ScalarTransposeAlgorithm R (KernelRectangle.Index U V) (KernelRectangle.Index U V)
      (coefficientMatrix (colourBasis R) (basisIndex (U := U) (V := V))
        (maskedSteps (projection (colourBasis R) (basisIndex (U := U) (V := V))) (rightKernelSteps R L))),
      ta.size = 2 * stateCount U * stateCount V * (rightKernelSteps R L).length := by
  classical
  obtain ⟨ta, hsize⟩ := KernelTranspose.exists_stages_transpose (colourBasis R)
    (basisIndex (U := U) (V := V)) (basisIndex_injective U V) (rightKernelSteps R L)
    (fun T hT d => rightKernelSteps_sparse R L T hT (basisIndex d))
  exact ⟨ta, by simpa only [card_index, Nat.mul_assoc] using hsize⟩

theorem maps_pascal_of_single {L m : ℕ} (hm : m < L)
    (f g : OneParticle R →ₗ[R] OneParticle R)
    (hfg : ∀ j < L, f (Finsupp.single j 1) = g (Finsupp.single j 1)) :
    f (Fock.pascal R (Finsupp.single m 1)) = g (Fock.pascal R (Finsupp.single m 1)) := by
  rw [Fock.pascal_single_sum]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hfg j (by have := Finset.mem_range.mp hj; omega)]

theorem lowerLeft_right (L : ℕ) (v : OneParticle R) :
    lowerColour R false L (particleEmbedding R (fun i => 2*i+1) v) =
      particleEmbedding R (fun i => 2*i+1) v := by
  have h : (lowerColour R false L).comp (particleEmbedding R (fun i => 2*i+1)) =
      particleEmbedding R (fun i => 2*i+1) := by
    apply (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).ext
    intro i
    simpa only [Finsupp.coe_basisSingleOne, LinearMap.comp_apply, particleEmbedding_single] using
      lowerLeft_right_single R L i
  exact LinearMap.congr_fun h v

theorem lowerLeft_pascal_left {L m : ℕ} (hm : m < L) :
    lowerColour R false L
      (particleEmbedding R (fun i => 2*i) (Fock.pascal R (Finsupp.single m 1))) =
      Finsupp.single (2*m) 1 := by
  have h := maps_pascal_of_single R hm
    ((lowerColour R false L).comp (particleEmbedding R (fun i => 2*i)))
    ((particleEmbedding R (fun i => 2*i)).comp (Fock.pascal R).toLinearMap)
    (fun j hj => by simpa only [LinearMap.comp_apply, particleEmbedding_single, LinearEquiv.coe_coe] using
      lowerLeft_left_single R hj)
  have hS : Fock.pascal R (Fock.pascal R (Finsupp.single m 1)) = Finsupp.single m 1 := by
    simpa only [Fock.pascal_symm] using (Fock.pascal R).apply_symm_apply (Finsupp.single m 1)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, hS, particleEmbedding_single] using h

theorem leftSplit_pascal {L m : ℕ} (hm : m < L) :
    Fock.linearShears R (leftSplitTriples R (Finset.range L).toList)
      (particleEmbedding R (fun i => 2*i) (Fock.pascal R (Finsupp.single m 1))) =
      particleEmbedding R (fun i => 2*i) (Fock.pascal R (Finsupp.single m 1)) +
        particleEmbedding R (fun i => 2*i+1) (Fock.pascal R (Finsupp.single m 1)) := by
  apply maps_pascal_of_single R hm
    ((Fock.linearShears R (leftSplitTriples R (Finset.range L).toList)).comp
      (particleEmbedding R (fun i => 2*i)))
    (particleEmbedding R (fun i => 2*i) + particleEmbedding R (fun i => 2*i+1))
  intro j hj
  simp only [LinearMap.comp_apply, particleEmbedding_single, LinearMap.add_apply]
  simpa only [Finset.mem_toList, Finset.mem_range, ite_eq_left hj] using
    leftSplit_even_single R (Finset.range L).toList (Finset.nodup_toList _) j

def leftPipelineLinear (L : ℕ) : OneParticle R →ₗ[R] OneParticle R :=
  (raiseColour R false L).comp ((raiseColour R true L).comp ((lowerColour R false L).comp
    ((Fock.linearShears R (leftSplitTriples R (Finset.range L).toList)).comp (lowerColour R false L))))

theorem leftPipeline_single {L m : ℕ} (hm : m < L) :
    leftPipelineLinear R L (Finsupp.single (2*m) 1) = substitution R L (Finsupp.single m 1) := by
  have hsplit := rightSplit_odd_single R (Finset.range L).toList (Finset.nodup_toList _) m
  simp only [Finset.mem_toList, Finset.mem_range, ite_eq_left hm] at hsplit
  have hpre :
      lowerColour R false L
        (Fock.linearShears R (leftSplitTriples R (Finset.range L).toList)
          (lowerColour R false L (Finsupp.single (2*m) 1))) =
      lowerColour R true L
        (Fock.linearShears R (rightSplitTriples R (Finset.range L).toList)
          (Finsupp.single (2*m+1) 1)) := by
    rw [lowerLeft_left_single R hm, leftSplit_pascal R hm, map_add,
      lowerLeft_pascal_left R hm, lowerLeft_right, hsplit, map_add,
      lowerRight_right_single R hm, lowerRight_left_single]
    exact add_comm _ _
  calc
    leftPipelineLinear R L (Finsupp.single (2*m) 1) =
        rightPipelineLinear R L (Finsupp.single (2*m+1) 1) := by
      change raiseColour R false L (raiseColour R true L _) = raiseColour R false L (raiseColour R true L _)
      simp only [LinearMap.comp_apply]
      rw [hpre]
    _ = _ := rightPipeline_single R hm

def leftPipelineSteps (L : ℕ) : List (Fock R →ₗ[R] Fock R) :=
  colourSteps R false (Fock.raisingSteps R L) ++ colourSteps R true (Fock.raisingSteps R L) ++
    lowerColourSteps R false L ++ rawSteps R (leftSplitTriples R (Finset.range L).toList) ++
      lowerColourSteps R false L

theorem leftPipelineSteps_map (L : ℕ) :
    actualSteps (leftPipelineSteps R L) = (ExteriorAlgebra.map (leftPipelineLinear R L)).toLinearMap := by
  simp only [leftPipelineSteps, actualSteps_append, colourSteps_map, lowerColourSteps_map, rawSteps_map]
  apply LinearMap.ext
  intro v
  change ((ExteriorAlgebra.map (raiseColour R false L)).comp
    ((ExteriorAlgebra.map (raiseColour R true L)).comp
      ((ExteriorAlgebra.map (lowerColour R false L)).comp
        ((ExteriorAlgebra.map (Fock.linearShears R (leftSplitTriples R (Finset.range L).toList))).comp
          (ExteriorAlgebra.map (lowerColour R false L)))))) v = _
  simp only [ExteriorAlgebra.map_comp_map]
  rfl

theorem leftPipeline_basis (L : ℕ) (I : Finset ℕ) (hI : ∀ i ∈ I, i < L) :
    actualSteps (leftPipelineSteps R L) (leftInclusion R (Fock.basis R I)) =
      ExteriorAlgebra.map (substitution R L) (Fock.basis R I) := by
  rw [leftPipelineSteps_map]
  change ((ExteriorAlgebra.map (leftPipelineLinear R L)).comp
    (ExteriorAlgebra.map (particleEmbedding R (fun i => 2*i)))) (Fock.basis R I) = _
  rw [ExteriorAlgebra.map_comp_map]
  apply exterior_maps_basis_of_single
  intro i hi
  simpa only [LinearMap.comp_apply, particleEmbedding_single] using leftPipeline_single R (hI i hi)

def leftKernelSteps (L : ℕ) : List (Fock R →ₗ[R] Fock R) :=
  factorSteps R L ++ leftPipelineSteps R L

theorem leftKernel_basis (L : ℕ) (I : Finset ℕ) (hI : ∀ i ∈ I, i < L) :
    actualSteps (leftKernelSteps R L) (leftInclusion R (Fock.basis R I)) =
      ExteriorAlgebra.map (substitution R L) (Fock.basis R I) * TwoColour.kernel R L := by
  rw [leftKernelSteps, actualSteps_append]
  simp only [LinearMap.comp_apply, factorSteps_map, leftPipeline_basis R L I hI,
    LinearMap.mulRight_apply]

theorem length_leftKernelSteps (L : ℕ) :
    (leftKernelSteps R L).length = 4 * (Fock.raisingSteps R L).length + 2*L + 2 := by
  simp only [leftKernelSteps, leftPipelineSteps, lowerColourSteps, colourSteps, rawSteps,
    leftSplitTriples, factorSteps, List.length_append, List.length_map, List.length_singleton,
    List.length_range, Fock.transposedSteps, List.length_reverse, Finset.length_toList,
    Finset.card_range]
  omega

theorem lowerColourSteps_right_basis (L : ℕ) (I : Finset ℕ) (hI : ∀ i ∈ I, i < L) :
    actualSteps (lowerColourSteps R true L) (rightInclusion R (Fock.basis R I)) =
      rightInclusion R (Fock.pascalExteriorInverse R (Fock.basis R I)) := by
  rw [lowerColourSteps_map, Fock.pascalExteriorInverse_eq]
  change ((ExteriorAlgebra.map (lowerColour R true L)).comp
    (ExteriorAlgebra.map (particleEmbedding R (fun i => 2*i+1)))) (Fock.basis R I) =
      ((ExteriorAlgebra.map (particleEmbedding R (fun i => 2*i+1))).comp
        (ExteriorAlgebra.map (Fock.pascal R).toLinearMap)) (Fock.basis R I)
  simp only [ExteriorAlgebra.map_comp_map]
  apply exterior_maps_basis_of_single
  intro i hi
  simpa only [LinearMap.comp_apply, particleEmbedding_single, LinearEquiv.coe_coe] using
    lowerRight_right_single R (hI i hi)

theorem lowerColourSteps_left_basis (L : ℕ) (I : Finset ℕ) (hI : ∀ i ∈ I, i < L) :
    actualSteps (lowerColourSteps R false L) (leftInclusion R (Fock.basis R I)) =
      leftInclusion R (Fock.pascalExteriorInverse R (Fock.basis R I)) := by
  rw [lowerColourSteps_map, Fock.pascalExteriorInverse_eq]
  change ((ExteriorAlgebra.map (lowerColour R false L)).comp
    (ExteriorAlgebra.map (particleEmbedding R (fun i => 2*i)))) (Fock.basis R I) =
      ((ExteriorAlgebra.map (particleEmbedding R (fun i => 2*i))).comp
        (ExteriorAlgebra.map (Fock.pascal R).toLinearMap)) (Fock.basis R I)
  simp only [ExteriorAlgebra.map_comp_map]
  apply exterior_maps_basis_of_single
  intro i hi
  simpa only [LinearMap.comp_apply, particleEmbedding_single, LinearEquiv.coe_coe] using
    lowerLeft_left_single R (hI i hi)

theorem leftSplitSteps_sparse (L : ℕ) :
    ∀ T ∈ rawSteps R (leftSplitTriples R (Finset.range L).toList), SparseColumns R T := by
  intro T hT K
  obtain ⟨I, J, rfl⟩ := colourIndex_surjective K
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hT
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hs
  obtain ⟨I', J', c, h, _, _⟩ := split_left_sparse R m I J
  exact ⟨colourIndex I' J', c, h⟩

theorem leftKernelSteps_sparse (L : ℕ) :
    ∀ T ∈ leftKernelSteps R L, SparseColumns R T := by
  intro T hT
  simp only [leftKernelSteps, leftPipelineSteps, List.append_assoc, List.mem_append] at hT
  rcases hT with hT | hT | hT | hT | hT | hT
  · exact factorSteps_sparse R L T hT
  · exact colourSteps_sparse R false _ T hT
  · exact colourSteps_sparse R true _ T hT
  · exact lowerColourSteps_sparse R false L T hT
  · exact leftSplitSteps_sparse R L T hT
  · exact lowerColourSteps_sparse R false L T hT

end

end Lemmata.FockCircuits.KernelPipeline
