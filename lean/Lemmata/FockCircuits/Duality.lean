module

public import Lemmata.FockCircuits.KernelOperators
public import Lemmata.FockCircuits.KernelOrientation
public import Lemmata.FockCircuits.PascalShears
public import Lemmata.FockCircuits.OperatorMatrix
public import Lemmata.FockCircuits.FiniteShearCircuit
public import Mathlib.Data.Finset.Sum

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lemmata.FockCircuits.FiniteIdentity

variable (R : Type*) [CommRing R]

open scoped BigOperators

noncomputable def rightParticle : OneParticle R →ₗ[R] OneParticle R :=
  Finsupp.linearCombination R fun n : ℕ =>
    if n % 2 = 1 then Finsupp.single (n / 2) (1 : R) else 0

noncomputable def rightProjection : Fock R →ₐ[R] Fock R :=
  ExteriorAlgebra.map (rightParticle R)

@[simp] theorem rightProjection_left (i : ℕ) :
    rightProjection R (TwoColour.left R i) = 0 := by
  have hm : (2 * i) % 2 ≠ 1 := by omega
  simp [rightProjection, TwoColour.left, Fock.generator, rightParticle, hm]

@[simp] theorem rightProjection_right (i : ℕ) :
    rightProjection R (TwoColour.right R i) = Fock.generator R i := by
  have hm : (2 * i + 1) % 2 = 1 := by omega
  have hd : (2 * i + 1) / 2 = i := by omega
  simp [rightProjection, TwoColour.right, Fock.generator, rightParticle, hm, hd]

theorem rightProjection_left_word (I : Finset ℕ) :
    rightProjection R (colourBasis R (colourIndex I ∅)) = if I = ∅ then 1 else 0 := by
  rw [colourBasis_left_word, map_list_prod, List.map_map]
  cases h : I.sort with
  | nil =>
    have hI : I = ∅ := by
      have hs := congrArg List.toFinset h
      simpa using hs
    simp [hI]
  | cons i rest =>
    have hI : I ≠ ∅ := by
      intro hI
      subst I
      simp at h
    simp [h, hI, Function.comp_def]

theorem rightProjection_right_word (I : Finset ℕ) :
    rightProjection R (colourBasis R (colourIndex ∅ I)) = Fock.basis R I := by
  rw [colourBasis_right_word, map_list_prod, List.map_map]
  simp only [Function.comp_def, rightProjection_right]
  exact (Fock.basis_eq_sorted_prod R I).symm

theorem rightProjection_colourBasis (I J : Finset ℕ) :
    rightProjection R (colourBasis R (colourIndex I J)) =
      if I = ∅ then Fock.basis R J else 0 := by
  have hm (x y : Fock R) : rightProjection R (x * y) =
      rightProjection R x * rightProjection R y := (rightProjection R).map_mul x y
  rw [← colourBasis_split, hm, rightProjection_left_word, rightProjection_right_word]
  split_ifs <;> simp

theorem colourIndex_surjective (K : Finset (ℕ ⊕ₗ ℕ)) :
    ∃ I J : Finset ℕ, colourIndex I J = K := by
  classical
  let S : Finset (ℕ ⊕ ℕ) := K.image ofLex
  refine ⟨S.toLeft, S.toRight, ?_⟩
  ext z
  cases h : ofLex z with
  | inl i =>
    have hz : z = toLex (Sum.inl i) := by
      simpa only [toLex_ofLex] using congrArg toLex h
    rw [hz]
    simp [colourIndex, S]
  | inr j =>
    have hz : z = toLex (Sum.inr j) := by
      simpa only [toLex_ofLex] using congrArg toLex h
    rw [hz]
    simp [colourIndex, S]

theorem rightProjection_coefficient (x : Fock R) (J : Finset ℕ) :
    (Fock.basis R).repr (rightProjection R x) J =
      (colourBasis R).repr x (colourIndex ∅ J) := by
  classical
  let F : Fock R →ₗ[R] R :=
    (Finsupp.lapply J).comp ((Fock.basis R).repr.toLinearMap.comp (rightProjection R).toLinearMap)
  let G : Fock R →ₗ[R] R :=
    (Finsupp.lapply (colourIndex ∅ J)).comp (colourBasis R).repr.toLinearMap
  have h : F = G := by
    apply (colourBasis R).ext
    intro K
    obtain ⟨I, T, rfl⟩ := colourIndex_surjective K
    by_cases hI : I = ∅ <;>
      simp [F, G, hI, rightProjection_colourBasis, Finsupp.single_apply,
        colourIndex_eq_iff, eq_comm]
  simpa [F, G] using LinearMap.congr_fun h x

@[simp] theorem rightProjection_kernel (L : ℕ) :
    rightProjection R (TwoColour.kernel R L) = 1 := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hm (x y : Fock R) : rightProjection R (x * y) =
        rightProjection R x * rightProjection R y := (rightProjection R).map_mul x y
    rw [TwoColour.kernel_succ, hm, ih]
    simp [TwoColour.factor]

@[simp] theorem rightParticle_leftVector (L : ℕ) (a : Fin L → R) :
    rightParticle R (TwoColour.leftVector R L a) = 0 := by
  simp [TwoColour.leftVector, rightParticle]

@[simp] theorem rightParticle_rightVector (L : ℕ) (a : Fin L → R) :
    rightParticle R (TwoColour.rightVector R L a) = finiteVector R L a := by
  have hm (i : Fin L) : (2 * (i : ℕ) + 1) % 2 = 1 := by omega
  have hd (i : Fin L) : (2 * (i : ℕ) + 1) / 2 = i := by omega
  simp [TwoColour.rightVector, rightParticle, finiteVector, hm, hd]

noncomputable def positiveMap (L : ℕ) : OneParticle R →ₗ[R] OneParticle R :=
  Finsupp.linearCombination R fun m : ℕ =>
    finiteVector R L (fun k => (positiveCoefficient m k : R))

theorem rightParticle_positiveLeft (L : ℕ) :
    (rightParticle R).comp (positiveLeft R L) = 0 := by
  apply (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).ext
  intro m
  simp [positiveLeft]

theorem rightParticle_positiveRight (L : ℕ) :
    (rightParticle R).comp (positiveRight R L) = positiveMap R L := by
  apply (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).ext
  intro m
  simp [positiveRight, positiveMap]

theorem rightParticle_substitution (L : ℕ) :
    (rightParticle R).comp (substitution R L) =
      (positiveMap R L).comp (Fock.pascal R).toLinearMap := by
  rw [substitution_eq, LinearMap.comp_add, ← LinearMap.comp_assoc,
    rightParticle_positiveLeft, rightParticle_positiveRight, zero_add]

theorem positiveMap_single {L m : ℕ} (hm : m < L) :
    positiveMap R L (Finsupp.single m 1) =
      Fock.finitePascal R L (Finsupp.single m 1) := by
  simp only [positiveMap, Finsupp.linearCombination_single, one_smul,
    Fock.finitePascal_single, ite_eq_left hm, finiteVector, positiveCoefficient,
    Int.cast_natCast]
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ => (k.choose m : R) • Finsupp.single k (1 : R)) L

theorem positiveMap_basis {L : ℕ} (I : Finset ℕ) (hI : ∀ i ∈ I, i < L) :
    ExteriorAlgebra.map (positiveMap R L) (Fock.basis R I) =
      ExteriorAlgebra.map (Fock.finitePascal R L) (Fock.basis R I) := by
  simp only [Fock.basis_eq_sorted_prod, map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_def, Fock.generator, ExteriorAlgebra.map_apply_ι,
    positiveMap_single R (hI i (by simpa only [Finset.mem_sort] using hi))]

theorem rightProjection_kernel_state (L : ℕ) (v : State R L) :
    rightProjection R (kernel R L v) =
      ExteriorAlgebra.map (positiveMap R L) (Fock.pascalExterior R (realize R L v)) := by
  have hm (x y : Fock R) : rightProjection R (x * y) =
      rightProjection R x * rightProjection R y := (rightProjection R).map_mul x y
  rw [kernel, hm, rightProjection_kernel, mul_one]
  change ExteriorAlgebra.map (rightParticle R)
      (ExteriorAlgebra.map (substitution R L) (realize R L v)) = _
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, rightParticle_substitution,
    ← ExteriorAlgebra.map_comp_map]
  rfl

theorem finiteProjection_energy {L E : ℕ} (hEL : E ≤ 2 * L) :
    (finiteProjection R L).comp (Fock.energyProjection R E) =
      Fock.energyProjection R E := by
  apply (Fock.basis R).ext
  intro I
  by_cases hI : doubledEnergy I ≤ E
  · have hIL : I ⊆ Finset.range L := by
      intro i hi
      have hb := Finset.single_le_sum (f := fun j : ℕ => 2 * j + 1)
        (fun j _ => Nat.zero_le _) hi
      change 2 * i + 1 ≤ doubledEnergy I at hb
      exact Finset.mem_range.mpr (by omega)
    simp only [LinearMap.comp_apply, Fock.energyProjection_basis, ite_eq_left hI,
      finiteProjection_basis R I hIL]
  · simp [hI]

theorem finiteProjection_of_energy {L E : ℕ} (hEL : E ≤ 2 * L) (x : Fock R)
    (hx : Fock.energyProjection R E x = x) : finiteProjection R L x = x := by
  have h := LinearMap.congr_fun (finiteProjection_energy R hEL) x
  simpa only [LinearMap.comp_apply, hx] using h

noncomputable def dualState (L : ℕ) (I : Finset ℕ) : State R L :=
  fun J => (Fock.basis R).repr (Fock.pascalExteriorInverse R (Fock.basis R I)) J.val

theorem realize_dualState {L : ℕ} (I : Finset ℕ) (hI : doubledEnergy I ≤ 2 * L) :
    realize R L (dualState R L I) = Fock.pascalExteriorInverse R (Fock.basis R I) := by
  change finiteProjection R L (Fock.pascalExteriorInverse R (Fock.basis R I)) = _
  exact finiteProjection_of_energy R hI _ (Fock.pascalExteriorInverse_basis_energy R I)

theorem dualState_energy {L : ℕ} (I : Finset ℕ) (J : Index L)
    (hJ : doubledEnergy I < doubledEnergy J.val) : dualState R L I J = 0 := by
  have h := congrArg (fun x : Fock R => (Fock.basis R).repr x J.val)
    (Fock.pascalExteriorInverse_basis_energy R I)
  rw [Fock.energyProjection_coefficient, if_neg (by omega)] at h
  exact h.symm

theorem dualState_parity {L : ℕ} (I : Finset ℕ) (J : Index L)
    (hI : ∀ i ∈ I, i < L)
    (hJ : doubledEnergy J.val % 2 ≠ doubledEnergy I % 2) : dualState R L I J = 0 := by
  have h := congrArg (fun x : Fock R => (Fock.basis R).repr x J.val)
    (Fock.pascalExteriorInverse_basis_parity R I hI)
  rw [Fock.parityProjection_coefficient, if_neg hJ] at h
  exact h.symm

theorem dualState_supported {L : ℕ} (I : Index L) (J : Index L)
    (hJ : dualState R L I.val J ≠ 0) :
    doubledEnergy J.val ≤ doubledEnergy I.val ∧
      doubledEnergy J.val % 2 = doubledEnergy I.val % 2 := by
  constructor
  · by_contra h
    exact hJ (dualState_energy R I.val J (by omega))
  · by_contra h
    exact hJ (dualState_parity R I.val J
      (fun i hi => Finset.mem_range.mp (Finset.mem_powerset.mp I.property hi)) h)

theorem dual_kernel_coefficient {L : ℕ} (I J : Index L)
    (hI : doubledEnergy I.val ≤ 2 * L)
    (henergy : doubledEnergy I.val = doubledEnergy J.val) :
    (colourBasis R).repr (kernel R L (dualState R L I.val)) (colourIndex ∅ J.val) =
      if I = J then 1 else 0 := by
  classical
  rw [← rightProjection_coefficient, rightProjection_kernel_state,
    realize_dualState R I.val hI, Fock.pascalExterior_inverse,
    positiveMap_basis R I.val (fun i hi =>
      Finset.mem_range.mp (Finset.mem_powerset.mp I.property hi))]
  have h := congrArg (fun x : Fock R => (Fock.basis R).repr x J.val)
    (Fock.finitePascal_homogeneous_diagonal R L I.val)
  rw [Fock.energyProjection_coefficient, if_pos (by omega)] at h
  simpa only [Module.Basis.repr_self_apply, Subtype.val_inj, eq_comm] using h

theorem dual_matrix_vacuum {L : ℕ} (I J : Index L)
    (hI : doubledEnergy I.val ≤ 2 * L)
    (henergy : doubledEnergy I.val = doubledEnergy J.val) :
    matrix R L (dualState R L I.val) ⟨∅, by simp⟩ J =
      if I = J then (dualSign J.val : R) else 0 := by
  rw [matrix, dual_kernel_coefficient R I J hI henergy]
  split_ifs <;> simp

theorem dual_matrix_normalized {L : ℕ} (I J : Index L)
    (hI : doubledEnergy I.val ≤ 2 * L)
    (henergy : doubledEnergy I.val = doubledEnergy J.val) :
    (dualSign J.val : R) * matrix R L (dualState R L I.val) ⟨∅, by simp⟩ J =
      if I = J then 1 else 0 := by
  rw [dual_matrix_vacuum R I J hI henergy]
  split_ifs
  · simpa only [Int.cast_mul, Int.cast_one] using
      congrArg (fun z : ℤ => (z : R)) (dualSign_mul_self J.val)
  · simp

theorem exists_dual_family (H L n : ℕ) (hH : 0 < H) (hHL : H ≤ L)
    (hcapacity : 2 * H * n ≤ stateCount H - 1) :
    ∃ (W : ℕ) (B : Fin n → Index L),
      0 < W ∧ W ≤ 2 * H ∧ Function.Injective B ∧
      (∀ i, doubledEnergy (B i).val = W) ∧
      (∀ i j, (dualSign (B j).val : R) *
        matrix R L (dualState R L (B i).val) ⟨∅, by simp⟩ (B j) =
          if i = j then 1 else 0) := by
  classical
  obtain ⟨W, S, hW, hWH, hcard, hS⟩ := exists_homogeneous_family H n hH hcapacity
  let e : Fin n ≃ S := (Finset.equivFinOfCardEq hcard).symm
  have hSL (I : S) : I.val ⊆ Finset.range L := by
    intro i hi
    have henergy := hS I.val I.property
    have hb := Finset.single_le_sum (f := fun j : ℕ => 2 * j + 1)
      (fun j _ => Nat.zero_le _) hi
    change 2 * i + 1 ≤ doubledEnergy I.val at hb
    exact Finset.mem_range.mpr (by omega)
  let B : Fin n → Index L := fun i => ⟨(e i).val, Finset.mem_powerset.mpr (hSL (e i))⟩
  have hB : Function.Injective B := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun x : Index L => x.val) hij
  have hBW (i : Fin n) : doubledEnergy (B i).val = W := hS (e i).val (e i).property
  refine ⟨W, B, hW, hWH, hB, hBW, ?_⟩
  intro i j
  rw [dual_matrix_normalized R (B i) (B j) (by rw [hBW]; omega) (by rw [hBW, hBW])]
  simp only [hB.eq_iff]

end Lemmata.FockCircuits.FiniteIdentity
