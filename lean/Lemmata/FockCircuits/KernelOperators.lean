module

public import Lemmata.FockCircuits.KernelCoevaluation

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lemmata.FockCircuits.FiniteIdentity

variable (R : Type*) [CommRing R]

@[simp] theorem leftParticle_single (i : ℕ) (a : R) :
    leftParticle R (Finsupp.single i a) = a • Finsupp.single (2 * i) 1 := by
  simp [leftParticle]

theorem leftParticle_even (v : OneParticle R) (i : ℕ) :
    leftParticle R v (2 * i) = v i := by
  have h : (Finsupp.lapply (2 * i)).comp (leftParticle R) = Finsupp.lapply i := by
    apply (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).ext
    intro j
    by_cases hji : j = i
    · subst j
      simp [Finsupp.lapply_apply]
    · have hne : 2 * j ≠ 2 * i := by omega
      simp [Finsupp.lapply_apply, Finsupp.single_apply, hji, hne]
  exact LinearMap.congr_fun h v

theorem contract_right_word (i : ℕ) (J : List ℕ) :
    Fock.contract R (2 * i) (J.map (TwoColour.right R)).prod = 0 := by
  induction J with
  | nil => simp
  | cons j J ih =>
    simp only [List.map_cons, List.prod_cons, TwoColour.contract_left_right,
      ih, mul_zero, neg_zero]

theorem contract_leftInclusion_mul_right (i : ℕ) (x : Fock R) (J : Finset ℕ) :
    Fock.contract R (2 * i) (leftInclusion R x * colourBasis R (colourIndex ∅ J)) =
      leftInclusion R (Fock.contract R i x) * colourBasis R (colourIndex ∅ J) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, ← Algebra.smul_def, map_smul, colourBasis_right_word,
      contract_right_word]
    simp [Fock.contract, CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy =>
    simp only [map_add, add_mul, hx, hy]
  | ι_mul x v ih =>
    have hm (y z : Fock R) : leftInclusion R (y * z) =
        leftInclusion R y * leftInclusion R z := (leftInclusion R).map_mul y z
    have hι : leftInclusion R (ExteriorAlgebra.ι R v) =
        ExteriorAlgebra.ι R (leftParticle R v) :=
      ExteriorAlgebra.map_apply_ι _ _
    have hd (w : OneParticle R) (k : ℕ) (z : Fock R) :
        Fock.contract R k (ExteriorAlgebra.ι R w * z) =
          w k • z - ExteriorAlgebra.ι R w * Fock.contract R k z := by
      simpa only [Fock.contract, Finsupp.lapply_apply] using
        (CliffordAlgebra.contractLeft_ι_mul
          (Q := (0 : QuadraticForm R (OneParticle R))) (Finsupp.lapply k) w z)
    rw [hm, hι, mul_assoc, hd, leftParticle_even, ih, hd,
      map_sub, map_smul, hm, hι]
    simp only [smul_mul_assoc, sub_mul, mul_assoc]

noncomputable def finiteVector (L : ℕ) (a : Fin L → R) : OneParticle R :=
  ∑ i, a i • Finsupp.single (i : ℕ) (1 : R)

@[simp] theorem finiteVector_apply (L : ℕ) (a : Fin L → R) (i : Fin L) :
    finiteVector R L a i = a i := by
  simp [finiteVector, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, Fin.val_inj]

theorem coordinateDual_finiteVector (L : ℕ) (a b : Fin L → R) :
    Fock.coordinateDual R (finiteVector R L a) (finiteVector R L b) =
      ∑ i, a i * b i := by
  change Fock.coordinateDual R (∑ i : Fin L, a i • Finsupp.single (i : ℕ) (1 : R))
    (finiteVector R L b) = _
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Fock.coordinateDual_single, one_mul, finiteVector_apply, smul_eq_mul]

theorem leftParticle_finiteVector (L : ℕ) (a : Fin L → R) :
    leftParticle R (finiteVector R L a) = TwoColour.leftVector R L a := by
  simp [finiteVector, TwoColour.leftVector, smul_smul]

theorem contractVector_finiteVector (L : ℕ) (a : Fin L → R) (x : Fock R) :
    Fock.contractVector R (finiteVector R L a) x =
      ∑ i, a i • Fock.contract R i x := by
  let d : OneParticle R →ₗ[R] Fock R →ₗ[R] Fock R :=
    (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (OneParticle R)))).comp
      (Fock.coordinateDual R)
  change d (∑ i : Fin L, a i • Finsupp.single (i : ℕ) (1 : R)) x = _
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change a i • Fock.contractVector R (Finsupp.single (i : ℕ) (1 : R)) x = _
  rw [Fock.contractVector_single]

@[simp] theorem leftInclusion_ι (v : OneParticle R) :
    leftInclusion R (ExteriorAlgebra.ι R v) = ExteriorAlgebra.ι R (leftParticle R v) :=
  ExteriorAlgebra.map_apply_ι _ _

theorem createVector_leftInclusion_mul_right (L : ℕ) (a : Fin L → R)
    (x : Fock R) (J : Finset ℕ) :
    Fock.createVector R (TwoColour.leftVector R L a)
        (leftInclusion R x * colourBasis R (colourIndex ∅ J)) =
      leftInclusion R (Fock.createVector R (finiteVector R L a) x) *
        colourBasis R (colourIndex ∅ J) := by
  simp only [Fock.createVector_apply, map_mul, leftInclusion_ι,
    leftParticle_finiteVector, mul_assoc]

theorem contractVector_leftInclusion_mul_right (L : ℕ) (a : Fin L → R)
    (x : Fock R) (J : Finset ℕ) :
    Fock.contractVector R (TwoColour.leftVector R L a)
        (leftInclusion R x * colourBasis R (colourIndex ∅ J)) =
      leftInclusion R (Fock.contractVector R (finiteVector R L a) x) *
        colourBasis R (colourIndex ∅ J) := by
  rw [TwoColour.contractVector_left, contractVector_finiteVector]
  simp only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc,
    contract_leftInclusion_mul_right]

noncomputable def plainList (L : ℕ)
    (S : List ((Fin L → R) × (Fin L → R))) : List (OneParticle R × OneParticle R) :=
  S.map fun a => (finiteVector R L a.1, finiteVector R L a.2)

theorem normalList_leftInclusion_mul_right (L : ℕ)
    (S : List ((Fin L → R) × (Fin L → R))) (x : Fock R) (J : Finset ℕ) :
    Fock.normalList R (TwoColour.colouredList R L S)
        (leftInclusion R x * colourBasis R (colourIndex ∅ J)) =
      leftInclusion R (Fock.normalList R (plainList R L S) x) *
        colourBasis R (colourIndex ∅ J) := by
  induction S generalizing x with
  | nil => simp [TwoColour.colouredList, plainList]
  | cons a S ih =>
    simp only [TwoColour.colouredList, plainList, List.map_cons,
      Fock.normalList_cons, List.length_map]
    change Fock.createVector R (TwoColour.leftVector R L a.1)
        (Fock.normalList R (TwoColour.colouredList R L S)
          (leftInclusion R x * colourBasis R (colourIndex ∅ J))) +
        (-1 : R) ^ S.length • Fock.normalList R (TwoColour.colouredList R L S)
          (Fock.contractVector R (TwoColour.leftVector R L a.2)
            (leftInclusion R x * colourBasis R (colourIndex ∅ J))) = _
    rw [ih, createVector_leftInclusion_mul_right,
      contractVector_leftInclusion_mul_right, ih]
    simp only [map_add, map_smul, add_mul, smul_mul_assoc, plainList]

theorem normalList_kernel_coevaluation (L : ℕ)
    (S : List ((Fin L → R) × (Fin L → R))) :
    Fock.normalList R (TwoColour.colouredList R L S) (TwoColour.kernel R L) =
      ∑ J ∈ (Finset.range L).powerset, (dualSign J : R) •
        (leftInclusion R (Fock.normalList R (plainList R L S) (Fock.basis R J)) *
          colourBasis R (colourIndex ∅ J)) := by
  rw [kernel_coevaluation]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  rw [← colourBasis_split, ← leftInclusion_basis, normalList_leftInclusion_mul_right]

theorem normalList_kernel_coefficient (L : ℕ)
    (S : List ((Fin L → R) × (Fin L → R))) (I J : Index L) :
    (colourBasis R).repr
        (Fock.normalList R (TwoColour.colouredList R L S) (TwoColour.kernel R L))
        (colourIndex I.val J.val) =
      (dualSign J.val : R) *
        (Fock.basis R).repr (Fock.normalList R (plainList R L S) (Fock.basis R J.val)) I.val := by
  rw [normalList_kernel_coevaluation]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, leftInclusion_right_coefficient]
  simp [Finset.mem_powerset.mp J.property]

theorem matrix_single_eq_normalList (L : ℕ) (A I J : Index L) (c : R) :
    matrix R L (Pi.single A c) I J = c *
      (Fock.basis R).repr
        (Fock.normalList R (plainList R L (sourceWord R L A)) (Fock.basis R J.val)) I.val := by
  rw [matrix, kernel_single, map_smul, Finsupp.smul_apply, smul_eq_mul,
    normalList_kernel_coefficient]
  have hs : (dualSign J.val : R) * (dualSign J.val : R) = 1 := by
    have h := congrArg (fun z : ℤ => (z : R)) (dualSign_mul_self J.val)
    simpa only [Int.cast_mul, Int.cast_one] using h
  calc
    _ = c * ((dualSign J.val : R) * (dualSign J.val : R)) *
        (Fock.basis R).repr
          (Fock.normalList R (plainList R L (sourceWord R L A)) (Fock.basis R J.val)) I.val := by ring
    _ = _ := by rw [hs, mul_one]

@[simp] theorem kernel_smul (L : ℕ) (c : R) (v : State R L) :
    kernel R L (c • v) = c • kernel R L v := by
  simp only [kernel, map_smul, smul_mul_assoc]

@[simp] theorem matrix_smul (L : ℕ) (c : R) (v : State R L) :
    matrix R L (c • v) = c • matrix R L v := by
  ext I J
  simp only [matrix, kernel_smul, map_smul, Finsupp.smul_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

noncomputable def matrixLinear (L : ℕ) : State R L →ₗ[R] Matrix (Index L) (Index L) R where
  toFun := matrix R L
  map_add' := matrix_add R L
  map_smul' c v := by simpa only [RingHom.id_apply] using matrix_smul R L c v

noncomputable def diagonalLinear (L : ℕ) (r : ℤ) :
    State R L →ₗ[R] Matrix (Index L) (Index L) R where
  toFun := diagonal R L r
  map_add' v w := by
    ext I J
    simp only [diagonal, matrix_add, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' c v := by
    ext I J
    simp only [diagonal, matrix_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem state_eq_sum_single (L : ℕ) (v : State R L) :
    v = ∑ A : Index L, v A • Pi.single A (1 : R) := by
  classical
  ext A
  simp [Pi.single_apply, eq_comm]

theorem matrix_eq_sum_single (L : ℕ) (v : State R L) :
    matrix R L v = ∑ A : Index L, v A • matrix R L (Pi.single A (1 : R)) := by
  change matrixLinear R L v = _
  conv_lhs => rw [state_eq_sum_single R L v]
  simp only [map_sum, map_smul] <;> rfl

theorem diagonal_eq_sum_single (L : ℕ) (r : ℤ) (v : State R L) :
    diagonal R L r v = ∑ A : Index L, v A • diagonal R L r (Pi.single A (1 : R)) := by
  change diagonalLinear R L r v = _
  conv_lhs => rw [state_eq_sum_single R L v]
  simp only [map_sum, map_smul] <;> rfl

end Lemmata.FockCircuits.FiniteIdentity
