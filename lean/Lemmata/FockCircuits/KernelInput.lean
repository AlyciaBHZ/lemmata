module

public import Lemmata.FockCircuits.KernelBanks
public import Lemmata.FockCircuits.Duality

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lemmata.FockCircuits.KernelInput

open FiniteIdentity KernelAlgorithm KernelStages KernelPipeline KernelBanks

noncomputable section

variable (R : Type*) [CommRing R]

def sourceInclusion (right : Bool) : Fock R →ₐ[R] Fock R :=
  if right then rightInclusion R else leftInclusion R

private theorem realize_sum (L : ℕ) (v : State R L) :
    realize R L v = ∑ I, v I • Fock.basis R I.val := rfl

theorem sourceInclusion_basis (right : Bool) (I : Finset ℕ) :
    sourceInclusion R right (Fock.basis R I) =
      colourBasis R (colourIndex (if right then ∅ else I) (if right then I else ∅)) := by
  cases right <;> simp [sourceInclusion, leftInclusion_basis, rightInclusion_basis]

theorem kernelSteps_source_basis (right : Bool) (L : ℕ) (I : Finset ℕ)
    (hI : ∀ i ∈ I, i < L) :
    actualSteps (kernelSteps R right L) (sourceInclusion R right (Fock.basis R I)) =
      ExteriorAlgebra.map (substitution R L) (Fock.basis R I) * TwoColour.kernel R L := by
  cases right
  · exact leftKernel_basis R L I hI
  · exact rightKernel_basis R L I hI

theorem kernelSteps_realize (right : Bool) (L : ℕ) (v : State R L) :
    actualSteps (kernelSteps R right L) (sourceInclusion R right (realize R L v)) =
      kernel R L v := by
  simp only [kernel, realize_sum, map_sum, map_smul, Finset.sum_mul, smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro I hI
  rw [kernelSteps_source_basis R right L I.val
    (fun i hi => Finset.mem_range.mp (Finset.mem_powerset.mp I.property hi))]

def sourceCoefficient (right : Bool) (c : Finset ℕ → R)
    (K : Finset (ℕ ⊕ₗ ℕ)) : R :=
  c (if right then (K.image ofLex).toRight else (K.image ofLex).toLeft)

theorem sourceCoefficient_index (right : Bool) (c : Finset ℕ → R) (I J : Finset ℕ) :
    sourceCoefficient R right c (colourIndex I J) = c (if right then J else I) := by
  cases right <;> simp [sourceCoefficient, colourIndex, Finset.image_union,
    Finset.image_image, Function.comp_def]
  all_goals
    congr 1
    ext i
    simp

def sourceDiagonal (right : Bool) (c : Finset ℕ → R) : Fock R →ₗ[R] Fock R :=
  coefficientDiagonal R (sourceCoefficient R right c)

theorem sourceDiagonal_basis (right : Bool) (c : Finset ℕ → R) (I : Finset ℕ) :
    sourceDiagonal R right c (sourceInclusion R right (Fock.basis R I)) =
      c I • sourceInclusion R right (Fock.basis R I) := by
  rw [sourceInclusion_basis, sourceDiagonal, coefficientDiagonal_basis, sourceCoefficient_index]
  cases right <;> rfl

theorem sourceDiagonal_realize (right : Bool) (c : Finset ℕ → R)
    (L : ℕ) (v : State R L) :
    sourceDiagonal R right c (sourceInclusion R right (realize R L v)) =
      sourceInclusion R right (realize R L (fun I => c I.val * v I)) := by
  simp only [realize_sum, map_sum, map_smul, sourceDiagonal_basis, smul_smul]
  apply Finset.sum_congr rfl
  intro I hI
  rw [mul_comm]

theorem sourceDiagonal_mark (right : Bool) (L W : ℕ) (k : Fin W) (v : State R L) :
    sourceDiagonal R right (fun I => (markCoefficient W (doubledEnergy I) k : R))
        (sourceInclusion R right (realize R L v)) =
      sourceInclusion R right (realize R L (mark R L W k v)) :=
  sourceDiagonal_realize R right _ L v

theorem lower_source_basis (right : Bool) (L : ℕ) (I : Finset ℕ)
    (hI : ∀ i ∈ I, i < L) :
    actualSteps (lowerColourSteps R right L) (sourceInclusion R right (Fock.basis R I)) =
      sourceInclusion R right (Fock.pascalExteriorInverse R (Fock.basis R I)) := by
  cases right
  · exact lowerColourSteps_left_basis R L I hI
  · exact lowerColourSteps_right_basis R L I hI

def markedPrefix (right : Bool) (L W : ℕ) (k : Fin W) : List (Fock R →ₗ[R] Fock R) :=
  [sourceDiagonal R right (fun I => (markCoefficient W (doubledEnergy I) k : R))] ++
    lowerColourSteps R right L

theorem markedPrefix_sparse (right : Bool) (L W : ℕ) (k : Fin W) :
    ∀ T ∈ markedPrefix R right L W k, SparseColumns R T :=
  source_prefix_sparse R right L
    (sourceCoefficient R right (fun I => (markCoefficient W (doubledEnergy I) k : R)))

theorem markedPrefix_preserves (U V L W : ℕ) (right : Bool) (k : Fin W) :
    ∀ T ∈ markedPrefix R right L W k,
      let P := KernelRectangle.projection (colourBasis R)
        (KernelRectangle.basisIndex (U := U) (V := V))
      P.comp (T.comp P) = T.comp P :=
  source_prefix_preserves R U V L right
    (sourceCoefficient R right (fun I => (markCoefficient W (doubledEnergy I) k : R)))

theorem markedPrefix_length (right : Bool) (L W : ℕ) (k : Fin W) :
    (markedPrefix R right L W k).length = (Fock.raisingSteps R L).length + 2 :=
  source_prefix_length R right L
    (sourceCoefficient R right (fun I => (markCoefficient W (doubledEnergy I) k : R)))

theorem markedPrefix_basis (right : Bool) (L W : ℕ) (k : Fin W) (I : Index L)
    (hI : doubledEnergy I.val ≤ 2 * L) :
    actualSteps (markedPrefix R right L W k) (sourceInclusion R right (Fock.basis R I.val)) =
      sourceInclusion R right (realize R L (mark R L W k (dualState R L I.val))) := by
  rw [markedPrefix, actualSteps_append]
  change sourceDiagonal R right (fun J => (markCoefficient W (doubledEnergy J) k : R))
    (actualSteps (lowerColourSteps R right L)
      (sourceInclusion R right (Fock.basis R I.val))) = _
  rw [lower_source_basis R right L I.val
      (fun i hi => Finset.mem_range.mp (Finset.mem_powerset.mp I.property hi)),
    ← realize_dualState R I.val hI, sourceDiagonal_mark]

theorem markedKernel_basis (right : Bool) (L W : ℕ) (k : Fin W) (I : Index L)
    (hI : doubledEnergy I.val ≤ 2 * L) :
    actualSteps (kernelSteps R right L ++ markedPrefix R right L W k)
        (sourceInclusion R right (Fock.basis R I.val)) =
      kernel R L (mark R L W k (dualState R L I.val)) := by
  rw [actualSteps_append]
  simp only [LinearMap.comp_apply, markedPrefix_basis R right L W k I hI]
  exact kernelSteps_realize R right L _

def barePrefix (right : Bool) : List (Fock R →ₗ[R] Fock R) :=
  [sourceDiagonal R right (fun J => (dualSign J : R))]

theorem barePrefix_sparse (right : Bool) : ∀ T ∈ barePrefix R right, SparseColumns R T := by
  intro T hT
  have h := List.mem_singleton.mp hT
  subst T
  exact coefficientDiagonal_sparse R _

theorem barePrefix_preserves (U V : ℕ) (right : Bool) :
    ∀ T ∈ barePrefix R right,
      let P := KernelRectangle.projection (colourBasis R)
        (KernelRectangle.basisIndex (U := U) (V := V))
      P.comp (T.comp P) = T.comp P := by
  intro T hT
  have h := List.mem_singleton.mp hT
  subst T
  exact coefficientDiagonal_preserves R U V _

theorem barePrefix_length (right : Bool) : (barePrefix R right).length = 1 := rfl

theorem bareKernel_basis (right : Bool) (L : ℕ) (I : Index L) :
    actualSteps (kernelSteps R right L ++ barePrefix R right)
        (sourceInclusion R right (Fock.basis R I.val)) =
      kernel R L ((dualSign I.val : R) • Pi.single I 1) := by
  rw [actualSteps_append]
  change actualSteps (kernelSteps R right L)
    (sourceDiagonal R right (fun J => (dualSign J : R))
      (sourceInclusion R right (Fock.basis R I.val))) = _
  rw [sourceDiagonal_basis, map_smul, kernel_smul]
  congr 1
  have h := kernelSteps_realize R right L (Pi.single I 1)
  simpa only [realize_single, one_smul] using h

end

end Lemmata.FockCircuits.KernelInput
