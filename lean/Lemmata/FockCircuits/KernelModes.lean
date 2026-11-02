module

public import Lemmata.FockCircuits.KernelInput
public import Lemmata.FockCircuits.SourceBanks
public import Lemmata.FockCircuits.RestrictedTranspose

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lemmata.FockCircuits.KernelModes

open FiniteIdentity KernelRectangle KernelAlgorithm KernelStages KernelBanks SourceBanks
open KernelPipeline

noncomputable section

variable (R : Type*) [CommRing R]
variable {X I F : Type*} [Fintype I] [Fintype F]

theorem mode_cost_bound (U V L : ℕ) (right : Bool)
    (sourceSteps : List (Fock R →ₗ[R] Fock R))
    (hlen : sourceSteps.length ≤ (Fock.raisingSteps R L).length + 2) :
    2 * stateCount U * stateCount V * ((kernelSteps R right L).length + sourceSteps.length) +
        stateCount U * stateCount V ≤ 32 * (L + 1)^2 * stateCount U * stateCount V := by
  have hs := stage_cost_bound R U V L right sourceSteps hlen
  have hpow : 1 ≤ (L + 1)^2 := one_le_pow₀ (by omega)
  have hD := Nat.mul_le_mul_right (stateCount U * stateCount V) hpow
  simp only [one_mul] at hD
  simp only [Nat.mul_assoc] at hs hD ⊢
  omega

theorem exists_mode_circuit (U V L : ℕ) (right : Bool) (r : ℤ)
    (sourceSteps : List (Fock R →ₗ[R] Fock R))
    (hsparse : ∀ T ∈ sourceSteps, SparseColumns R T)
    (hpres : ∀ T ∈ sourceSteps,
      let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
      P.comp (T.comp P) = T.comp P)
    (hlen : sourceSteps.length ≤ (Fock.raisingSteps R L).length + 2)
    (source : I ↪ KernelRectangle.Index U V) (label : I → X)
    (output : F ↪ KernelRectangle.Index U V)
    (row col : F → FiniteIdentity.Index L)
    (hrow : ∀ f, (row f).val = (output f).1.val)
    (hcol : ∀ f, (col f).val = (output f).2.val)
    (states : I → State R L)
    (hcolumns : ∀ i, actualSteps (kernelSteps R right L ++ sourceSteps)
      (colourBasis R (basisIndex (source i))) = kernel R L (states i)) :
    ∃ p : CircuitFamily R X F,
      p.size ≤ 32 * (L + 1)^2 * stateCount U * stateCount V ∧
      ∀ f, p.polynomial f = ∑ i, diagonal R L r (states i) (row f) (col f) •
        FreeAlgebra.ι R (label i) := by
  obtain ⟨p, hsize, hp⟩ := exists_kernelWithPrefix_circuit R U V L right sourceSteps
    hsparse hpres (sourceBank source label)
  let q := (scaleOutputs (modeScale (R := R) r) p).reindexOutputs output
  refine ⟨q, ?_, ?_⟩
  · dsimp only [q]
    rw [CircuitFamily.size_reindexOutputs, size_scaleOutputs, hsize, size_sourceBank,
      zero_add, card_index]
    exact mode_cost_bound R U V L right sourceSteps hlen
  · intro f
    rw [CircuitFamily.polynomial_reindexOutputs, polynomial_scaleOutputs,
      represents_sourceBank (colourBasis R) basisIndex source label p _ hp,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_smul]
    congr 1
    change modeScale (R := R) r (output f) *
      (colourBasis R).repr (actualSteps (kernelSteps R right L ++ sourceSteps)
        (colourBasis R (basisIndex (source i)))) (basisIndex (output f)) = _
    rw [hcolumns]
    exact modeScale_kernel r (states i) (output f) (row f) (col f) (hrow f) (hcol f)

end

end Lemmata.FockCircuits.KernelModes
