module

public import Lemmata.FockCircuits.KernelModes

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lemmata.FockCircuits.KernelModes

open FiniteIdentity KernelRectangle KernelAlgorithm KernelStages KernelPipeline KernelBanks SourceBanks

noncomputable section

variable (R : Type*) [CommRing R]
variable {I F : Type*} [Fintype I] [Fintype F]

theorem exists_mode_transpose (U V L : ℕ) (right : Bool) (r : ℤ) (scale : R)
    (sourceSteps : List (Fock R →ₗ[R] Fock R))
    (hsparse : ∀ T ∈ sourceSteps, SparseColumns R T)
    (hpres : ∀ T ∈ sourceSteps,
      let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
      P.comp (T.comp P) = T.comp P)
    (hlen : sourceSteps.length ≤ (Fock.raisingSteps R L).length + 2)
    (source : I ↪ KernelRectangle.Index U V)
    (output : F ↪ KernelRectangle.Index U V)
    (row col : F → FiniteIdentity.Index L)
    (hrow : ∀ f, (row f).val = (output f).1.val)
    (hcol : ∀ f, (col f).val = (output f).2.val)
    (states : I → State R L)
    (hcolumns : ∀ i, actualSteps (kernelSteps R right L ++ sourceSteps)
      (colourBasis R (basisIndex (source i))) = kernel R L (states i)) :
    ∃ ta : ScalarTransposeAlgorithm R I F
      (fun f i => scale * diagonal R L r (states i) (row f) (col f)),
      ta.size ≤ 32 * (L + 1)^2 * stateCount U * stateCount V := by
  classical
  obtain ⟨t, hsize⟩ := exists_kernelWithPrefix_transpose R U V L right sourceSteps hsparse hpres
  let q := RestrictedTranspose.build t source output (fun d => scale * modeScale (R := R) r d)
  refine ⟨⟨q.circuit, ?_⟩, ?_⟩
  · intro i
    rw [q.correct]
    apply Finset.sum_congr rfl
    intro f hf
    congr 1
    change (scale * modeScale (R := R) r (output f)) *
      (colourBasis R).repr (actualSteps (kernelSteps R right L ++ sourceSteps)
        (colourBasis R (basisIndex (source i)))) (basisIndex (output f)) = _
    rw [hcolumns, mul_assoc,
      modeScale_kernel r (states i) (output f) (row f) (col f) (hrow f) (hcol f)]
  · change q.size ≤ _
    rw [RestrictedTranspose.size_build, hsize, card_index]
    exact mode_cost_bound R U V L right sourceSteps hlen

end

end Lemmata.FockCircuits.KernelModes
