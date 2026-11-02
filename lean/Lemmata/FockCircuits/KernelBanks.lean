module

public import Lemmata.FockCircuits.KernelSafety

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.KernelBanks

open FiniteIdentity KernelRectangle KernelAlgorithm KernelTruncation KernelSupports KernelStages
open KernelTransforms KernelPipeline KernelSafety

noncomputable section

variable (R : Type*) [CommRing R]

def coefficientDiagonal (c : Finset (ℕ ⊕ₗ ℕ) → R) : Fock R →ₗ[R] Fock R :=
  (colourBasis R).constr R fun K => c K • colourBasis R K

@[simp] theorem coefficientDiagonal_basis (c : Finset (ℕ ⊕ₗ ℕ) → R)
    (K : Finset (ℕ ⊕ₗ ℕ)) :
    coefficientDiagonal R c (colourBasis R K) = c K • colourBasis R K := by
  simp [coefficientDiagonal]

theorem coefficientDiagonal_sparse (c : Finset (ℕ ⊕ₗ ℕ) → R) :
    SparseColumns R (coefficientDiagonal R c) := by
  intro K
  refine ⟨K, c K - 1, ?_⟩
  rw [coefficientDiagonal_basis]
  module

theorem coefficientDiagonal_preserves (U V : ℕ) (c : Finset (ℕ ⊕ₗ ℕ) → R) :
    let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
    P.comp ((coefficientDiagonal R c).comp P) = (coefficientDiagonal R c).comp P := by
  dsimp only
  simp only [rectangle_eq_filters, leftFilter, rightFilter, colourFilter_comp]
  apply preserves_colourFilter
  intro I J
  refine ⟨I, J, c (colourIndex I J) - 1, ?_, fun hp => hp⟩
  rw [coefficientDiagonal_basis]
  module

def kernelSteps (right : Bool) (L : ℕ) : List (Fock R →ₗ[R] Fock R) :=
  if right then rightKernelSteps R L else leftKernelSteps R L

theorem kernelSteps_sparse (right : Bool) (L : ℕ) :
    ∀ T ∈ kernelSteps R right L, SparseColumns R T := by
  cases right
  · exact leftKernelSteps_sparse R L
  · exact rightKernelSteps_sparse R L

theorem kernelSteps_restriction (U V L : ℕ) (right : Bool) :
    let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
    (maskedSteps P (kernelSteps R right L)).comp P =
      P.comp ((actualSteps (kernelSteps R right L)).comp P) := by
  cases right
  · exact leftKernel_restriction R U V L
  · exact rightKernel_restriction R U V L

theorem maskedSteps_preserving {M : Type*} [AddCommGroup M] [Module R M]
    (P : M →ₗ[R] M) (hP : P.comp P = P) (steps : List (M →ₗ[R] M))
    (hpres : ∀ T ∈ steps, P.comp (T.comp P) = T.comp P) :
    (maskedSteps P steps).comp P = (actualSteps steps).comp P := by
  have hmask := maskedSteps_oriented (LinearMap.id : M →ₗ[R] M) P rfl hP
    (by simp) steps (fun T _ => by simp) hpres
  have hactual := actualSteps_preserves P hP steps hpres
  simpa only [LinearMap.id_comp] using hmask.trans hactual

theorem restriction_with_prefix {M : Type*} [AddCommGroup M] [Module R M]
    (P : M →ₗ[R] M) (hP : P.comp P = P) (core sourceSteps : List (M →ₗ[R] M))
    (hcore : (maskedSteps P core).comp P = P.comp ((actualSteps core).comp P))
    (hprefix : ∀ T ∈ sourceSteps, P.comp (T.comp P) = T.comp P) :
    (maskedSteps P (core ++ sourceSteps)).comp P =
      P.comp ((actualSteps (core ++ sourceSteps)).comp P) := by
  have hmask := maskedSteps_preserving R P hP sourceSteps hprefix
  have hactual := actualSteps_preserves P hP sourceSteps hprefix
  rw [maskedSteps_append, actualSteps_append]
  apply LinearMap.ext
  intro v
  have hm := LinearMap.congr_fun hmask v
  have ha := LinearMap.congr_fun hactual v
  have hc := LinearMap.congr_fun hcore ((actualSteps sourceSteps) (P v))
  simp only [LinearMap.comp_apply] at hm ha hc ⊢
  rw [ha] at hc
  rw [hm]
  exact hc

theorem kernelWithPrefix_restriction (U V L : ℕ) (right : Bool)
    (sourceSteps : List (Fock R →ₗ[R] Fock R))
    (hpres : ∀ T ∈ sourceSteps,
      let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
      P.comp (T.comp P) = T.comp P) :
    let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
    (maskedSteps P (kernelSteps R right L ++ sourceSteps)).comp P =
      P.comp ((actualSteps (kernelSteps R right L ++ sourceSteps)).comp P) :=
  restriction_with_prefix R _ (projection_idempotent _ _ (basisIndex_injective U V)) _ _
    (kernelSteps_restriction R U V L right) hpres

theorem exists_kernelWithPrefix_circuit {X : Type*} (U V L : ℕ) (right : Bool)
    (sourceSteps : List (Fock R →ₗ[R] Fock R))
    (hsparse : ∀ T ∈ sourceSteps, SparseColumns R T)
    (hpres : ∀ T ∈ sourceSteps,
      let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
      P.comp (T.comp P) = T.comp P)
    (bank : CircuitFamily R X (KernelRectangle.Index U V)) :
    ∃ p : CircuitFamily R X (KernelRectangle.Index U V),
      p.size = bank.size + 2 * stateCount U * stateCount V *
        ((kernelSteps R right L).length + sourceSteps.length) ∧
      Represents (colourBasis R) (basisIndex (U := U) (V := V)) bank p
        (actualSteps (kernelSteps R right L ++ sourceSteps)) := by
  have hsp : ∀ T ∈ kernelSteps R right L ++ sourceSteps, SparseColumns R T := by
    intro T hT
    rcases List.mem_append.mp hT with hT | hT
    · exact kernelSteps_sparse R right L T hT
    · exact hsparse T hT
  obtain ⟨p, hsize, hp⟩ := exists_stage_circuit (colourBasis R) (basisIndex (U := U) (V := V))
    (basisIndex_injective U V) (kernelSteps R right L ++ sourceSteps)
    (fun _ => 2 * stateCount U * stateCount V) (fun T hT bank => by
      obtain ⟨q, hsize, hq⟩ := exists_projected_sparse_circuit (colourBasis R)
        (basisIndex (U := U) (V := V)) (basisIndex_injective U V) T bank
        (fun d => hsp T hT (basisIndex d))
      exact ⟨q, by simpa only [card_index, Nat.mul_assoc] using hsize, hq⟩) bank
  refine ⟨p, ?_, represents_of_coefficientMatrix_eq hp ?_⟩
  · rw [hsize, ← List.length_append]
    congr 1
    clear hsize hp p bank hsp hsparse hpres
    generalize kernelSteps R right L ++ sourceSteps = S
    induction S with
    | nil => simp
    | cons s S ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
  · exact coefficientMatrix_of_restriction _ _ (basisIndex_injective U V) _ _
      (kernelWithPrefix_restriction R U V L right sourceSteps hpres)

theorem exists_kernelWithPrefix_transpose (U V L : ℕ) (right : Bool)
    (sourceSteps : List (Fock R →ₗ[R] Fock R))
    (hsparse : ∀ T ∈ sourceSteps, SparseColumns R T)
    (hpres : ∀ T ∈ sourceSteps,
      let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
      P.comp (T.comp P) = T.comp P) :
    ∃ ta : ScalarTransposeAlgorithm R (KernelRectangle.Index U V) (KernelRectangle.Index U V)
      (coefficientMatrix (colourBasis R) (basisIndex (U := U) (V := V))
        (actualSteps (kernelSteps R right L ++ sourceSteps))),
      ta.size = 2 * stateCount U * stateCount V *
        ((kernelSteps R right L).length + sourceSteps.length) := by
  classical
  obtain ⟨ta, hsize⟩ := KernelTranspose.exists_stages_transpose (colourBasis R)
    (basisIndex (U := U) (V := V)) (basisIndex_injective U V) (kernelSteps R right L ++ sourceSteps)
    (fun T hT d => by
      rcases List.mem_append.mp hT with hT | hT
      · exact kernelSteps_sparse R right L T hT (basisIndex d)
      · exact hsparse T hT (basisIndex d))
  have heq := coefficientMatrix_of_restriction _ _ (basisIndex_injective U V) _ _
    (kernelWithPrefix_restriction R U V L right sourceSteps hpres)
  exact ⟨KernelTranspose.retype ta heq, by
    simpa only [KernelTranspose.size_retype, hsize, List.length_append, card_index, Nat.mul_assoc]⟩

theorem stage_cost_bound (U V L : ℕ) (right : Bool)
    (sourceSteps : List (Fock R →ₗ[R] Fock R))
    (hlen : sourceSteps.length ≤ (Fock.raisingSteps R L).length + 2) :
    2 * stateCount U * stateCount V * ((kernelSteps R right L).length + sourceSteps.length) ≤
      16 * (L+1)^2 * stateCount U * stateCount V := by
  have hkernel : (kernelSteps R right L).length ≤ 4*(Fock.raisingSteps R L).length + 2*L+2 := by
    cases right with
    | false => simpa only [kernelSteps, Bool.false_eq_true, ite_false, length_leftKernelSteps] using
        (le_rfl : 4*(Fock.raisingSteps R L).length + 2*L+2 ≤ 4*(Fock.raisingSteps R L).length + 2*L+2)
    | true => simp only [kernelSteps, ite_true, length_rightKernelSteps]; omega
  have hraising : 2*(Fock.raisingSteps R L).length ≤ L^2 := by
    rw [Fock.length_raisingSteps, pow_two]
    exact Nat.mul_le_mul_left L (Nat.sub_le L 1)
  have hcount : 2*((kernelSteps R right L).length + sourceSteps.length) ≤ 16*(L+1)^2 := by
    nlinarith
  calc
    2 * stateCount U * stateCount V * ((kernelSteps R right L).length + sourceSteps.length) =
        (stateCount U * stateCount V) * (2*((kernelSteps R right L).length + sourceSteps.length)) := by ring
    _ ≤ (stateCount U * stateCount V) * (16*(L+1)^2) := Nat.mul_le_mul_left _ hcount
    _ = _ := by ring

theorem source_prefix_length (right : Bool) (L : ℕ) (c : Finset (ℕ ⊕ₗ ℕ) → R) :
    ([coefficientDiagonal R c] ++ lowerColourSteps R right L).length =
      (Fock.raisingSteps R L).length + 2 := by
  simp only [lowerColourSteps, colourSteps, Fock.transposedSteps, List.length_append,
    List.length_singleton, List.length_map, List.length_reverse]
  omega

theorem source_prefix_sparse (right : Bool) (L : ℕ) (c : Finset (ℕ ⊕ₗ ℕ) → R) :
    ∀ T ∈ [coefficientDiagonal R c] ++ lowerColourSteps R right L, SparseColumns R T := by
  intro T hT
  rcases List.mem_append.mp hT with hT | hT
  · have ht := List.mem_singleton.mp hT
    subst T
    exact coefficientDiagonal_sparse R c
  · exact lowerColourSteps_sparse R right L T hT

theorem source_prefix_preserves (U V L : ℕ) (right : Bool) (c : Finset (ℕ ⊕ₗ ℕ) → R) :
    ∀ T ∈ [coefficientDiagonal R c] ++ lowerColourSteps R right L,
      let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
      P.comp (T.comp P) = T.comp P := by
  intro T hT
  rcases List.mem_append.mp hT with hT | hT
  · have ht := List.mem_singleton.mp hT
    subst T
    exact coefficientDiagonal_preserves R U V c
  · exact lowerColourSteps_preserves_rectangle R U V L right T hT

end

end Lemmata.FockCircuits.KernelBanks
