module

public import Lemmata.FockCircuits.KernelPipeline

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.KernelSafety

open FiniteIdentity KernelRectangle KernelAlgorithm KernelTruncation KernelSupports KernelStages
open KernelTransforms KernelPipeline

noncomputable section

variable (R : Type*) [CommRing R]

def outerSteps (L : ℕ) : List (Fock R →ₗ[R] Fock R) :=
  factorSteps R L ++ colourSteps R false (Fock.raisingSteps R L) ++
    colourSteps R true (Fock.raisingSteps R L)

def rightCoreSteps (L : ℕ) : List (Fock R →ₗ[R] Fock R) :=
  lowerColourSteps R true L ++ rawSteps R (rightSplitTriples R (Finset.range L).toList)

def leftCoreSteps (L : ℕ) : List (Fock R →ₗ[R] Fock R) :=
  lowerColourSteps R false L ++ rawSteps R (leftSplitTriples R (Finset.range L).toList) ++
    lowerColourSteps R false L

theorem colourShear_preserves_rectangle (U V : ℕ) (right : Bool)
    (a : R) (i j : ℕ) (hji : j ≤ i) :
    let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
    P.comp ((colourShear R right (i,j,a)).toLinearMap.comp P) =
      (colourShear R right (i,j,a)).toLinearMap.comp P := by
  dsimp only
  simp only [rectangle_eq_filters, leftFilter, rightFilter, colourFilter_comp]
  apply preserves_colourFilter
  intro I J
  cases right with
  | false =>
    obtain ⟨I', c, h, hc | he⟩ := left_shear_basis_sparse R a i j I J
    · refine ⟨I, J, 0, ?_, fun hp => hp⟩
      simpa only [colourShear, Bool.false_eq_true, ite_false, AlgHom.toLinearMap_apply,
        hc, zero_smul, add_zero] using h
    · exact ⟨I', J, c, h, fun hp => ⟨by have := hp.1; omega, hp.2⟩⟩
  | true =>
    obtain ⟨J', c, h, hc | he⟩ := right_shear_basis_sparse R a i j I J
    · refine ⟨I, J, 0, ?_, fun hp => hp⟩
      simpa only [colourShear, ite_true, AlgHom.toLinearMap_apply,
        hc, zero_smul, add_zero] using h
    · exact ⟨I, J', c, h, fun hp => ⟨hp.1, by have := hp.2; omega⟩⟩

theorem diagonal_preserves_rectangle (U V : ℕ) (a : ℕ → R) :
    let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
    P.comp ((diagonalMap R a).toLinearMap.comp P) = (diagonalMap R a).toLinearMap.comp P := by
  dsimp only
  simp only [rectangle_eq_filters, leftFilter, rightFilter, colourFilter_comp]
  exact diagonal_preserves_colourFilter R _ a

theorem lowerColourSteps_preserves_rectangle (U V L : ℕ) (right : Bool) :
    ∀ T ∈ lowerColourSteps R right L,
      let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
      P.comp (T.comp P) = T.comp P := by
  intro T hT
  rcases List.mem_append.mp hT with hT | hT
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hT
    exact colourShear_preserves_rectangle R U V right s.2.2 s.1 s.2.1
      (Fock.transposed_raisingSteps_oriented R L s hs).le
  · have hTeq := List.mem_singleton.mp hT
    subst T
    exact diagonal_preserves_rectangle R U V (colourSignCoefficient R right)

theorem colourShear_no_return_rectangle (U V : ℕ) (right : Bool)
    (a : R) (i j : ℕ) (hij : i ≤ j) :
    let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
    P.comp ((colourShear R right (i,j,a)).toLinearMap.comp P) =
      P.comp (colourShear R right (i,j,a)).toLinearMap := by
  dsimp only
  simp only [rectangle_eq_filters, leftFilter, rightFilter, colourFilter_comp]
  apply no_return_colourFilter
  intro I J
  cases right with
  | false =>
    obtain ⟨I', c, h, hc | he⟩ := left_shear_basis_sparse R a i j I J
    · refine ⟨I, J, 0, ?_, fun hp => hp⟩
      simpa only [colourShear, Bool.false_eq_true, ite_false, AlgHom.toLinearMap_apply,
        hc, zero_smul, add_zero] using h
    · exact ⟨I', J, c, h, fun hp => ⟨by have := hp.1; omega, hp.2⟩⟩
  | true =>
    obtain ⟨J', c, h, hc | he⟩ := right_shear_basis_sparse R a i j I J
    · refine ⟨I, J, 0, ?_, fun hp => hp⟩
      simpa only [colourShear, ite_true, AlgHom.toLinearMap_apply,
        hc, zero_smul, add_zero] using h
    · exact ⟨I, J', c, h, fun hp => ⟨hp.1, by have := hp.2; omega⟩⟩

theorem outerSteps_no_return (U V L : ℕ) :
    ∀ T ∈ outerSteps R L,
      let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
      P.comp (T.comp P) = P.comp T := by
  intro T hT
  simp only [outerSteps, List.append_assoc, List.mem_append] at hT
  rcases hT with hT | hT | hT
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hT
    exact factor_no_return_rectangle R U V m
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hT
    exact colourShear_no_return_rectangle R U V false s.2.2 s.1 s.2.1
      (Fock.raisingSteps_oriented R L s hs).le
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hT
    exact colourShear_no_return_rectangle R U V true s.2.2 s.1 s.2.1
      (Fock.raisingSteps_oriented R L s hs).le

theorem lowerRight_safe (U V L : ℕ) :
    ∀ T ∈ lowerColourSteps R true L,
      (leftFilter R U).comp (T.comp (leftFilter R U)) = (leftFilter R U).comp T ∧
      (rightFilter R V).comp (T.comp (rightFilter R V)) = T.comp (rightFilter R V) := by
  intro T hT
  rcases List.mem_append.mp hT with hT | hT
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hT
    exact ⟨right_shear_no_return_left R U s.2.2 s.1 s.2.1,
      right_shear_preserves_right R V s.2.2 s.1 s.2.1
        (Fock.transposed_raisingSteps_oriented R L s hs).le⟩
  · have ht := List.mem_singleton.mp hT
    subst T
    exact ⟨diagonal_no_return_colourFilter R (fun I _ => doubledEnergy I ≤ 2*U)
      (colourSignCoefficient R true),
      diagonal_preserves_colourFilter R (fun _ J => doubledEnergy J ≤ 2*V)
        (colourSignCoefficient R true)⟩

theorem lowerLeft_safe (U V L : ℕ) :
    ∀ T ∈ lowerColourSteps R false L,
      (rightFilter R V).comp (T.comp (rightFilter R V)) = (rightFilter R V).comp T ∧
      (leftFilter R U).comp (T.comp (leftFilter R U)) = T.comp (leftFilter R U) := by
  intro T hT
  rcases List.mem_append.mp hT with hT | hT
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hT
    exact ⟨left_shear_no_return_right R V s.2.2 s.1 s.2.1,
      left_shear_preserves_left R U s.2.2 s.1 s.2.1
        (Fock.transposed_raisingSteps_oriented R L s hs).le⟩
  · have ht := List.mem_singleton.mp hT
    subst T
    exact ⟨diagonal_no_return_colourFilter R (fun _ J => doubledEnergy J ≤ 2*V)
      (colourSignCoefficient R false),
      diagonal_preserves_colourFilter R (fun I _ => doubledEnergy I ≤ 2*U)
        (colourSignCoefficient R false)⟩

theorem rightCore_safe (U V L : ℕ) :
    ∀ T ∈ rightCoreSteps R L,
      (leftFilter R U).comp (T.comp (leftFilter R U)) = (leftFilter R U).comp T ∧
      (rightFilter R V).comp (T.comp (rightFilter R V)) = T.comp (rightFilter R V) := by
  intro T hT
  rcases List.mem_append.mp hT with hT | hT
  · exact lowerRight_safe R U V L T hT
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hT
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hs
    exact ⟨right_split_no_return_left R U m, right_split_preserves_right R V m⟩

theorem leftCore_safe (U V L : ℕ) :
    ∀ T ∈ leftCoreSteps R L,
      (rightFilter R V).comp (T.comp (rightFilter R V)) = (rightFilter R V).comp T ∧
      (leftFilter R U).comp (T.comp (leftFilter R U)) = T.comp (leftFilter R U) := by
  intro T hT
  simp only [leftCoreSteps, List.append_assoc, List.mem_append] at hT
  rcases hT with hT | hT | hT
  · exact lowerLeft_safe R U V L T hT
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hT
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hs
    exact ⟨left_split_no_return_right R V m, left_split_preserves_left R U m⟩
  · exact lowerLeft_safe R U V L T hT

theorem rightKernel_restriction (U V L : ℕ) :
    let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
    (maskedSteps P (rightKernelSteps R L)).comp P =
      P.comp ((actualSteps (rightKernelSteps R L)).comp P) := by
  have hid p := basisFilter_idempotent (colourBasis R) p
  have hc := colourFilter_commute R (fun I _ => doubledEnergy I ≤ 2*U)
    (fun _ J => doubledEnergy J ≤ 2*V)
  have h := maskedSteps_two_phases (leftFilter R U) (rightFilter R V)
    (hid _) (hid _) hc (outerSteps R L) (rightCoreSteps R L)
    (by simpa only [← rectangle_eq_filters] using outerSteps_no_return R U V L)
    (fun T hT => (rightCore_safe R U V L T hT).1)
    (fun T hT => (rightCore_safe R U V L T hT).2)
  simpa only [← rectangle_eq_filters, outerSteps, rightCoreSteps,
    rightKernelSteps, rightPipelineSteps, List.append_assoc] using h

theorem leftKernel_restriction (U V L : ℕ) :
    let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
    (maskedSteps P (leftKernelSteps R L)).comp P =
      P.comp ((actualSteps (leftKernelSteps R L)).comp P) := by
  have hid p := basisFilter_idempotent (colourBasis R) p
  have hc := colourFilter_commute R (fun _ J => doubledEnergy J ≤ 2*V)
    (fun I _ => doubledEnergy I ≤ 2*U)
  have hrect : (rightFilter R V).comp (leftFilter R U) =
      projection (colourBasis R) (basisIndex (U := U) (V := V)) := by
    rw [rectangle_eq_filters]
    exact hc
  have h := maskedSteps_two_phases (rightFilter R V) (leftFilter R U)
    (hid _) (hid _) hc (outerSteps R L) (leftCoreSteps R L)
    (by simpa only [hrect] using outerSteps_no_return R U V L)
    (fun T hT => (leftCore_safe R U V L T hT).1)
    (fun T hT => (leftCore_safe R U V L T hT).2)
  simpa only [hrect, outerSteps, leftCoreSteps, leftKernelSteps, leftPipelineSteps,
    List.append_assoc] using h

theorem rightKernel_coefficientMatrix (U V L : ℕ) :
    coefficientMatrix (colourBasis R) (basisIndex (U := U) (V := V))
      (maskedSteps (projection (colourBasis R) (basisIndex (U := U) (V := V))) (rightKernelSteps R L)) =
    coefficientMatrix (colourBasis R) (basisIndex (U := U) (V := V))
      (actualSteps (rightKernelSteps R L)) :=
  coefficientMatrix_of_restriction _ _ (basisIndex_injective U V) _ _ (rightKernel_restriction R U V L)

theorem leftKernel_coefficientMatrix (U V L : ℕ) :
    coefficientMatrix (colourBasis R) (basisIndex (U := U) (V := V))
      (maskedSteps (projection (colourBasis R) (basisIndex (U := U) (V := V))) (leftKernelSteps R L)) =
    coefficientMatrix (colourBasis R) (basisIndex (U := U) (V := V))
      (actualSteps (leftKernelSteps R L)) :=
  coefficientMatrix_of_restriction _ _ (basisIndex_injective U V) _ _ (leftKernel_restriction R U V L)

end

end Lemmata.FockCircuits.KernelSafety
