module

public import Lemmata.FockCircuits.KernelAlgorithm
public import Lemmata.FockCircuits.KernelTruncation

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.KernelSupports

open FiniteIdentity KernelRectangle KernelAlgorithm KernelTruncation

noncomputable section

variable (R : Type*) [CommRing R]

theorem colourIndex_surjective (K : Finset (ℕ ⊕ₗ ℕ)) :
    ∃ I J : Finset ℕ, colourIndex I J = K := by
  classical
  induction K using Finset.induction_on with
  | empty => exact ⟨∅, ∅, by simp [colourIndex]⟩
  | @insert k K hk ih =>
    obtain ⟨I, J, rfl⟩ := ih
    obtain ⟨s, rfl⟩ : ∃ s : ℕ ⊕ ℕ, toLex s = k := ⟨ofLex k, rfl⟩
    cases s with
    | inl i => exact ⟨insert i I, J, by simp [colourIndex]⟩
    | inr j => exact ⟨I, insert j J, by simp [colourIndex]⟩

def colourProperty (p : Finset ℕ → Finset ℕ → Prop) (K : Finset (ℕ ⊕ₗ ℕ)) : Prop :=
  ∃ I J, colourIndex I J = K ∧ p I J

@[simp] theorem colourProperty_index (p : Finset ℕ → Finset ℕ → Prop) (I J : Finset ℕ) :
    colourProperty p (colourIndex I J) ↔ p I J := by
  constructor
  · rintro ⟨I', J', h, hp⟩
    obtain ⟨rfl, rfl⟩ := (colourIndex_eq_iff _ _ _ _).mp h
    exact hp
  · exact fun hp => ⟨I, J, rfl, hp⟩

def colourFilter (p : Finset ℕ → Finset ℕ → Prop) : Fock R →ₗ[R] Fock R :=
  basisFilter (colourBasis R) (colourProperty p)

@[simp] theorem colourFilter_basis (p : Finset ℕ → Finset ℕ → Prop) [DecidableRel p]
    (I J : Finset ℕ) :
    colourFilter R p (colourBasis R (colourIndex I J)) =
      if p I J then colourBasis R (colourIndex I J) else 0 := by
  classical
  simp [colourFilter]

theorem colourFilter_comp (p q : Finset ℕ → Finset ℕ → Prop) :
    (colourFilter R p).comp (colourFilter R q) = colourFilter R (fun I J => p I J ∧ q I J) := by
  apply (colourBasis R).ext
  intro K
  obtain ⟨I, J, rfl⟩ := colourIndex_surjective K
  classical
  by_cases hp : p I J <;> by_cases hq : q I J <;> simp [hp, hq]

theorem colourFilter_commute (p q : Finset ℕ → Finset ℕ → Prop) :
    (colourFilter R p).comp (colourFilter R q) = (colourFilter R q).comp (colourFilter R p) := by
  apply basisFilter_commute

def leftFilter (U : ℕ) : Fock R →ₗ[R] Fock R :=
  colourFilter R fun I _ => doubledEnergy I ≤ 2 * U

def rightFilter (V : ℕ) : Fock R →ₗ[R] Fock R :=
  colourFilter R fun _ J => doubledEnergy J ≤ 2 * V

theorem rectangle_eq_filters (U V : ℕ) :
    projection (colourBasis R) (basisIndex (U := U) (V := V)) =
      (leftFilter R U).comp (rightFilter R V) := by
  classical
  rw [projection_eq_basisFilter _ _ (basisIndex_injective U V)]
  change basisFilter (colourBasis R) _ =
    (colourFilter R (fun I _ => doubledEnergy I ≤ 2 * U)).comp
      (colourFilter R (fun _ J => doubledEnergy J ≤ 2 * V))
  rw [colourFilter_comp]
  apply (colourBasis R).ext
  intro K
  obtain ⟨I, J, rfl⟩ := colourIndex_surjective K
  have hmem : (∃ d : Index U V, basisIndex d = colourIndex I J) ↔
      doubledEnergy I ≤ 2 * U ∧ doubledEnergy J ≤ 2 * V := by
    constructor
    · rintro ⟨d, hd⟩
      obtain ⟨hI, hJ⟩ := (colourIndex_eq_iff _ _ _ _).mp hd
      exact ⟨by simpa only [hI] using mem_fullCutoff.mp d.1.property,
        by simpa only [hJ] using mem_fullCutoff.mp d.2.property⟩
    · rintro ⟨hI, hJ⟩
      exact ⟨(⟨I, mem_fullCutoff.mpr hI⟩, ⟨J, mem_fullCutoff.mpr hJ⟩), rfl⟩
  simp only [basisFilter_basis, hmem, colourFilter_basis]

theorem preserves_colourFilter (p : Finset ℕ → Finset ℕ → Prop) (T : Fock R →ₗ[R] Fock R)
    (hT : ∀ I J, ∃ I' J' : Finset ℕ, ∃ c : R,
      T (colourBasis R (colourIndex I J)) = colourBasis R (colourIndex I J) +
        c • colourBasis R (colourIndex I' J') ∧ (p I J → p I' J')) :
    (colourFilter R p).comp (T.comp (colourFilter R p)) = T.comp (colourFilter R p) := by
  apply preserves_filter_of_sparse
  intro K
  obtain ⟨I, J, rfl⟩ := colourIndex_surjective K
  obtain ⟨I', J', c, h, hp⟩ := hT I J
  exact ⟨colourIndex I' J', c, h, by simpa only [colourProperty_index] using hp⟩

theorem no_return_colourFilter (p : Finset ℕ → Finset ℕ → Prop) (T : Fock R →ₗ[R] Fock R)
    (hT : ∀ I J, ∃ I' J' : Finset ℕ, ∃ c : R,
      T (colourBasis R (colourIndex I J)) = colourBasis R (colourIndex I J) +
        c • colourBasis R (colourIndex I' J') ∧ (p I' J' → p I J)) :
    (colourFilter R p).comp (T.comp (colourFilter R p)) = (colourFilter R p).comp T := by
  apply no_return_filter_of_sparse
  intro K
  obtain ⟨I, J, rfl⟩ := colourIndex_surjective K
  obtain ⟨I', J', c, h, hp⟩ := hT I J
  exact ⟨colourIndex I' J', c, h, by simpa only [colourProperty_index] using hp⟩

theorem left_shear_preserves_left (U : ℕ) (a : R) (i j : ℕ) (hji : j ≤ i) :
    (leftFilter R U).comp ((Fock.shear R a (2*i) (2*j)).toLinearMap.comp (leftFilter R U)) =
      (Fock.shear R a (2*i) (2*j)).toLinearMap.comp (leftFilter R U) := by
  apply preserves_colourFilter
  intro I J
  obtain ⟨I', c, h, hc | he⟩ := left_shear_basis_sparse R a i j I J
  · exact ⟨I, J, 0, by simpa only [AlgHom.toLinearMap_apply, hc, zero_smul, add_zero] using h, fun hp => hp⟩
  · exact ⟨I', J, c, h, fun hp => by change doubledEnergy I ≤ 2 * U at hp; omega⟩

theorem left_shear_no_return_left (U : ℕ) (a : R) (i j : ℕ) (hij : i ≤ j) :
    (leftFilter R U).comp ((Fock.shear R a (2*i) (2*j)).toLinearMap.comp (leftFilter R U)) =
      (leftFilter R U).comp (Fock.shear R a (2*i) (2*j)).toLinearMap := by
  apply no_return_colourFilter
  intro I J
  obtain ⟨I', c, h, hc | he⟩ := left_shear_basis_sparse R a i j I J
  · exact ⟨I, J, 0, by simpa only [AlgHom.toLinearMap_apply, hc, zero_smul, add_zero] using h, fun hp => hp⟩
  · exact ⟨I', J, c, h, fun hp => by change doubledEnergy I' ≤ 2 * U at hp; omega⟩

theorem right_shear_preserves_right (V : ℕ) (a : R) (i j : ℕ) (hji : j ≤ i) :
    (rightFilter R V).comp ((Fock.shear R a (2*i+1) (2*j+1)).toLinearMap.comp (rightFilter R V)) =
      (Fock.shear R a (2*i+1) (2*j+1)).toLinearMap.comp (rightFilter R V) := by
  apply preserves_colourFilter
  intro I J
  obtain ⟨J', c, h, hc | he⟩ := right_shear_basis_sparse R a i j I J
  · exact ⟨I, J, 0, by simpa only [AlgHom.toLinearMap_apply, hc, zero_smul, add_zero] using h, fun hp => hp⟩
  · exact ⟨I, J', c, h, fun hp => by change doubledEnergy J ≤ 2 * V at hp; omega⟩

theorem right_shear_no_return_right (V : ℕ) (a : R) (i j : ℕ) (hij : i ≤ j) :
    (rightFilter R V).comp ((Fock.shear R a (2*i+1) (2*j+1)).toLinearMap.comp (rightFilter R V)) =
      (rightFilter R V).comp (Fock.shear R a (2*i+1) (2*j+1)).toLinearMap := by
  apply no_return_colourFilter
  intro I J
  obtain ⟨J', c, h, hc | he⟩ := right_shear_basis_sparse R a i j I J
  · exact ⟨I, J, 0, by simpa only [AlgHom.toLinearMap_apply, hc, zero_smul, add_zero] using h, fun hp => hp⟩
  · exact ⟨I, J', c, h, fun hp => by change doubledEnergy J' ≤ 2 * V at hp; omega⟩

theorem right_split_preserves_right (V m : ℕ) :
    (rightFilter R V).comp ((Fock.shear R 1 (2*m+1) (2*m)).toLinearMap.comp (rightFilter R V)) =
      (Fock.shear R 1 (2*m+1) (2*m)).toLinearMap.comp (rightFilter R V) := by
  apply preserves_colourFilter
  intro I J
  obtain ⟨I', J', c, h, _, hJ⟩ := split_right_sparse R m I J
  exact ⟨I', J', c, h, fun hp => hJ.trans hp⟩

theorem right_split_no_return_left (U m : ℕ) :
    (leftFilter R U).comp ((Fock.shear R 1 (2*m+1) (2*m)).toLinearMap.comp (leftFilter R U)) =
      (leftFilter R U).comp (Fock.shear R 1 (2*m+1) (2*m)).toLinearMap := by
  apply no_return_colourFilter
  intro I J
  obtain ⟨I', J', c, h, hI, _⟩ := split_right_sparse R m I J
  exact ⟨I', J', c, h, fun hp => hI.trans hp⟩

theorem left_split_preserves_left (U m : ℕ) :
    (leftFilter R U).comp ((Fock.shear R 1 (2*m) (2*m+1)).toLinearMap.comp (leftFilter R U)) =
      (Fock.shear R 1 (2*m) (2*m+1)).toLinearMap.comp (leftFilter R U) := by
  apply preserves_colourFilter
  intro I J
  obtain ⟨I', J', c, h, hI, _⟩ := split_left_sparse R m I J
  exact ⟨I', J', c, h, fun hp => hI.trans hp⟩

theorem left_split_no_return_right (V m : ℕ) :
    (rightFilter R V).comp ((Fock.shear R 1 (2*m) (2*m+1)).toLinearMap.comp (rightFilter R V)) =
      (rightFilter R V).comp (Fock.shear R 1 (2*m) (2*m+1)).toLinearMap := by
  apply no_return_colourFilter
  intro I J
  obtain ⟨I', J', c, h, _, hJ⟩ := split_left_sparse R m I J
  exact ⟨I', J', c, h, fun hp => hJ.trans hp⟩

theorem factor_no_return_rectangle (U V m : ℕ) :
    let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
    P.comp ((LinearMap.mulRight R (TwoColour.factor R m)).comp P) =
      P.comp (LinearMap.mulRight R (TwoColour.factor R m)) := by
  dsimp only
  rw [rectangle_eq_filters, leftFilter, rightFilter, colourFilter_comp]
  apply no_return_colourFilter
  intro I J
  obtain ⟨I', J', c, h, hI, hJ⟩ := factor_sparse R m I J
  exact ⟨I', J', c, h, fun hp => ⟨hI.trans hp.1, hJ.trans hp.2⟩⟩

theorem diagonal_preserves_colourFilter (p : Finset ℕ → Finset ℕ → Prop) (a : ℕ → R) :
    (colourFilter R p).comp ((diagonalMap R a).toLinearMap.comp (colourFilter R p)) =
      (diagonalMap R a).toLinearMap.comp (colourFilter R p) := by
  apply preserves_colourFilter
  intro I J
  obtain ⟨c, h⟩ := diagonal_sparse R a I J
  exact ⟨I, J, c, h, fun hp => hp⟩

theorem diagonal_no_return_colourFilter (p : Finset ℕ → Finset ℕ → Prop) (a : ℕ → R) :
    (colourFilter R p).comp ((diagonalMap R a).toLinearMap.comp (colourFilter R p)) =
      (colourFilter R p).comp (diagonalMap R a).toLinearMap := by
  apply no_return_colourFilter
  intro I J
  obtain ⟨c, h⟩ := diagonal_sparse R a I J
  exact ⟨I, J, c, h, fun hp => hp⟩

end

end Lemmata.FockCircuits.KernelSupports
