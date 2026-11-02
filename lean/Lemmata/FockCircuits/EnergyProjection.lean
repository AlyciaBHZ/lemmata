module

public import Lemmata.FockCircuits.Shear

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Fock

variable (R : Type*) [CommRing R]

noncomputable def energyProjection (E : ℕ) : Fock R →ₗ[R] Fock R :=
  (basis R).constr R fun I => if doubledEnergy I ≤ E then basis R I else 0

@[simp] theorem energyProjection_basis (E : ℕ) (I : Finset ℕ) :
    energyProjection R E (basis R I) =
      if doubledEnergy I ≤ E then basis R I else 0 := by
  simp [energyProjection]

theorem energyProjection_idempotent (E : ℕ) :
    (energyProjection R E).comp (energyProjection R E) = energyProjection R E := by
  apply (basis R).ext
  intro I
  by_cases hI : doubledEnergy I ≤ E <;> simp [hI]

theorem lowering_preserves_projection (a : R) {i j : ℕ} (hji : j ≤ i) (E : ℕ) :
    (energyProjection R E).comp
        ((shear R a i j).toLinearMap.comp (energyProjection R E)) =
      (shear R a i j).toLinearMap.comp (energyProjection R E) := by
  apply (basis R).ext
  intro I
  obtain ⟨J, c, hc, hJ⟩ := shear_basis_lowering R a hji I
  by_cases hI : doubledEnergy I ≤ E
  · have hJE := hJ.trans hI
    simp only [LinearMap.comp_apply, energyProjection_basis, ite_eq_left hI,
      AlgHom.toLinearMap_apply, hc, map_add, map_smul, ite_eq_left hJE]
  · simp [hI]

theorem raising_cannot_return (a : R) {i j : ℕ} (hij : i ≤ j) (E : ℕ) :
    (energyProjection R E).comp
        ((shear R a i j).toLinearMap.comp (energyProjection R E)) =
      (energyProjection R E).comp (shear R a i j).toLinearMap := by
  apply (basis R).ext
  intro I
  obtain ⟨J, c, hc, hJ⟩ := shear_basis_raising R a hij I
  by_cases hI : doubledEnergy I ≤ E
  · simp only [LinearMap.comp_apply, energyProjection_basis, ite_eq_left hI]
  · have hJE : ¬ doubledEnergy J ≤ E := fun h => hI (hJ.trans h)
    simp [hI, hc, hJE]

theorem raising_homogeneous_diagonal (a : R) {i j : ℕ} (hij : i < j)
    (I : Finset ℕ) :
    energyProjection R (doubledEnergy I) (shear R a i j (basis R I)) = basis R I := by
  obtain ⟨J, c, hc, he⟩ := shear_basis_sparse_energy R a i j I
  rw [hc]
  rcases he with rfl | he
  · simp
  · have hJ : ¬ doubledEnergy J ≤ doubledEnergy I := by omega
    simp [hJ]

noncomputable def parityProjection (p : ℕ) : Fock R →ₗ[R] Fock R :=
  (basis R).constr R fun I => if doubledEnergy I % 2 = p then basis R I else 0

@[simp] theorem parityProjection_basis (p : ℕ) (I : Finset ℕ) :
    parityProjection R p (basis R I) =
      if doubledEnergy I % 2 = p then basis R I else 0 := by
  simp [parityProjection]

set_option backward.isDefEq.respectTransparency false in
private theorem selected_basis_coefficient (P : Finset ℕ → Prop) [DecidablePred P]
    (x : Fock R) (J : Finset ℕ) :
    (basis R).repr ((basis R).constr R (fun I => if P I then basis R I else 0) x) J =
      if P J then (basis R).repr x J else 0 := by
  classical
  let F : Fock R →ₗ[R] R :=
    (Finsupp.lapply J).comp ((basis R).repr.toLinearMap.comp
      ((basis R).constr R (fun I => if P I then basis R I else 0)))
  let G : Fock R →ₗ[R] R :=
    if P J then (Finsupp.lapply J).comp (basis R).repr.toLinearMap else 0
  have h : F = G := by
    apply (basis R).ext
    intro I
    by_cases hJ : P J <;>
      by_cases hI : P I <;>
      by_cases hIJ : I = J <;> simp_all [F, G, Finsupp.single_apply]
  by_cases hJ : P J <;>
    simpa [F, G, hJ] using LinearMap.congr_fun h x

theorem energyProjection_coefficient (E : ℕ) (x : Fock R) (J : Finset ℕ) :
    (basis R).repr (energyProjection R E x) J =
      if doubledEnergy J ≤ E then (basis R).repr x J else 0 :=
  selected_basis_coefficient R (fun I => doubledEnergy I ≤ E) x J

theorem parityProjection_coefficient (p : ℕ) (x : Fock R) (J : Finset ℕ) :
    (basis R).repr (parityProjection R p x) J =
      if doubledEnergy J % 2 = p then (basis R).repr x J else 0 :=
  selected_basis_coefficient R (fun I => doubledEnergy I % 2 = p) x J

theorem shear_parityProjection (a : R) (i j p : ℕ) :
    (parityProjection R p).comp (shear R a i j).toLinearMap =
      (shear R a i j).toLinearMap.comp (parityProjection R p) := by
  apply (basis R).ext
  intro I
  obtain ⟨J, c, hc, he⟩ := shear_basis_sparse_energy R a i j I
  rcases he with rfl | he
  · by_cases hI : doubledEnergy I % 2 = p <;> simp [hc, hI]
  · have hJ : doubledEnergy J % 2 = doubledEnergy I % 2 := by omega
    by_cases hI : doubledEnergy I % 2 = p <;> simp [hc, hI, hJ]

end Lemmata.FockCircuits.Fock
