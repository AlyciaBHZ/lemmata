module

public import Lemmata.FockCircuits.Shear
public import Lemmata.FockCircuits.Partition
public import Lemmata.FockCircuits.SparseCircuit
public import Lemmata.FockCircuits.EnergyProjection
public import Lemmata.FockCircuits.PascalShears

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.Fock

variable (R : Type*) [CommRing R]

theorem exists_projected_shear_circuit {X : Type*} (H : ℕ) (a : R)
    (i j : ℕ) (bank : CircuitFamily R X ↥(fullCutoff H)) :
    ∃ p : CircuitFamily R X ↥(fullCutoff H),
      p.size = bank.size + 2 * stateCount H ∧
      ∀ x : X → R,
        (∑ I, p.eval id x I • basis R I.val) =
          energyProjection R (2 * H)
            (shear R a i j (∑ I, bank.eval id x I • basis R I.val)) := by
  classical
  let T := (energyProjection R (2 * H)).comp (shear R a i j).toLinearMap
  have hcol : ∀ I : ↥(fullCutoff H), ∃ J : ↥(fullCutoff H), ∃ c : R,
      T (basis R I.val) = basis R I.val + c • basis R J.val := by
    intro I
    obtain ⟨J, c, hc, _⟩ := shear_basis_sparse_energy R a i j I.val
    have hI := mem_fullCutoff.mp I.property
    by_cases hJ : doubledEnergy J ≤ 2 * H
    · refine ⟨⟨J, mem_fullCutoff.mpr hJ⟩, c, ?_⟩
      simp [T, hc, hI, hJ]
    · refine ⟨I, 0, ?_⟩
      simp [T, hc, hI, hJ]
  choose target c hc using hcol
  refine ⟨SparseCircuit.scatter bank target c, ?_, ?_⟩
  · simp [stateCount]
  · intro x
    exact SparseCircuit.scatter_realizes_linearMap bank target c x
      (fun I => basis R I.val) T hc

theorem exists_lowering_circuit {X : Type*} (H : ℕ) (a : R)
    {i j : ℕ} (hji : j ≤ i) (bank : CircuitFamily R X ↥(fullCutoff H)) :
    ∃ p : CircuitFamily R X ↥(fullCutoff H),
      p.size = bank.size + 2 * stateCount H ∧
      ∀ x : X → R,
        (∑ I, p.eval id x I • basis R I.val) =
          shear R a i j (∑ I, bank.eval id x I • basis R I.val) := by
  classical
  choose J c hc hJ using fun I : ↥(fullCutoff H) =>
    shear_basis_lowering R a hji I.val
  let target : ↥(fullCutoff H) → ↥(fullCutoff H) := fun I =>
    ⟨J I, mem_fullCutoff.mpr ((hJ I).trans (mem_fullCutoff.mp I.property))⟩
  refine ⟨SparseCircuit.scatter bank target c, ?_, ?_⟩
  · simp [stateCount]
  · intro x
    exact SparseCircuit.scatter_realizes_linearMap bank target c x
      (fun I => basis R I.val) (shear R a i j).toLinearMap hc

theorem projection_realize_cutoff (H : ℕ) (v : ↥(fullCutoff H) → R) :
    energyProjection R (2 * H) (∑ I, v I • basis R I.val) =
      ∑ I, v I • basis R I.val := by
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro I hI
  rw [energyProjection_basis, ite_eq_left (mem_fullCutoff.mp I.property)]

theorem exists_raising_circuit {X : Type*} (H : ℕ)
    (steps : List (ℕ × ℕ × R))
    (horient : ∀ s ∈ steps, s.1 ≤ s.2.1)
    (bank : CircuitFamily R X ↥(fullCutoff H)) :
    ∃ p : CircuitFamily R X ↥(fullCutoff H),
      p.size = bank.size + 2 * stateCount H * steps.length ∧
      ∀ x : X → R,
        (∑ I, p.eval id x I • basis R I.val) =
          energyProjection R (2 * H)
            (ExteriorAlgebra.map (linearShears R steps)
              (∑ I, bank.eval id x I • basis R I.val)) := by
  induction steps with
  | nil =>
    refine ⟨bank, by simp, ?_⟩
    intro x
    simp only [linearShears, ExteriorAlgebra.map_id, AlgHom.id_apply]
    exact (projection_realize_cutoff R H (bank.eval id x)).symm
  | cons s rest ih =>
    have hs : s.1 ≤ s.2.1 := horient s (by simp)
    obtain ⟨q, hq, hqx⟩ := ih (fun t ht => horient t (by simp [ht]))
    obtain ⟨p, hp, hpx⟩ := exists_projected_shear_circuit R H s.2.2 s.1 s.2.1 q
    refine ⟨p, ?_, ?_⟩
    · rw [hp, hq, List.length_cons]
      ring
    · intro x
      rw [hpx, hqx]
      have he := LinearMap.congr_fun (raising_cannot_return R s.2.2 hs (2 * H))
        (ExteriorAlgebra.map (linearShears R rest)
          (∑ I, bank.eval id x I • basis R I.val))
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at he
      rw [he]
      congr 1
      rw [linearShears, ← ExteriorAlgebra.map_comp_map]
      rfl

theorem exists_finitePascal_circuit {X : Type*} (H L : ℕ)
    (bank : CircuitFamily R X ↥(fullCutoff H)) :
    ∃ p : CircuitFamily R X ↥(fullCutoff H),
      p.size = bank.size + stateCount H * (L * (L - 1)) ∧
      ∀ x : X → R,
        (∑ I, p.eval id x I • basis R I.val) =
          energyProjection R (2 * H)
            (ExteriorAlgebra.map (finitePascal R L)
              (∑ I, bank.eval id x I • basis R I.val)) := by
  obtain ⟨p, hp, hpx⟩ := exists_raising_circuit R H (raisingSteps R L)
    (fun s hs => (raisingSteps_oriented R L s hs).le) bank
  refine ⟨p, ?_, ?_⟩
  · rw [hp, show 2 * stateCount H * (raisingSteps R L).length =
        stateCount H * (2 * (raisingSteps R L).length) by ring,
      length_raisingSteps]
  · intro x
    simpa only [raisingSteps_factorization] using hpx x

theorem raisingSteps_homogeneous_diagonal (steps : List (ℕ × ℕ × R))
    (horient : ∀ s ∈ steps, s.1 < s.2.1) (I : Finset ℕ) :
    energyProjection R (doubledEnergy I)
      (ExteriorAlgebra.map (linearShears R steps) (basis R I)) = basis R I := by
  induction steps with
  | nil => simp [linearShears, ExteriorAlgebra.map_id]
  | cons s rest ih =>
    have hs := horient s (by simp)
    have hi := ih (fun t ht => horient t (by simp [ht]))
    have he := LinearMap.congr_fun
      (raising_cannot_return R s.2.2 hs.le (doubledEnergy I))
      (ExteriorAlgebra.map (linearShears R rest) (basis R I))
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at he
    rw [linearShears, ← ExteriorAlgebra.map_comp_map]
    change energyProjection R (doubledEnergy I)
      (shear R s.2.2 s.1 s.2.1 (ExteriorAlgebra.map (linearShears R rest) (basis R I))) = _
    rw [← he, hi]
    exact raising_homogeneous_diagonal R s.2.2 hs I

theorem finitePascal_homogeneous_diagonal (L : ℕ) (I : Finset ℕ) :
    energyProjection R (doubledEnergy I)
      (ExteriorAlgebra.map (finitePascal R L) (basis R I)) = basis R I := by
  rw [← raisingSteps_factorization]
  exact raisingSteps_homogeneous_diagonal R (raisingSteps R L)
    (raisingSteps_oriented R L) I

theorem loweringSteps_preserves_projection (steps : List (ℕ × ℕ × R))
    (horient : ∀ s ∈ steps, s.2.1 ≤ s.1) (E : ℕ) (x : Fock R)
    (hx : energyProjection R E x = x) :
    energyProjection R E (ExteriorAlgebra.map (linearShears R steps) x) =
      ExteriorAlgebra.map (linearShears R steps) x := by
  induction steps with
  | nil => simpa [linearShears, ExteriorAlgebra.map_id] using hx
  | cons s rest ih =>
    have hs := horient s (by simp)
    have hi := ih (fun t ht => horient t (by simp [ht]))
    have he := LinearMap.congr_fun
      (lowering_preserves_projection R s.2.2 hs E)
      (ExteriorAlgebra.map (linearShears R rest) x)
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at he
    rw [hi] at he
    rw [linearShears, ← ExteriorAlgebra.map_comp_map]
    simpa only [AlgHom.comp_apply, shear] using he

theorem pascalExterior_basis_energy (I : Finset ℕ) :
    energyProjection R (doubledEnergy I) (pascalExterior R (basis R I)) =
      pascalExterior R (basis R I) := by
  let L := doubledEnergy I + 1
  have hI : ∀ i ∈ I, i < L := by
    intro i hi
    have h := Finset.single_le_sum (f := fun j : ℕ => 2 * j + 1)
      (fun j _ => Nat.zero_le _) hi
    change 2 * i + 1 ≤ doubledEnergy I at h
    dsimp [L]
    omega
  rw [pascalExterior_basis_factor R I hI, signDiagonal_basis, map_smul, map_smul]
  congr 1
  exact loweringSteps_preserves_projection R (transposedSteps R (raisingSteps R L))
    (fun s hs => (transposed_raisingSteps_oriented R L s hs).le)
    (doubledEnergy I) (basis R I) (by simp)

theorem pascalExteriorInverse_basis_energy (I : Finset ℕ) :
    energyProjection R (doubledEnergy I) (pascalExteriorInverse R (basis R I)) =
      pascalExteriorInverse R (basis R I) := by
  simpa only [pascalExteriorInverse_eq] using pascalExterior_basis_energy R I

theorem linearShears_parityProjection (steps : List (ℕ × ℕ × R)) (p : ℕ) (x : Fock R) :
    parityProjection R p (ExteriorAlgebra.map (linearShears R steps) x) =
      ExteriorAlgebra.map (linearShears R steps) (parityProjection R p x) := by
  induction steps generalizing x with
  | nil => simp [linearShears, ExteriorAlgebra.map_id]
  | cons s rest ih =>
    have he := LinearMap.congr_fun (shear_parityProjection R s.2.2 s.1 s.2.1 p)
      (ExteriorAlgebra.map (linearShears R rest) x)
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] at he
    rw [linearShears, ← ExteriorAlgebra.map_comp_map]
    change parityProjection R p
        (shear R s.2.2 s.1 s.2.1 (ExteriorAlgebra.map (linearShears R rest) x)) =
      shear R s.2.2 s.1 s.2.1
        (ExteriorAlgebra.map (linearShears R rest) (parityProjection R p x))
    rw [he, ih]

theorem pascalExterior_basis_parity {L : ℕ} (I : Finset ℕ)
    (hI : ∀ i ∈ I, i < L) :
    parityProjection R (doubledEnergy I % 2) (pascalExterior R (basis R I)) =
      pascalExterior R (basis R I) := by
  rw [pascalExterior_basis_factor R I hI, signDiagonal_basis, map_smul, map_smul,
    linearShears_parityProjection, parityProjection_basis, ite_eq_left rfl]

theorem pascalExteriorInverse_basis_parity {L : ℕ} (I : Finset ℕ)
    (hI : ∀ i ∈ I, i < L) :
    parityProjection R (doubledEnergy I % 2) (pascalExteriorInverse R (basis R I)) =
      pascalExteriorInverse R (basis R I) := by
  simpa only [pascalExteriorInverse_eq] using pascalExterior_basis_parity R I hI

end Lemmata.FockCircuits.Fock
