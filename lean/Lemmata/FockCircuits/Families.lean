module

public import Lemmata.FockCircuits.Duality
public import Lemmata.FockCircuits.StateIdentity
public import Lemmata.FockCircuits.CrossingCircuit

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lemmata.FockCircuits.Families

open FiniteIdentity CrossingCircuit

variable (R : Type*) [CommRing R]

noncomputable def dualFamily {I : Type*} {L : ℕ} (B : I → Index L) (i : I) : State R L :=
  dualState R L (B i).val

noncomputable def bareFamily {I : Type*} {L : ℕ} (B : I → Index L) (i : I) : State R L :=
  (dualSign (B i).val : R) • Pi.single (B i) 1

theorem oppositeMode_bareFamily {I : Type*} {L W : ℕ}
    (B : I → Index L) (i : I) (r : Fin W) :
    oppositeMode R L W r (bareFamily R B i) =
      (dualSign (B i).val : R) • oppositeMode R L W r (Pi.single (B i) 1) := by
  change diagonalLinear R L (-shift W r)
      ((dualSign (B i).val : R) • Pi.single (B i) 1) =
    (dualSign (B i).val : R) • diagonalLinear R L (-shift W r) (Pi.single (B i) 1)
  simpa only [RingHom.id_apply] using (diagonalLinear R L (-shift W r)).map_smul
    (dualSign (B i).val : R) (Pi.single (B i) 1)

theorem family_signed_identity {I J : Type*} [DecidableEq I] [DecidableEq J] {L W : ℕ}
    (B : I ↪ Index L) (action : J ↪ Index L) (hW : 0 < W) (hWL : W ≤ 2 * L)
    (hBW : ∀ i, doubledEnergy (B i).val = W)
    (hcut : ∀ j, doubledEnergy (action j).val + W ≤ 2 * L)
    (i k : I) (j l : J) :
    (∑ r : Fin W,
      ((oppositeMode R L W r (bareFamily R B k) *
          markedMode R L W r (dualFamily R B i)) (action l) (action j) -
        (sigma W : R) *
          ((markedMode R L W r (dualFamily R B i) *
            oppositeMode R L W r (bareFamily R B k)) (action l) (action j)))) =
      if i = k then (if j = l then 1 else 0) else 0 := by
  classical
  have hsupport (A : Index L) (hA : dualState R L (B i).val A ≠ 0) :
      doubledEnergy A.val ≤ W ∧ doubledEnergy A.val % 2 = W % 2 := by
    simpa only [hBW i] using dualState_supported R (B i) A hA
  have h := state_signed_identity R L W (dualState R L (B i).val) (B k)
    (action l) (action j) hW (hBW k) hsupport (hcut j)
  have hnormal := dual_matrix_normalized R (B i) (B k)
    (by rw [hBW]; exact hWL) (by rw [hBW, hBW])
  calc
    _ = (dualSign (B k).val : R) *
        (∑ r : Fin W,
          ((diagonal R L (-shift W r) (Pi.single (B k) 1) *
              diagonal R L (shift W r) (mark R L W r (dualState R L (B i).val)))
                (action l) (action j) -
            (sigma W : R) *
              (diagonal R L (shift W r) (mark R L W r (dualState R L (B i).val)) *
                diagonal R L (-shift W r) (Pi.single (B k) 1)) (action l) (action j))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [oppositeMode_bareFamily]
      simp only [dualFamily, markedMode, oppositeMode, mul_smul_comm, smul_mul_assoc,
        Matrix.smul_apply, smul_eq_mul]
      ring
    _ = (if action l = action j then (1 : R) else 0) *
        ((dualSign (B k).val : R) *
          matrix R L (dualState R L (B i).val) ⟨∅, by simp⟩ (B k)) := by rw [h]; ring
    _ = _ := by
      rw [hnormal]
      simp only [B.injective.eq_iff, action.injective.eq_iff]
      by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [hik, hjl, eq_comm]

theorem family_coefficient_identity {I J ρ : Type*} [Fintype I] [Fintype J] [Fintype ρ]
    [DecidableEq I] [DecidableEq J] {L E W : ℕ}
    (B : I ↪ Index L) (action : J ↪ Index L) (middle : ρ ↪ Index L)
    (hW : 0 < W) (hBW : ∀ i, doubledEnergy (B i).val = W)
    (haction : ∀ j, doubledEnergy (action j).val ≤ 2 * E)
    (hcover : ∀ s : Index L, doubledEnergy s.val ≤ 2 * L → s ∈ Set.range middle)
    (hcut : 2 * E + W ≤ 2 * L) (i k : I) (j l : J) :
    (∑ s : Fin W × ρ,
      coefficientA R (dualFamily R B) action middle s i j *
        coefficientB R (bareFamily R B) action middle s k l) -
      (sigma W : R) * (∑ s : Fin W × ρ,
        coefficientC R (dualFamily R B) action middle s i l *
          coefficientD R (bareFamily R B) action middle s k j) =
      if i = k then (if j = l then 1 else 0) else 0 := by
  apply coefficient_identity_of_signed R (dualFamily R B) (bareFamily R B)
    action middle haction hcover hcut
  intro i k j l
  exact family_signed_identity R B action hW (by omega) hBW
    (fun j => by have hj := haction j; omega) i k j l

end Lemmata.FockCircuits.Families
