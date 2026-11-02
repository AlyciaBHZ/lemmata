module

public import Lemmata.FockCircuits.CoordinateModes
public import Lemmata.FockCircuits.ModeTranspose
public import Lemmata.FockCircuits.QuinticExistence
public import Lemmata.FockCircuits.Positional

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lemmata.FockCircuits.ModeAdjoints

open FiniteIdentity Families CrossingCircuit CrossingExistence KernelRectangle
open KernelAlgorithm KernelStages KernelInput SourceBanks KernelModes CoordinateModes
open scoped BigOperators

noncomputable section

variable (R : Type*) [CommRing R]

theorem exists_coordinate_transpose (n H E W : ℕ) (right : Bool) (scale : R)
    (B : Fin n ↪ FiniteIdentity.Index (H + E))
    (hWH : W ≤ 2 * H) (hBW : ∀ i, doubledEnergy (B i).val = W) (k : Fin W) :
    ∃ t : ScalarTransposeAlgorithm R (Fin n) (KernelRectangle.Index (H + E) E)
      (fun f i => scale * diagonal R (H + E) (shift W k) (states R true B k i)
        (if right then action H E f.2 else middle (H + E) f.1)
        (if right then middle (H + E) f.1 else action H E f.2)),
      t.size ≤ 32 * (H + E + 1)^2 * stateCount (H + E) * stateCount E := by
  classical
  let L := H + E
  have hB (i : Fin n) : doubledEnergy (B i).val ≤ 2 * L := by rw [hBW]; dsimp [L]; omega
  cases right with
  | false =>
    let source := leftSource (V := E) B hB
    obtain ⟨t, ht⟩ := exists_mode_transpose R L E L false (shift W k) scale
      (sourceSteps R true false L W k) (sourceSteps_sparse R true false L W k)
      (sourceSteps_preserves R L E L W true false k)
      (sourceSteps_length R true false L W k) source (Function.Embedding.refl _)
      (fun f => middle L f.1) (fun f => action H E f.2)
      (fun _ => rfl) (fun _ => rfl) (states R true B k) (by
        intro i
        rw [leftSource_basis]
        exact sourceSteps_kernel R true false B k i (hB i))
    exact ⟨t, ht⟩
  | true =>
    let source := rightSource (U := E) B hB
    let output : KernelRectangle.Index L E ↪ KernelRectangle.Index E L :=
      (Equiv.prodComm _ _).toEmbedding
    obtain ⟨t, ht⟩ := exists_mode_transpose R E L L true (shift W k) scale
      (sourceSteps R true true L W k) (sourceSteps_sparse R true true L W k)
      (sourceSteps_preserves R E L L W true true k)
      (sourceSteps_length R true true L W k) source output
      (fun f => action H E f.2) (fun f => middle L f.1)
      (fun _ => rfl) (fun _ => rfl) (states R true B k) (by
        intro i
        rw [rightSource_basis]
        exact sourceSteps_kernel R true true B k i (hB i))
    refine ⟨t, ?_⟩
    simpa only [L, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using ht

def reindexOutput {I O P : Type*} [Fintype O] [Fintype P]
    {a : O → I → R} (t : ScalarTransposeAlgorithm R I O a) (e : P ≃ O) :
    ScalarTransposeAlgorithm R I P (fun p i => a (e p) i) where
  circuit := t.circuit.mapInputs e.symm
  correct := by
    intro i
    rw [CircuitFamily.polynomial_mapInputs, t.correct]
    simp only [map_sum, map_smul, FreeAlgebra.lift_ι_apply]
    simpa only [e.symm_apply_apply] using
      (e.sum_comp (fun o => a o i • FreeAlgebra.ι R (e.symm o))).symm

@[simp] theorem size_reindexOutput {I O P : Type*} [Fintype O] [Fintype P]
    {a : O → I → R} (t : ScalarTransposeAlgorithm R I O a) (e : P ≃ O) :
    (reindexOutput R t e).size = t.size :=
  CircuitFamily.size_mapInputs t.circuit e.symm

theorem source_card_le (n H E W : ℕ) (B : Fin n ↪ FiniteIdentity.Index (H + E))
    (hWH : W ≤ 2 * H) (hBW : ∀ i, doubledEnergy (B i).val = W) :
    n ≤ stateCount (H + E) * stateCount E := by
  let e : Fin n ↪ ↥(fullCutoff (H + E)) :=
    ⟨fun i => ⟨(B i).val, mem_fullCutoff.mpr (by rw [hBW]; omega)⟩,
      fun i j h => B.injective (Subtype.ext
        (congrArg (fun s : ↥(fullCutoff (H + E)) => s.val) h))⟩
  have hcard : n ≤ stateCount (H + E) := by
    simpa only [Fintype.card_fin, Fintype.card_coe, stateCount] using
      Fintype.card_le_of_injective e e.injective
  exact hcard.trans (Nat.le_mul_of_pos_right _ (stateCount_pos E))

theorem exists_stacked_transpose (n H E W : ℕ) (right : Bool) (scale : R)
    (B : Fin n ↪ FiniteIdentity.Index (H + E))
    (hWH : W ≤ 2 * H) (hBW : ∀ i, doubledEnergy (B i).val = W) :
    ∃ t : ScalarTransposeAlgorithm R (Fin n) (Rows W (H + E) × Actions E)
      (fun f i => scale * diagonal R (H + E) (shift W f.1.1)
        (states R true B f.1.1 i)
        (if right then action H E f.2 else middle (H + E) f.1.2)
        (if right then middle (H + E) f.1.2 else action H E f.2)),
      t.size ≤ 128 * (H + E + 1)^3 * stateCount (H + E) * stateCount E := by
  classical
  choose t ht using fun k : Fin W => exists_coordinate_transpose R n H E W right scale B hWH hBW k
  let a := fun (k : Fin W) (f : KernelRectangle.Index (H + E) E) (i : Fin n) =>
    scale * diagonal R (H + E) (shift W k) (states R true B k i)
      (if right then action H E f.2 else middle (H + E) f.1)
      (if right then middle (H + E) f.1 else action H E f.2)
  let stacked := KernelTranspose.stacked W a t
  let result := reindexOutput R stacked (Equiv.prodAssoc _ _ _)
  refine ⟨result, ?_⟩
  have hsum : (∑ k : Fin W, (t k).size) ≤
      W * (32 * (H + E + 1)^2 * stateCount (H + E) * stateCount E) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin W))) (fun k _ => ht k)
  have hn := source_card_le n H E W B hWH hBW
  have hW : W ≤ 2 * (H + E + 1) := by omega
  have hpow : 1 ≤ (H + E + 1)^2 := one_le_pow₀ (by omega)
  have hextra : 2 * W * n ≤ 2 * W * (stateCount (H + E) * stateCount E) :=
    Nat.mul_le_mul_left _ hn
  have htotal : W * (32 * (H + E + 1)^2 * stateCount (H + E) * stateCount E) +
      2 * W * (stateCount (H + E) * stateCount E) ≤
        128 * (H + E + 1)^3 * stateCount (H + E) * stateCount E := by
    have hcoefficient : 32 * (H + E + 1)^2 + 2 ≤ 64 * (H + E + 1)^2 := by omega
    calc
      _ = W * ((32 * (H + E + 1)^2 + 2) * (stateCount (H + E) * stateCount E)) := by ring
      _ ≤ W * ((64 * (H + E + 1)^2) * (stateCount (H + E) * stateCount E)) :=
        Nat.mul_le_mul_left W (Nat.mul_le_mul_right _ hcoefficient)
      _ ≤ (2 * (H + E + 1)) * ((64 * (H + E + 1)^2) *
          (stateCount (H + E) * stateCount E)) := Nat.mul_le_mul_right _ hW
      _ = _ := by ring
  have hsize : result.size = (∑ k : Fin W, (t k).size) + 2 * W * n := by
    simp only [result, size_reindexOutput, stacked, KernelTranspose.size_stacked, Fintype.card_fin]
  rw [hsize]
  exact (Nat.add_le_add hsum hextra).trans htotal

theorem exists_quinticBank {C n H E W : ℕ} {B : Fin n ↪ FiniteIdentity.Index (H + E)}
    (bank : ModeBank R C n H E W B)
    (hWH : W ≤ 2 * H) (hBW : ∀ i, doubledEnergy (B i).val = W) :
    Nonempty (QuinticExistence.QuinticBank R (C + 256) n H E W B) := by
  classical
  obtain ⟨ta, hta⟩ := exists_stacked_transpose R n H E W false 1 B hWH hBW
  obtain ⟨tc, htc⟩ := exists_stacked_transpose R n H E W true (-(sigma W : R)) B hWH hBW
  let ta' : ScalarTransposeAlgorithm R (Fin n) (Rows W (H + E) × Actions E)
      (fun q i => coefficientA R (dualFamily R B) (action H E) (middle (H + E)) q.1 i q.2) :=
    ⟨ta.circuit, by
      intro i
      simpa only [one_mul, Bool.false_eq_true, ite_false, states, ite_true,
        coefficientA, markedMode] using ta.correct i⟩
  let tc' : ScalarTransposeAlgorithm R (Fin n) (Rows W (H + E) × Actions E)
      (fun q i => -(sigma W : R) *
        coefficientC R (dualFamily R B) (action H E) (middle (H + E)) q.1 i q.2) :=
    ⟨tc.circuit, by
      intro i
      simpa only [states, ite_true, coefficientC, markedMode] using tc.correct i⟩
  let z := (H + E + 1)^3 * stateCount (H + E) * stateCount E
  have hbank : bank.circuit.size ≤ C * z := by simpa only [z, Nat.mul_assoc] using bank.size_le
  have hbank' : bank.circuit.size ≤ (C + 256) * (H + E + 1)^3 * stateCount (H + E) * stateCount E := by
    have hle := Nat.mul_le_mul_right z (by omega : C ≤ C + 256)
    simpa only [z, Nat.mul_assoc] using hbank.trans hle
  let bank' : ModeBank R (C + 256) n H E W B :=
    ⟨bank.circuit, bank.a_correct, bank.b_correct, bank.c_correct, bank.d_correct, bank.y_correct, hbank'⟩
  refine ⟨⟨bank', ta', tc', ?_⟩⟩
  have hta' : ta'.size ≤ 128 * z := by
    dsimp only [ta', ScalarTransposeAlgorithm.size]
    simpa only [ScalarTransposeAlgorithm.size, z, Nat.mul_assoc] using hta
  have htc' : tc'.size ≤ 128 * z := by
    dsimp only [tc', ScalarTransposeAlgorithm.size]
    simpa only [ScalarTransposeAlgorithm.size, z, Nat.mul_assoc] using htc
  change bank.circuit.size + ta'.size + tc'.size ≤ _
  calc
    _ ≤ C * z + 128 * z + 128 * z := Nat.add_le_add (Nat.add_le_add hbank hta') htc'
    _ = _ := by dsimp [z]; ring

end

end Lemmata.FockCircuits.ModeAdjoints
