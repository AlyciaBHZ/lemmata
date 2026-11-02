module

public import Lemmata.FockCircuits.CoordinateModes

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lemmata.FockCircuits.ModeBanks

open FiniteIdentity Families CrossingCircuit CrossingExistence CoordinateModes
open Lemmata.FockCircuits.Matrix

noncomputable section

variable (R : Type*) [CommRing R]

theorem exists_modeBank (n H E W : ℕ) (B : Fin n ↪ Index (H + E))
    (hWH : W ≤ 2 * H) (hBW : ∀ i, doubledEnergy (B i).val = W) :
    Nonempty (ModeBank R 256 n H E W B) := by
  classical
  let x : Fin n → Inputs n E := fun i => (true, Sum.inl i)
  let v : Fin n → Inputs n E := fun i => (false, Sum.inl i)
  choose a ha hpa using fun k : Fin W => exists_coordinate_mode R n H E W true false B hWH hBW k x
  choose b hb hpb using fun k : Fin W => exists_coordinate_mode R n H E W false true B hWH hBW k v
  choose c hc hpc using fun k : Fin W => exists_coordinate_mode R n H E W true true B hWH hBW k x
  choose d hd hpd using fun k : Fin W => exists_coordinate_mode R n H E W false false B hWH hBW k v
  let A := CircuitBuilders.parallelFin W a
  let BB := CircuitBuilders.parallelFin W b
  let CC := CircuitBuilders.parallelFin W c
  let DD := CircuitBuilders.parallelFin W d
  let role : CircuitFamily R (Inputs n E)
      ((Bool × Bool) × (Rows W (H + E) × Actions E)) :=
    ((A.combine BB).combine (CC.combine DD)).reindexOutputs (fun z =>
      if z.1.1 then
        Sum.inl (if z.1.2 then Sum.inl (z.2.1.1, (z.2.1.2, z.2.2)) else
          Sum.inr (z.2.1.1, (z.2.1.2, z.2.2)))
      else Sum.inr (if z.1.2 then Sum.inl (z.2.1.1, (z.2.1.2, z.2.2)) else
          Sum.inr (z.2.1.1, (z.2.1.2, z.2.2))))
  let Y : CircuitFamily R (Inputs n E) (Actions E × Batch n E) :=
    CircuitBuilders.family fun z => CircuitBuilders.input (true, Sum.inr z)
  let bank := role.combine Y
  refine ⟨⟨bank, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro r j
    simpa only [bank, role, A, CircuitFamily.polynomial, CircuitFamily.eval_combine_inl,
      CircuitFamily.eval_reindexOutputs, CircuitBuilders.eval_parallelFin,
      if_true, if_false, coefficientRows, coefficientA, markedMode,
      CoordinateModes.states, selectedShift, Bool.false_eq_true, ite_true, ite_false, x]
      using hpa r.1 (r.2, j)
  · intro r j
    simpa only [bank, role, BB, CircuitFamily.polynomial, CircuitFamily.eval_combine_inl,
      CircuitFamily.eval_combine_inr, CircuitFamily.eval_reindexOutputs,
      CircuitBuilders.eval_parallelFin, if_true, if_false, coefficientRows, coefficientB,
      oppositeMode, CoordinateModes.states, selectedShift, Bool.false_eq_true, ite_true,
      ite_false, v] using hpb r.1 (r.2, j)
  · intro r j
    simpa only [bank, role, CC, CircuitFamily.polynomial, CircuitFamily.eval_combine_inl,
      CircuitFamily.eval_combine_inr, CircuitFamily.eval_reindexOutputs,
      CircuitBuilders.eval_parallelFin, if_true, if_false, coefficientRows, coefficientC,
      markedMode, CoordinateModes.states, selectedShift, Bool.false_eq_true, ite_true,
      ite_false, x] using hpc r.1 (r.2, j)
  · intro r j
    simpa only [bank, role, DD, CircuitFamily.polynomial, CircuitFamily.eval_combine_inl,
      CircuitFamily.eval_combine_inr, CircuitFamily.eval_reindexOutputs,
      CircuitBuilders.eval_parallelFin, if_true, if_false, coefficientRows, coefficientD,
      oppositeMode, CoordinateModes.states, selectedShift, Bool.false_eq_true, ite_true,
      ite_false, v] using hpd r.1 (r.2, j)
  · intro j k
    simp [bank, Y, CircuitFamily.polynomial]
  · have hs (p : Fin W → CircuitFamily R (Inputs n E) (KernelRectangle.Index (H + E) E))
        (hp : ∀ k, (p k).size ≤ 32 * (H + E + 1)^2 * stateCount (H + E) * stateCount E) :
        (CircuitBuilders.parallelFin W p).size ≤
          W * (32 * (H + E + 1)^2 * stateCount (H + E) * stateCount E) := by
      rw [CircuitBuilders.size_parallelFin]
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin W))) (fun k _ => hp k)
    have hsize : bank.size ≤
        4 * W * (32 * (H + E + 1)^2 * stateCount (H + E) * stateCount E) := by
      dsimp only [bank, role]
      simp only [CircuitFamily.size_combine, CircuitFamily.size_reindexOutputs]
      have hy : Y.size = 0 := by simp [Y]
      rw [hy, add_zero]
      have hA := hs a ha
      have hB := hs b hb
      have hC := hs c hc
      have hD := hs d hd
      change A.size + BB.size + (CC.size + DD.size) ≤ _
      dsimp only [A, BB, CC, DD]
      have htotal := Nat.add_le_add (Nat.add_le_add hA hB) (Nat.add_le_add hC hD)
      convert htotal using 1 <;> ring
    have hW : W ≤ 2 * (H + E + 1) := by omega
    have hmult := Nat.mul_le_mul_right
      (128 * (H + E + 1)^2 * stateCount (H + E) * stateCount E) hW
    calc
      bank.size ≤ 4 * W * (32 * (H + E + 1)^2 * stateCount (H + E) * stateCount E) := hsize
      _ ≤ 256 * (H + E + 1)^3 * stateCount (H + E) * stateCount E := by
        convert hmult using 1 <;> ring

end

end Lemmata.FockCircuits.ModeBanks
