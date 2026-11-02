module

public import Lemmata.FockCircuits.CrossingBounds
public import Lemmata.FockCircuits.Families

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lemmata.FockCircuits.CrossingExistence

open FiniteIdentity CrossingCircuit Families CrossingAlgorithms CrossingPadding Filter Exponent
open scoped BigOperators Topology

noncomputable section

abbrev Actions (E : ℕ) := ↥(fullCutoff E)
abbrev Batch (n E : ℕ) := Fin (batchCount n (stateCount E))
abbrev Rows (W L : ℕ) := Fin W × ↥(fullCutoff L)
abbrev Inputs (n E : ℕ) := Variables n (Actions E) (Batch n E)
abbrev Outputs (n H E W : ℕ) :=
  ((Bool × Bool) × (Rows W (H + E) × Actions E)) ⊕ (Actions E × Batch n E)

abbrev action (H E : ℕ) : Actions E ↪ Index (H + E) :=
  cutoffEmbedding (by omega : E ≤ H + E)

abbrev middle (L : ℕ) : ↥(fullCutoff L) ↪ Index L := cutoffEmbedding le_rfl

/-- A shared coefficient circuit with its exact linear output polynomials and counted arithmetic cost. -/
structure ModeBank (R : Type*) [CommRing R] (C n H E W : ℕ)
    (B : Fin n ↪ Index (H + E)) where
  circuit : CircuitFamily R (Inputs n E) (Outputs n H E W)
  a_correct : ∀ r j, circuit.polynomial (.inl ((true, true), (r, j))) =
    coefficientRows (coefficientA R (dualFamily R B) (action H E) (middle (H + E)))
      (fun i => FreeAlgebra.ι R (true, Sum.inl i)) r j
  b_correct : ∀ r j, circuit.polynomial (.inl ((true, false), (r, j))) =
    coefficientRows (coefficientB R (bareFamily R B) (action H E) (middle (H + E)))
      (fun i => FreeAlgebra.ι R (false, Sum.inl i)) r j
  c_correct : ∀ r j, circuit.polynomial (.inl ((false, true), (r, j))) =
    coefficientRows (coefficientC R (dualFamily R B) (action H E) (middle (H + E)))
      (fun i => FreeAlgebra.ι R (true, Sum.inl i)) r j
  d_correct : ∀ r j, circuit.polynomial (.inl ((false, false), (r, j))) =
    coefficientRows (coefficientD R (bareFamily R B) (action H E) (middle (H + E)))
      (fun i => FreeAlgebra.ι R (false, Sum.inl i)) r j
  y_correct : ∀ j k, circuit.polynomial (.inr (j, k)) =
    FreeAlgebra.ι R (true, Sum.inr (j, k))
  size_le : circuit.size ≤ C * (H + E + 1) ^ 3 * stateCount (H + E) * stateCount E

namespace ModeBank

variable {R : Type*} [CommRing R] {C n H E W : ℕ} {B : Fin n ↪ Index (H + E)}

theorem identity_circuit (bank : ModeBank R C n H E W B)
    (hW : 0 < W) (hWH : W ≤ 2 * H) (hBW : ∀ i, doubledEnergy (B i).val = W)
    (p : AllOrders R (Rows (2 * H) (H + E)) (Actions E) (Batch n E)) :
    ∃ s : ℕ, HasCircuit (identityQuartic (R := R) n) s ∧
      s ≤ bank.circuit.size + p.abc.size + p.cba.size + p.cab.size + p.bac.size +
        4 * (stateCount E * batchCount n (stateCount E)) := by
  classical
  let q := p.restrictModes hWH
  let sa : Rows W (H + E) × Actions E → Outputs n H E W := fun z => .inl ((true, true), z)
  let sb : Rows W (H + E) × Actions E → Outputs n H E W := fun z => .inl ((true, false), z)
  let sc : Rows W (H + E) × Actions E → Outputs n H E W := fun z => .inl ((false, true), z)
  let sd : Rows W (H + E) × Actions E → Outputs n H E W := fun z => .inl ((false, false), z)
  let sy : Actions E × Batch n E → Outputs n H E W := Sum.inr
  let y : Matrix (Actions E) (Batch n E) (Inputs n E) :=
    Matrix.of fun j k => (true, Sum.inr (j, k))
  let u : Matrix (Actions E) (Batch n E) (Inputs n E) :=
    Matrix.of fun j k => (false, Sum.inr (j, k))
  let c : CircuitFamily R (Inputs n E) PUnit.{1} :=
    CrossingCircuit.compile (-(sigma W : R)) bank.circuit sa sb sc sd sy
    (fun z => u z.1 z.2) q.abc q.cba q.cab q.bac
  have hcut : 2 * E + W ≤ 2 * (H + E) := by omega
  have hsigned (i k : Fin n) (j l : Actions E) :
      (∑ r : Fin W,
        ((oppositeMode R (H + E) W r (bareFamily R B k) *
            markedMode R (H + E) W r (dualFamily R B i)) (action H E l) (action H E j) -
          (sigma W : R) *
            ((markedMode R (H + E) W r (dualFamily R B i) *
              oppositeMode R (H + E) W r (bareFamily R B k)) (action H E l) (action H E j)))) =
        if i = k then (if j = l then 1 else 0) else 0 := by
    exact family_signed_identity R B (action H E) hW (by omega) hBW
      (fun j => by
        have he := cutoffEmbedding_energy (by omega : E ≤ H + E) j
        change doubledEnergy (action H E j).val ≤ 2 * E at he
        omega) i k j l
  have hc := CrossingCircuit.compile_modes_correct (R := R)
    (dualFamily R B) (bareFamily R B) (action H E) (middle (H + E))
    (fun j => cutoffEmbedding_energy (by omega : E ≤ H + E) j)
    (cutoffEmbedding_covers (H + E)) hcut hsigned bank.circuit sa sb sc sd sy
    (fun i => (true, Sum.inl i)) (fun i => (false, Sum.inl i)) y u
    bank.a_correct bank.b_correct bank.c_correct bank.d_correct bank.y_correct
    q.abc q.cba q.cab q.bac
  have hc' : c.polynomial PUnit.unit = crossingPolynomial (R := R) n (Actions E) (Batch n E) := hc.1
  refine ⟨c.size, hasCircuit_identify (batchEmbedding n E) c hc', ?_⟩
  have hsize : c.size = bank.circuit.size + q.abc.size + q.cba.size + q.cab.size + q.bac.size +
      4 * (stateCount E * batchCount n (stateCount E)) := by
    simpa only [Fintype.card_coe, Fintype.card_fin, stateCount] using hc.2
  rw [hsize]
  simp only [q, AllOrders.restrictModes, AllOrders.restrict, Matrix.OrderedMatrixAlgorithm.size_pad,
    le_refl]

end ModeBank

theorem eventually_identity_circuits (R : Type*) [Field R] (C : ℕ)
    (hbanks : ∀ (n H E W : ℕ) (B : Fin n ↪ Index (H + E)),
      0 < W → W ≤ 2 * H → (∀ i, doubledEnergy (B i).val = W) →
        Nonempty (ModeBank R C n H E W B))
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      ∃ s : ℕ, HasCircuit (identityQuartic (R := R) n) s ∧
        (s : ℝ) ≤ (n : ℝ) ^ (gamma + eps) := by
  classical
  obtain ⟨padding, hpadding, halg, hoverhead⟩ :=
    eventually_exterior_algorithms R (eps / 2) (by linarith)
  let H := ceilLogEnergy countingConstant (1 + padding)
  let E := floorLogEnergy countingConstant optimalInput
  let L : ℝ := gamma + eps / 2
  let bound (n : ℕ) : ℝ :=
    ((C + 8 : ℕ) : ℝ) * ((H n + E n + 1 : ℕ) : ℝ) ^ 3 * (n : ℝ) ^ L
  have hcost : ∀ᶠ n : ℕ in atTop,
      ∃ s : ℕ, HasCircuit (identityQuartic (R := R) n) s ∧ (s : ℝ) ≤ bound n := by
    filter_upwards [halg] with n hn
    rcases hn with ⟨hH, hcapacity, p, hp, harea, _, hfinal⟩
    obtain ⟨W, B, hW, hWH, hBinj, hBW, _⟩ :=
      exists_dual_family R (H n) (H n + E n) n hH (by omega) hcapacity
    let B' : Fin n ↪ Index (H n + E n) := ⟨B, hBinj⟩
    obtain ⟨bank⟩ := hbanks n (H n) (E n) W B' hW hWH hBW
    obtain ⟨s, hs, hsize⟩ := bank.identity_circuit hW hWH hBW p
    let t : ℝ := (n : ℝ) ^ L
    let o : ℝ := ((H n + E n + 1 : ℕ) : ℝ) ^ 3
    have ht : 0 ≤ t := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have ho : 1 ≤ o := one_le_pow₀ (by exact_mod_cast (show 1 ≤ H n + E n + 1 by omega))
    have hareaNat : stateCount (H n + E n) * stateCount (E n) ≤
        (2 * H n * stateCount (H n + E n)) * stateCount (E n) := by
      have hmul := Nat.mul_le_mul_left (stateCount (H n + E n) * stateCount (E n))
        (by omega : 1 ≤ 2 * H n)
      simpa only [mul_one, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
    have harea' : ((stateCount (H n + E n) * stateCount (E n) : ℕ) : ℝ) ≤ t :=
      (Nat.cast_le.mpr hareaNat).trans harea
    have hbank : (bank.circuit.size : ℝ) ≤ (C : ℝ) * o * t := by
      have h0 : (bank.circuit.size : ℝ) ≤
          (C : ℝ) * o * stateCount (H n + E n) * stateCount (E n) := by
        dsimp only [o]
        exact_mod_cast bank.size_le
      have h1 := mul_le_mul_of_nonneg_left harea'
        (mul_nonneg (Nat.cast_nonneg C) (zero_le_one.trans ho))
      exact h0.trans (by simpa only [Nat.cast_mul, mul_assoc] using h1)
    have hsizeR : (s : ℝ) ≤ (bank.circuit.size : ℝ) + p.abc.size + p.cba.size +
        p.cab.size + p.bac.size + 4 * ((stateCount (E n) * batchCount n (stateCount (E n)) : ℕ) : ℝ) := by
      exact_mod_cast hsize
    rcases hp with ⟨hABC, _, hBAC, _, hCAB, hCBA⟩
    have hsum : (s : ℝ) ≤ ((C : ℝ) * o + 8) * t := by
      change (p.abc.size : ℝ) ≤ t at hABC
      change (p.bac.size : ℝ) ≤ t at hBAC
      change (p.cab.size : ℝ) ≤ t at hCAB
      change (p.cba.size : ℝ) ≤ t at hCBA
      change ((stateCount (E n) * batchCount n (stateCount (E n)) : ℕ) : ℝ) ≤ t at hfinal
      linarith
    have hfactor : (C : ℝ) * o + 8 ≤ ((C : ℝ) + 8) * o := by linarith
    refine ⟨s, hs, hsum.trans ?_⟩
    simpa only [bound, Nat.cast_add, Nat.cast_ofNat, o, t, mul_assoc] using
      mul_le_mul_of_nonneg_right hfactor ht
  let size (n : ℕ) : ℕ := if h : ∃ s : ℕ,
      HasCircuit (identityQuartic (R := R) n) s ∧ (s : ℝ) ≤ bound n then Classical.choose h else 0
  have hchosen : ∀ᶠ n : ℕ in atTop,
      HasCircuit (identityQuartic (R := R) n) (size n) ∧ (size n : ℝ) ≤ bound n :=
    hcost.mono fun n hn => by
      dsimp only [size]
      rw [dif_pos hn]
      exact Classical.choose_spec hn
  have hsizebound := CrossingBounds.eventually_cost_bound C H E size L (eps / 2)
    (by linarith) hoverhead (hchosen.mono fun _ h => h.2)
  filter_upwards [hchosen, hsizebound] with n hn hbound
  refine ⟨size n, hn.1, ?_⟩
  convert hbound using 1 <;> dsimp [L] <;> congr 1 <;> ring

theorem identity_circuit_bound (R : Type*) [Field R] (C : ℕ)
    (hbanks : ∀ (n H E W : ℕ) (B : Fin n ↪ Index (H + E)),
      0 < W → W ≤ 2 * H → (∀ i, doubledEnergy (B i).val = W) →
        Nonempty (ModeBank R C n H E W B))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (identityQuartic (R := R) n) s ∧
        (s : ℝ) ≤ K * (n : ℝ) ^ (gamma + eps) := by
  apply uniform_bound_of_eventually (fun n => identityQuartic (R := R) n) (gamma + eps)
    (by unfold gamma; positivity)
  exact eventually_identity_circuits R C hbanks eps heps

end

end Lemmata.FockCircuits.CrossingExistence
