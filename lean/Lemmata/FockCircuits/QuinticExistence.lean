module

public import Lemmata.FockCircuits.CrossingExistence
public import Lemmata.FockCircuits.ScalarAdjoints

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lemmata.FockCircuits.QuinticExistence

open FiniteIdentity CrossingCircuit Families CrossingAlgorithms CrossingPadding CrossingExistence
open scoped BigOperators Topology

noncomputable section

def identityQuintic (R : Type*) [CommSemiring R] (n : ℕ) : FreeAlgebra R (Fin n ⊕ Fin n) :=
  ∑ i, ∑ j, FreeAlgebra.ι R (Sum.inl i) * FreeAlgebra.ι R (Sum.inr j) *
    FreeAlgebra.ι R (Sum.inl i) * FreeAlgebra.ι R (Sum.inr j) * FreeAlgebra.ι R (Sum.inl i)

def crossingQuintic (R : Type*) [CommSemiring R] (n : ℕ) (J K : Type*) [Fintype J] [Fintype K] :
    FreeAlgebra R (Variables n J K) :=
  ∑ i, ∑ j, ∑ k, FreeAlgebra.ι R (true, Sum.inl i) * FreeAlgebra.ι R (true, Sum.inr (j, k)) *
    FreeAlgebra.ι R (false, Sum.inl i) * FreeAlgebra.ι R (false, Sum.inr (j, k)) *
      FreeAlgebra.ι R (true, Sum.inl i)

structure QuinticBank (R : Type*) [CommRing R] (C n H E W : ℕ)
    (B : Fin n ↪ Index (H + E)) where
  bank : ModeBank R C n H E W B
  ta : ScalarTransposeAlgorithm R (Fin n) (Rows W (H + E) × Actions E)
    (fun q i => coefficientA R (dualFamily R B) (action H E) (middle (H + E)) q.1 i q.2)
  tc : ScalarTransposeAlgorithm R (Fin n) (Rows W (H + E) × Actions E)
    (fun q i => -(sigma W : R) *
      coefficientC R (dualFamily R B) (action H E) (middle (H + E)) q.1 i q.2)
  size_le : bank.circuit.size + ta.size + tc.size ≤
    C * (H + E + 1) ^ 3 * stateCount (H + E) * stateCount E

variable {R : Type*} [CommRing R]

theorem polynomial_identify {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin n ↪ J × K) (c : CircuitFamily R (Variables n J K) PUnit)
    (hc : c.polynomial PUnit.unit = crossingQuintic R n J K) :
    ((identifyBank (R := R) e).substitute c).polynomial PUnit.unit = identityQuintic R n := by
  classical
  rw [CircuitFamily.polynomial_substitute, hc]
  simp only [crossingQuintic, identityQuintic, map_sum, map_mul, FreeAlgebra.lift_ι_apply,
    polynomial_identifyBank_left, polynomial_identifyBank_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Fintype.sum_prod_type (fun p : J × K =>
    FreeAlgebra.ι R (Sum.inl i) *
      Function.extend e (fun j => FreeAlgebra.ι R (Sum.inr j)) (fun _ => 0) p *
      FreeAlgebra.ι R (Sum.inl i) *
      Function.extend e (fun j => FreeAlgebra.ι R (Sum.inr j)) (fun _ => 0) p *
      FreeAlgebra.ι R (Sum.inl i))]
  symm
  apply Fintype.sum_of_injective e e.injective
  · intro p hp
    rw [Function.extend_apply' _ _ _ hp]
    simp only [mul_zero, zero_mul]
  · intro j
    simp only [e.injective.extend_apply]

theorem hasCircuit_identify {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin n ↪ J × K) (c : CircuitFamily R (Variables n J K) PUnit)
    (hc : c.polynomial PUnit.unit = crossingQuintic R n J K) :
    HasCircuit (identityQuintic R n) c.size := by
  let d := (identifyBank (R := R) e).substitute c
  refine ⟨d.nodeCount, d.circuit, d.output PUnit.unit, polynomial_identify e c hc, ?_⟩
  change d.size ≤ c.size
  simp only [d, CircuitFamily.size_substitute, size_identifyBank, zero_add, le_refl]

namespace QuinticBank

variable {C n H E W : ℕ} {B : Fin n ↪ Index (H + E)}

theorem identity_circuit (bank : QuinticBank R C n H E W B)
    (hW : 0 < W) (hWH : W ≤ 2 * H) (hBW : ∀ i, doubledEnergy (B i).val = W)
    (p : AllOrders R (Rows (2 * H) (H + E)) (Actions E) (Batch n E)) :
    ∃ s : ℕ, HasCircuit (identityQuintic R n) s ∧
      s ≤ bank.bank.circuit.size + p.abc.size + p.bca.size + p.cba.size + p.acb.size +
        bank.ta.size + bank.tc.size + 5 * n := by
  classical
  let q := p.restrictModes hWH
  let uBank : CircuitFamily R (Inputs n E) (Actions E × Batch n E) :=
    Matrix.CircuitBuilders.family (fun z => Matrix.CircuitBuilders.input (false, Sum.inr z))
  let b := bank.bank.circuit.combine uBank
  let sb : Rows W (H + E) × Actions E → Outputs n H E W ⊕ (Actions E × Batch n E) :=
    fun z => .inl (.inl ((true, false), z))
  let sd : Rows W (H + E) × Actions E → Outputs n H E W ⊕ (Actions E × Batch n E) :=
    fun z => .inl (.inl ((false, false), z))
  let sy : Actions E × Batch n E → Outputs n H E W ⊕ (Actions E × Batch n E) :=
    fun z => .inl (.inr z)
  let su : Actions E × Batch n E → Outputs n H E W ⊕ (Actions E × Batch n E) := Sum.inr
  let a := coefficientA R (dualFamily R B) (action H E) (middle (H + E)) (W := W)
  let bCoeff := coefficientB R (bareFamily R B) (action H E) (middle (H + E)) (W := W)
  let c := fun r i j => -(sigma W : R) *
    coefficientC R (dualFamily R B) (action H E) (middle (H + E)) (W := W) r i j
  let d := coefficientD R (bareFamily R B) (action H E) (middle (H + E)) (W := W)
  let x : Fin n → Inputs n E := fun i => (true, Sum.inl i)
  let v : Fin n → Inputs n E := fun i => (false, Sum.inl i)
  let y : Matrix (Actions E) (Batch n E) (Inputs n E) :=
    Matrix.of fun j k => (true, Sum.inr (j, k))
  let u : Matrix (Actions E) (Batch n E) (Inputs n E) :=
    Matrix.of fun j k => (false, Sum.inr (j, k))
  let result : CircuitFamily R (Inputs n E) PUnit.{1} :=
    QuinticCompiler.compile (a := a) (c := c) b sb sd sy su q.abc q.bca q.cba q.acb bank.ta bank.tc x x
  have hcoeff (i j k l) :
      (∑ r, a r i j * bCoeff r k l) + (∑ r, c r i l * d r k j) =
        if i = k then (if j = l then 1 else 0) else 0 := by
    have h := family_coefficient_identity R B (action H E) (middle (H + E)) hW hBW
      (E := E) (fun j => cutoffEmbedding_energy (by omega : E ≤ H + E) j)
      (cutoffEmbedding_covers (H + E)) (by omega) i k j l
    simpa only [a, bCoeff, c, d, mul_assoc, ← Finset.mul_sum, neg_mul,
      Finset.sum_neg_distrib, sub_eq_add_neg] using h
  have hb (r j) : b.polynomial (sb (r, j)) = coefficientRows bCoeff (fun i => FreeAlgebra.ι R (v i)) r j := by
    simpa only [b, sb, CircuitFamily.polynomial, CircuitFamily.eval_combine_inl] using bank.bank.b_correct r j
  have hd (r j) : b.polynomial (sd (r, j)) = coefficientRows d (fun i => FreeAlgebra.ι R (v i)) r j := by
    simpa only [b, sd, CircuitFamily.polynomial, CircuitFamily.eval_combine_inl] using bank.bank.d_correct r j
  have hy (j k) : b.polynomial (sy (j, k)) = FreeAlgebra.ι R (y j k) := by
    simpa only [b, sy, y, Matrix.of_apply, CircuitFamily.polynomial,
      CircuitFamily.eval_combine_inl] using bank.bank.y_correct j k
  have hu (j k) : b.polynomial (su (j, k)) = FreeAlgebra.ι R (u j k) := by
    simp [b, su, uBank, CircuitFamily.polynomial, u]
  have hresult : result.polynomial PUnit.unit = crossingQuintic R n (Actions E) (Batch n E) :=
    QuinticCompiler.polynomial_compile_crossing b sb sd sy su q.abc q.bca q.cba q.acb
      a bCoeff c d bank.ta bank.tc hcoeff x v x y u hb hd hy hu
  refine ⟨result.size, hasCircuit_identify (batchEmbedding n E) result hresult, ?_⟩
  have hsize := QuinticCompiler.size_compile (a := a) (c := c)
    b sb sd sy su q.abc q.bca q.cba q.acb bank.ta bank.tc x x
  have hbank : b.size = bank.bank.circuit.size := by simp [b, uBank]
  change result.size ≤ _
  rw [show result.size = b.size + q.abc.size + q.bca.size + q.cba.size + q.acb.size +
    bank.ta.size + bank.tc.size + 5 * n by simpa only [Fintype.card_fin] using hsize, hbank]
  simp only [q, AllOrders.restrictModes, AllOrders.restrict, Matrix.OrderedMatrixAlgorithm.size_pad,
    le_refl]

end QuinticBank

theorem eventually_identity_circuits (R : Type*) [Field R] (C : ℕ)
    (hbanks : ∀ (n H E W : ℕ) (B : Fin n ↪ Index (H + E)),
      0 < W → W ≤ 2 * H → (∀ i, doubledEnergy (B i).val = W) →
        Nonempty (QuinticBank R C n H E W B))
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ s : ℕ, HasCircuit (identityQuintic R n) s ∧
        (s : ℝ) ≤ (n : ℝ) ^ (Exponent.gamma + eps) := by
  classical
  obtain ⟨padding, hpadding, halg, hoverhead⟩ :=
    eventually_exterior_algorithms R (eps / 2) (by linarith)
  let H := ceilLogEnergy countingConstant (1 + padding)
  let E := floorLogEnergy countingConstant Exponent.optimalInput
  let L : ℝ := Exponent.gamma + eps / 2
  let bound (n : ℕ) : ℝ :=
    ((C + 9 : ℕ) : ℝ) * ((H n + E n + 1 : ℕ) : ℝ) ^ 3 * (n : ℝ) ^ L
  have hcost : ∀ᶠ n : ℕ in Filter.atTop,
      ∃ s : ℕ, HasCircuit (identityQuintic R n) s ∧ (s : ℝ) ≤ bound n := by
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
    have hbank : ((bank.bank.circuit.size + bank.ta.size + bank.tc.size : ℕ) : ℝ) ≤
        (C : ℝ) * o * t := by
      have h0 : ((bank.bank.circuit.size + bank.ta.size + bank.tc.size : ℕ) : ℝ) ≤
          (C : ℝ) * o * stateCount (H n + E n) * stateCount (E n) := by
        dsimp only [o]
        exact_mod_cast bank.size_le
      have h1 := mul_le_mul_of_nonneg_left harea'
        (mul_nonneg (Nat.cast_nonneg C) (zero_le_one.trans ho))
      exact h0.trans (by simpa only [Nat.cast_mul, mul_assoc] using h1)
    have hsizeR : (s : ℝ) ≤
        ((bank.bank.circuit.size + bank.ta.size + bank.tc.size : ℕ) : ℝ) +
          p.abc.size + p.bca.size + p.cba.size + p.acb.size + 5 * (n : ℝ) := by
      exact_mod_cast (show s ≤ bank.bank.circuit.size + bank.ta.size + bank.tc.size +
        p.abc.size + p.bca.size + p.cba.size + p.acb.size + 5 * n by omega)
    have hnarea : (n : ℝ) ≤ t :=
      (Nat.cast_le.mpr (batch_capacity n (stateCount (E n)) (stateCount_pos (E n)))).trans hfinal
    rcases hp with ⟨hABC, hACB, _, hBCA, _, hCBA⟩
    have hsum : (s : ℝ) ≤ ((C : ℝ) * o + 9) * t := by
      change (p.abc.size : ℝ) ≤ t at hABC
      change (p.acb.size : ℝ) ≤ t at hACB
      change (p.bca.size : ℝ) ≤ t at hBCA
      change (p.cba.size : ℝ) ≤ t at hCBA
      linarith
    have hfactor : (C : ℝ) * o + 9 ≤ ((C : ℝ) + 9) * o := by linarith
    refine ⟨s, hs, hsum.trans ?_⟩
    simpa only [bound, Nat.cast_add, Nat.cast_ofNat, o, t, mul_assoc] using
      mul_le_mul_of_nonneg_right hfactor ht
  let size (n : ℕ) : ℕ := if h : ∃ s : ℕ,
      HasCircuit (identityQuintic R n) s ∧ (s : ℝ) ≤ bound n then Classical.choose h else 0
  have hchosen : ∀ᶠ n : ℕ in Filter.atTop,
      HasCircuit (identityQuintic R n) (size n) ∧ (size n : ℝ) ≤ bound n :=
    hcost.mono fun n hn => by
      dsimp only [size]
      rw [dif_pos hn]
      exact Classical.choose_spec hn
  have hsizebound := CrossingBounds.eventually_cost_bound (C + 1) H E size L (eps / 2)
    (by linarith) hoverhead (by simpa only [bound, Nat.add_assoc] using hchosen.mono fun _ h => h.2)
  filter_upwards [hchosen, hsizebound] with n hn hbound
  refine ⟨size n, hn.1, ?_⟩
  convert hbound using 1 <;> dsimp [L] <;> congr 1 <;> ring

theorem identity_circuit_bound (R : Type*) [Field R] (C : ℕ)
    (hbanks : ∀ (n H E W : ℕ) (B : Fin n ↪ Index (H + E)),
      0 < W → W ≤ 2 * H → (∀ i, doubledEnergy (B i).val = W) →
        Nonempty (QuinticBank R C n H E W B))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (identityQuintic R n) s ∧
        (s : ℝ) ≤ K * (n : ℝ) ^ (Exponent.gamma + eps) := by
  apply uniform_bound_of_eventually (fun n => identityQuintic R n) (Exponent.gamma + eps)
    (by unfold Exponent.gamma; positivity)
  exact eventually_identity_circuits R C hbanks eps heps

end

end Lemmata.FockCircuits.QuinticExistence
