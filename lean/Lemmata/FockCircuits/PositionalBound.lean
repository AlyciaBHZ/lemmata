module

public import Lemmata.FockCircuits.ModeBanks
public import Lemmata.FockCircuits.ModeAdjoints
public import Lemmata.FockCircuits.CoreBounds

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lemmata.FockCircuits.Positional

open FiniteIdentity Families CrossingCircuit CrossingExistence CrossingAlgorithms CrossingPadding
open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R] {C n H E W : ℕ} {B : Fin n ↪ Index (H + E)}

theorem finite_quartic (bank : ModeBank R C n H E W B)
    (hW : 0 < W) (hWH : W ≤ 2 * H) (hBW : ∀ i, doubledEnergy (B i).val = W)
    (p : AllOrders R (Rows (2 * H) (H + E)) (Actions E) (Batch n E)) :
    ∃ s : ℕ, HasCircuit (quartic R n) s ∧
      s ≤ C * (H + E + 1)^3 * stateCount (H + E) * stateCount E + CoreBounds.matrixCost p +
        9 * (stateCount E * batchCount n (stateCount E)) := by
  classical
  let q := p.restrictModes hWH
  let sa : Rows W (H + E) × Actions E → Outputs n H E W := fun z => .inl ((true, true), z)
  let sb : Rows W (H + E) × Actions E → Outputs n H E W := fun z => .inl ((true, false), z)
  let sc : Rows W (H + E) × Actions E → Outputs n H E W := fun z => .inl ((false, true), z)
  let sd : Rows W (H + E) × Actions E → Outputs n H E W := fun z => .inl ((false, false), z)
  let sy : Actions E × Batch n E → Outputs n H E W := Sum.inr
  let y : Matrix (Actions E) (Batch n E) (Inputs n E) := Matrix.of fun j k => (true, Sum.inr (j,k))
  let u : Matrix (Actions E) (Batch n E) (Inputs n E) := Matrix.of fun j k => (false, Sum.inr (j,k))
  let result : CircuitFamily R (Inputs n E) PUnit.{1} :=
    CrossingCircuit.compile (-(sigma W : R)) bank.circuit sa sb sc sd sy
    (fun z => u z.1 z.2) q.abc q.cba q.cab q.bac
  have hcoeff (i j k l) :
      (∑ r : Rows W (H + E), coefficientA R (dualFamily R B) (action H E) (middle (H + E)) r i j *
        coefficientB R (bareFamily R B) (action H E) (middle (H + E)) r k l) +
      (-(sigma W : R)) * (∑ r : Rows W (H + E), coefficientC R (dualFamily R B) (action H E) (middle (H + E)) r i l *
        coefficientD R (bareFamily R B) (action H E) (middle (H + E)) r k j) =
        if i = k then (if j = l then 1 else 0) else 0 := by
    simpa only [neg_mul, sub_eq_add_neg] using
      family_coefficient_identity R B (action H E) (middle (H + E)) hW hBW (E := E)
        (fun j => cutoffEmbedding_energy (by omega : E ≤ H + E) j)
        (cutoffEmbedding_covers (H + E)) (by omega) i k j l
  have hresult : result.polynomial PUnit.unit = crossingPolynomial (R := R) n (Actions E) (Batch n E) :=
    CrossingCircuit.polynomial_compile_crossing (-(sigma W : R))
      (coefficientA R (dualFamily R B) (action H E) (middle (H + E)))
      (coefficientB R (bareFamily R B) (action H E) (middle (H + E)))
      (coefficientC R (dualFamily R B) (action H E) (middle (H + E)))
      (coefficientD R (bareFamily R B) (action H E) (middle (H + E))) hcoeff
      bank.circuit sa sb sc sd sy (fun i => (true, Sum.inl i)) (fun i => (false, Sum.inl i)) y u
      bank.a_correct bank.b_correct bank.c_correct bank.d_correct bank.y_correct q.abc q.cba q.cab q.bac
  refine ⟨result.size, hasCircuit_quartic (batchEmbedding n E) result hresult, ?_⟩
  have hsize : result.size = bank.circuit.size + p.abc.size + p.cba.size + p.cab.size + p.bac.size +
      4 * (stateCount E * batchCount n (stateCount E)) := by
    simp only [result, CrossingCircuit.size_compile, q, AllOrders.restrictModes, AllOrders.restrict,
      Matrix.OrderedMatrixAlgorithm.size_pad, Fintype.card_coe, Fintype.card_fin, stateCount]
  rw [hsize]
  have hbank := bank.size_le
  unfold CoreBounds.matrixCost
  omega

theorem finite_quintic (bank : QuinticExistence.QuinticBank R C n H E W B)
    (hW : 0 < W) (hWH : W ≤ 2 * H) (hBW : ∀ i, doubledEnergy (B i).val = W)
    (p : AllOrders R (Rows (2 * H) (H + E)) (Actions E) (Batch n E)) :
    ∃ s : ℕ, HasCircuit (quintic R n) s ∧
      s ≤ C * (H + E + 1)^3 * stateCount (H + E) * stateCount E + CoreBounds.matrixCost p +
        9 * (stateCount E * batchCount n (stateCount E)) := by
  classical
  let q := p.restrictModes hWH
  let mapped := bank.bank.circuit.mapInputs (Sum.inl : Inputs n E → Inputs n E ⊕ Fin n)
  let uBank : CircuitFamily R (Inputs n E ⊕ Fin n) (Actions E × Batch n E) :=
    Matrix.CircuitBuilders.family (fun z => Matrix.CircuitBuilders.input (.inl (false, Sum.inr z)))
  let b := mapped.combine uBank
  let sb : Rows W (H + E) × Actions E → Outputs n H E W ⊕ (Actions E × Batch n E) :=
    fun z => .inl (.inl ((true, false), z))
  let sd : Rows W (H + E) × Actions E → Outputs n H E W ⊕ (Actions E × Batch n E) :=
    fun z => .inl (.inl ((false, false), z))
  let sy : Actions E × Batch n E → Outputs n H E W ⊕ (Actions E × Batch n E) := fun z => .inl (.inr z)
  let su : Actions E × Batch n E → Outputs n H E W ⊕ (Actions E × Batch n E) := Sum.inr
  let a := coefficientA R (dualFamily R B) (action H E) (middle (H + E)) (W := W)
  let bCoeff := coefficientB R (bareFamily R B) (action H E) (middle (H + E)) (W := W)
  let c := fun r i j => -(sigma W : R) *
    coefficientC R (dualFamily R B) (action H E) (middle (H + E)) (W := W) r i j
  let d := coefficientD R (bareFamily R B) (action H E) (middle (H + E)) (W := W)
  let x : Fin n → Inputs n E ⊕ Fin n := fun i => .inl (true, Sum.inl i)
  let v : Fin n → Inputs n E ⊕ Fin n := fun i => .inl (false, Sum.inl i)
  let w : Fin n → Inputs n E ⊕ Fin n := Sum.inr
  let y : Matrix (Actions E) (Batch n E) (Inputs n E ⊕ Fin n) := Matrix.of fun j k => .inl (true, Sum.inr (j,k))
  let u : Matrix (Actions E) (Batch n E) (Inputs n E ⊕ Fin n) := Matrix.of fun j k => .inl (false, Sum.inr (j,k))
  let result : CircuitFamily R (Inputs n E ⊕ Fin n) PUnit.{1} :=
    QuinticCompiler.compile (a := a) (c := c) b sb sd sy su q.abc q.bca q.cba q.acb bank.ta bank.tc x w
  have hcoeff (i j k l) : (∑ r, a r i j * bCoeff r k l) + (∑ r, c r i l * d r k j) =
      if i = k then (if j = l then 1 else 0) else 0 := by
    simpa only [a,bCoeff,c,d,mul_assoc,← Finset.mul_sum,neg_mul,Finset.sum_neg_distrib,sub_eq_add_neg] using
      family_coefficient_identity R B (action H E) (middle (H + E)) hW hBW (E := E)
        (fun j => cutoffEmbedding_energy (by omega : E ≤ H + E) j)
        (cutoffEmbedding_covers (H + E)) (by omega) i k j l
  have hb (r j) : b.polynomial (sb (r,j)) = coefficientRows bCoeff (fun i => FreeAlgebra.ι R (v i)) r j := by
    rw [show b.polynomial (sb (r,j)) = mapped.polynomial (.inl ((true,false),(r,j))) by
      exact CircuitFamily.polynomial_combine_inl _ _ _]
    rw [CircuitFamily.polynomial_mapInputs, bank.bank.b_correct]
    simp only [coefficientRows, map_sum, map_smul, FreeAlgebra.lift_ι_apply, bCoeff, v]
  have hd (r j) : b.polynomial (sd (r,j)) = coefficientRows d (fun i => FreeAlgebra.ι R (v i)) r j := by
    rw [show b.polynomial (sd (r,j)) = mapped.polynomial (.inl ((false,false),(r,j))) by
      exact CircuitFamily.polynomial_combine_inl _ _ _]
    rw [CircuitFamily.polynomial_mapInputs, bank.bank.d_correct]
    simp only [coefficientRows, map_sum, map_smul, FreeAlgebra.lift_ι_apply, d, v]
  have hy (j k) : b.polynomial (sy (j,k)) = FreeAlgebra.ι R (y j k) := by
    simp only [y, Matrix.of_apply]
    rw [show b.polynomial (sy (j,k)) = mapped.polynomial (.inr (j,k)) by exact CircuitFamily.polynomial_combine_inl _ _ _]
    rw [CircuitFamily.polynomial_mapInputs, bank.bank.y_correct, FreeAlgebra.lift_ι_apply]
  have hu (j k) : b.polynomial (su (j,k)) = FreeAlgebra.ι R (u j k) := by
    simp [b,su,uBank,CircuitFamily.polynomial,u]
  have hresult : result.polynomial PUnit.unit = gridQuintic R n (Actions E) (Batch n E) :=
    QuinticCompiler.polynomial_compile_crossing b sb sd sy su q.abc q.bca q.cba q.acb
      a bCoeff c d bank.ta bank.tc hcoeff x v w y u hb hd hy hu
  refine ⟨result.size, hasCircuit_quintic (batchEmbedding n E) result hresult, ?_⟩
  have hsize : result.size = bank.bank.circuit.size + p.abc.size + p.bca.size + p.cba.size + p.acb.size +
      bank.ta.size + bank.tc.size + 5*n := by
    simp only [result,QuinticCompiler.size_compile,b,uBank,mapped,CircuitFamily.size_combine,
      CircuitFamily.size_mapInputs,Matrix.CircuitBuilders.size_family,Matrix.CircuitBuilders.size_input,
      Finset.sum_const_zero,add_zero,q,AllOrders.restrictModes,AllOrders.restrict,
      Matrix.OrderedMatrixAlgorithm.size_pad,Fintype.card_fin]
  rw [hsize]
  have hbank := bank.size_le
  have hn := batch_capacity n (stateCount E) (stateCount_pos E)
  unfold CoreBounds.matrixCost
  omega

theorem quartic_bound (R : Type*) [Field R] (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (quartic R n) s ∧ (s : ℝ) ≤ K * (n : ℝ) ^ (Exponent.gamma + eps) := by
  apply CoreBounds.uniform_core_bound R (fun n => quartic R n) 256 _ eps heps
  intro n H E W B hW hWH hBW p
  obtain ⟨bank⟩ := ModeBanks.exists_modeBank R n H E W B hWH hBW
  exact finite_quartic bank hW hWH hBW p

theorem quintic_bound (R : Type*) [Field R] (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (quintic R n) s ∧ (s : ℝ) ≤ K * (n : ℝ) ^ (Exponent.gamma + eps) := by
  apply CoreBounds.uniform_core_bound R (fun n => quintic R n) 512 _ eps heps
  intro n H E W B hW hWH hBW p
  obtain ⟨bank⟩ := ModeBanks.exists_modeBank R n H E W B hWH hBW
  obtain ⟨qbank⟩ := ModeAdjoints.exists_quinticBank R bank hWH hBW
  exact finite_quintic qbank hW hWH hBW p

end

end Lemmata.FockCircuits.Positional
