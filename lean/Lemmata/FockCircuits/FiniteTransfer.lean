module

public import Lemmata.FockCircuits.ModeBanks
public import Lemmata.FockCircuits.Positional

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lemmata.FockCircuits.FiniteTransfer

open FiniteIdentity Families CrossingCircuit CrossingExistence CrossingPadding
open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

def phi (R : Type*) [CommSemiring R] (n N : ℕ) : FreeAlgebra R (Bool × (Fin n ⊕ Fin N)) :=
  ∑ i, ∑ j, FreeAlgebra.ι R (true, Sum.inl i) * FreeAlgebra.ι R (true, Sum.inr j) *
    FreeAlgebra.ι R (false, Sum.inl i) * FreeAlgebra.ι R (false, Sum.inr j)

def zeroAuxiliary (n E : ℕ) (K : Type*) [Fintype K] :
    CircuitFamily R (Variables n (Actions E) K) (Inputs n E) :=
  Matrix.CircuitBuilders.family (fun p : Inputs n E => match p.2 with
    | Sum.inl i => Matrix.CircuitBuilders.input (p.1, Sum.inl i)
    | Sum.inr _ => Matrix.CircuitBuilders.scalar 0)

theorem size_zeroAuxiliary (n E : ℕ) (K : Type*) [Fintype K] :
    (zeroAuxiliary (R := R) n E K).size = 0 := by
  rw [zeroAuxiliary, Matrix.CircuitBuilders.size_family]
  apply Finset.sum_eq_zero
  intro p hp
  cases h : p.2 <;> simp [h]

@[simp] theorem polynomial_zeroAuxiliary_left (n E : ℕ) (K : Type*) [Fintype K]
    (b : Bool) (i : Fin n) :
    (zeroAuxiliary (R := R) n E K).polynomial (b, Sum.inl i) = FreeAlgebra.ι R (b, Sum.inl i) := by
  simp [zeroAuxiliary, CircuitFamily.polynomial]

theorem grouped_circuit {C n H E W : ℕ} {B : Fin n ↪ Index (H + E)}
    (bank : ModeBank R C n H E W B) (hW : 0 < W) (hWH : W ≤ 2 * H)
    (hBW : ∀ i, doubledEnergy (B i).val = W) (K : Type*) [Fintype K]
    (p : OrderedMatrixAlgorithm R (Rows W (H + E)) (Actions E) K)
    (q : OrderedMatrixAlgorithm R K (Actions E) (Rows W (H + E)))
    (zp : OrderedMatrixAlgorithm R K (Rows W (H + E)) (Actions E))
    (zm : OrderedMatrixAlgorithm R (Actions E) (Rows W (H + E)) K) :
    ∃ c : CircuitFamily R (Variables n (Actions E) K) PUnit.{1},
      c.polynomial PUnit.unit = crossingPolynomial (R := R) n (Actions E) K ∧
        c.size = bank.circuit.size + p.size + q.size + zp.size + zm.size +
          4 * (stateCount E * Fintype.card K) := by
  classical
  let roles := (zeroAuxiliary (R := R) n E K).substitute bank.circuit
  let yBank : CircuitFamily R (Variables n (Actions E) K) (Actions E × K) :=
    Matrix.CircuitBuilders.family (fun z => Matrix.CircuitBuilders.input (true, Sum.inr z))
  let total := roles.combine yBank
  let sa : Rows W (H + E) × Actions E → Outputs n H E W ⊕ (Actions E × K) := fun z => .inl (.inl ((true,true),z))
  let sb : Rows W (H + E) × Actions E → Outputs n H E W ⊕ (Actions E × K) := fun z => .inl (.inl ((true,false),z))
  let sc : Rows W (H + E) × Actions E → Outputs n H E W ⊕ (Actions E × K) := fun z => .inl (.inl ((false,true),z))
  let sd : Rows W (H + E) × Actions E → Outputs n H E W ⊕ (Actions E × K) := fun z => .inl (.inl ((false,false),z))
  let sy : Actions E × K → Outputs n H E W ⊕ (Actions E × K) := Sum.inr
  let x : Fin n → Variables n (Actions E) K := fun i => (true, Sum.inl i)
  let v : Fin n → Variables n (Actions E) K := fun i => (false, Sum.inl i)
  let y : Matrix (Actions E) K (Variables n (Actions E) K) := Matrix.of fun j k => (true, Sum.inr (j,k))
  let u : Matrix (Actions E) K (Variables n (Actions E) K) := Matrix.of fun j k => (false, Sum.inr (j,k))
  let a := coefficientA R (dualFamily R B) (action H E) (middle (H + E)) (W := W)
  let b := coefficientB R (bareFamily R B) (action H E) (middle (H + E)) (W := W)
  let c := coefficientC R (dualFamily R B) (action H E) (middle (H + E)) (W := W)
  let d := coefficientD R (bareFamily R B) (action H E) (middle (H + E)) (W := W)
  have hcoeff (i j k l) : (∑ r, a r i j * b r k l) +
      (-(sigma W : R)) * (∑ r, c r i l * d r k j) =
        if i = k then (if j = l then 1 else 0) else 0 := by
    simpa only [a,b,c,d,neg_mul,sub_eq_add_neg] using
      family_coefficient_identity R B (action H E) (middle (H + E)) hW hBW (E := E)
        (fun j => cutoffEmbedding_energy (by omega : E ≤ H + E) j)
        (cutoffEmbedding_covers (H + E)) (by omega) i k j l
  have ha (r j) : total.polynomial (sa (r,j)) = coefficientRows a (fun i => FreeAlgebra.ι R (x i)) r j := by
    rw [show total.polynomial (sa (r,j)) = roles.polynomial (.inl ((true,true),(r,j))) by exact CircuitFamily.polynomial_combine_inl _ _ _]
    rw [CircuitFamily.polynomial_substitute,bank.a_correct]
    simp only [coefficientRows,map_sum,map_smul,FreeAlgebra.lift_ι_apply,polynomial_zeroAuxiliary_left,a,x]
  have hb (r j) : total.polynomial (sb (r,j)) = coefficientRows b (fun i => FreeAlgebra.ι R (v i)) r j := by
    rw [show total.polynomial (sb (r,j)) = roles.polynomial (.inl ((true,false),(r,j))) by exact CircuitFamily.polynomial_combine_inl _ _ _]
    rw [CircuitFamily.polynomial_substitute,bank.b_correct]
    simp only [coefficientRows,map_sum,map_smul,FreeAlgebra.lift_ι_apply,polynomial_zeroAuxiliary_left,b,v]
  have hc (r j) : total.polynomial (sc (r,j)) = coefficientRows c (fun i => FreeAlgebra.ι R (x i)) r j := by
    rw [show total.polynomial (sc (r,j)) = roles.polynomial (.inl ((false,true),(r,j))) by exact CircuitFamily.polynomial_combine_inl _ _ _]
    rw [CircuitFamily.polynomial_substitute,bank.c_correct]
    simp only [coefficientRows,map_sum,map_smul,FreeAlgebra.lift_ι_apply,polynomial_zeroAuxiliary_left,c,x]
  have hd (r j) : total.polynomial (sd (r,j)) = coefficientRows d (fun i => FreeAlgebra.ι R (v i)) r j := by
    rw [show total.polynomial (sd (r,j)) = roles.polynomial (.inl ((false,false),(r,j))) by exact CircuitFamily.polynomial_combine_inl _ _ _]
    rw [CircuitFamily.polynomial_substitute,bank.d_correct]
    simp only [coefficientRows,map_sum,map_smul,FreeAlgebra.lift_ι_apply,polynomial_zeroAuxiliary_left,d,v]
  have hy (j k) : total.polynomial (sy (j,k)) = FreeAlgebra.ι R (y j k) := by
    simp [total,sy,yBank,CircuitFamily.polynomial,y]
  let result : CircuitFamily R (Variables n (Actions E) K) PUnit.{1} :=
    CrossingCircuit.compile (-(sigma W : R)) total sa sb sc sd sy (fun z => u z.1 z.2) p q zp zm
  refine ⟨result, ?_, ?_⟩
  · exact CrossingCircuit.polynomial_compile_crossing (-(sigma W : R)) a b c d hcoeff
      total sa sb sc sd sy x v y u ha hb hc hd hy p q zp zm
  · have htotal : total.size = bank.circuit.size := by
      simp [total,roles,yBank,size_zeroAuxiliary]
    simpa only [result,CrossingCircuit.size_compile,htotal,Fintype.card_coe,stateCount]

def paddingColour {n N : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin N ↪ J × K) (b : Bool) :
    CircuitFamily R (Bool × (Fin n ⊕ Fin N)) (Fin n ⊕ (J × K)) :=
  (Matrix.CircuitBuilders.family (fun i => Matrix.CircuitBuilders.input (b, Sum.inl i))).combine
    (SourceBanks.sourceBank e (fun j => (b, Sum.inr j)))

def paddingBank {n N : ℕ} {J K : Type*} [Fintype J] [Fintype K] (e : Fin N ↪ J × K) :
    CircuitFamily R (Bool × (Fin n ⊕ Fin N)) (Variables n J K) :=
  ((paddingColour e true).combine (paddingColour e false)).reindexOutputs
    (fun z => if z.1 then .inl z.2 else .inr z.2)

@[simp] theorem size_paddingColour {n N : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin N ↪ J × K) (b : Bool) : (paddingColour (R := R) (n := n) e b).size = 0 := by
  simp [paddingColour,SourceBanks.size_sourceBank]

@[simp] theorem size_paddingBank {n N : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin N ↪ J × K) : (paddingBank (R := R) (n := n) e).size = 0 := by simp [paddingBank]

@[simp] theorem polynomial_paddingBank_left {n N : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin N ↪ J × K) (b : Bool) (i : Fin n) :
    (paddingBank (R := R) e).polynomial (b,Sum.inl i) = FreeAlgebra.ι R (b,Sum.inl i) := by
  cases b <;> simp [paddingBank,paddingColour,CircuitFamily.polynomial]

@[simp] theorem polynomial_paddingBank_right {n N : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin N ↪ J × K) (b : Bool) (j : J) (k : K) :
    (paddingBank (R := R) (n := n) e).polynomial (b,Sum.inr (j,k)) =
      Function.extend e (fun i => FreeAlgebra.ι R (b,Sum.inr i)) (fun _ => 0) (j,k) := by
  cases b <;> simp [paddingBank,paddingColour,SourceBanks.polynomial_sourceBank]

theorem hasCircuit_padding {n N : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin N ↪ J × K) (c : CircuitFamily R (Variables n J K) PUnit)
    (hc : c.polynomial PUnit.unit = crossingPolynomial (R := R) n J K) :
    HasCircuit (phi R n N) c.size := by
  let d := (paddingBank (R := R) e).substitute c
  refine ⟨d.nodeCount,d.circuit,d.output PUnit.unit,?_,?_⟩
  · change d.polynomial PUnit.unit = _
    rw [CircuitFamily.polynomial_substitute,hc]
    simp only [crossingPolynomial,batchedCrossing,map_sum,map_mul,FreeAlgebra.lift_ι_apply,
      polynomial_paddingBank_left,polynomial_paddingBank_right,Matrix.of_apply]
    unfold phi
    apply Finset.sum_congr rfl
    intro i hi
    apply Positional.sum_padded e _ _ (fun y u => FreeAlgebra.ι R (true,Sum.inl i) * y *
      FreeAlgebra.ι R (false,Sum.inl i) * u)
    simp
  · change d.size ≤ c.size
    simp [d]

theorem finite_transfer (R : Type*) [CommRing R] (n N H E : ℕ)
    (hH : 0 < H) (hcapacity : 2 * H * n ≤ stateCount H - 1) :
    ∃ W : ℕ, 0 < W ∧ W ≤ 2 * H ∧
      ∀ (p : OrderedMatrixAlgorithm R (Rows W (H + E)) (Actions E) (Batch N E))
        (q : OrderedMatrixAlgorithm R (Batch N E) (Actions E) (Rows W (H + E)))
        (zp : OrderedMatrixAlgorithm R (Batch N E) (Rows W (H + E)) (Actions E))
        (zm : OrderedMatrixAlgorithm R (Actions E) (Rows W (H + E)) (Batch N E)),
        ∃ s : ℕ, HasCircuit (phi R n N) s ∧
          s ≤ 256 * (H + E + 1)^3 * stateCount (H + E) * stateCount E +
            p.size + q.size + zp.size + zm.size + 4 * (stateCount E * batchCount N (stateCount E)) := by
  classical
  obtain ⟨W,B,hW,hWH,hBinj,hBW,_⟩ := exists_dual_family R H (H + E) n hH (by omega) hcapacity
  let B' : Fin n ↪ Index (H + E) := ⟨B,hBinj⟩
  obtain ⟨bank⟩ := ModeBanks.exists_modeBank R n H E W B' hWH hBW
  refine ⟨W,hW,hWH,fun p q zp zm => ?_⟩
  obtain ⟨c,hc,hsize⟩ := grouped_circuit bank hW hWH hBW (Batch N E) p q zp zm
  refine ⟨c.size,hasCircuit_padding (batchEmbedding N E) c hc,?_⟩
  rw [hsize]
  have hb := bank.size_le
  simp only [Fintype.card_fin]
  omega

end

end Lemmata.FockCircuits.FiniteTransfer
