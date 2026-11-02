module

public import Lemmata.FockCircuits.FiniteTransfer

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lemmata.FockCircuits.FiniteModeTransfer

open FiniteIdentity Families CrossingCircuit CrossingExistence CrossingPadding
open scoped BigOperators

noncomputable section

variable {R X O ρ J K : Type*} [CommRing R] [Fintype O] [Fintype ρ] [Fintype J] [Fintype K]

@[simp] theorem polynomial_inputs (o : O) :
    (ScalarAdjoints.inputs (R := R) O).polynomial o = FreeAlgebra.ι R o :=
  ScalarAdjoints.eval_inputs (algebraMap R (FreeAlgebra R O)) (FreeAlgebra.ι R) o

def template (sign : R) (sa sb sc sd : ρ × J → O) (sy su : J × K → O)
    (p : OrderedMatrixAlgorithm R ρ J K) (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J) (zm : OrderedMatrixAlgorithm R J ρ K) :
    CircuitFamily R O PUnit.{1} :=
  CrossingCircuit.compile sign (ScalarAdjoints.inputs O) sa sb sc sd sy su p q zp zm

theorem size_template (sign : R) (sa sb sc sd : ρ × J → O) (sy su : J × K → O)
    (p : OrderedMatrixAlgorithm R ρ J K) (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J) (zm : OrderedMatrixAlgorithm R J ρ K) :
    (template sign sa sb sc sd sy su p q zp zm).size =
      p.size + q.size + zp.size + zm.size + 4 * (Fintype.card J * Fintype.card K) := by
  simp only [template, CrossingCircuit.size_compile, ScalarAdjoints.size_inputs, zero_add]

theorem eval_template {A : Type*} [Semiring A] [Algebra R A]
    (sign : R) (sa sb sc sd : ρ × J → O) (sy su : J × K → O)
    (p : OrderedMatrixAlgorithm R ρ J K) (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J) (zm : OrderedMatrixAlgorithm R J ρ K) (z : O → A) :
    (template sign sa sb sc sd sy su p q zp zm).eval (algebraMap R A) z PUnit.unit =
      orderedAssembly (Matrix.of (fun r j => z (sa (r,j))))
        (Matrix.of (fun r j => z (sb (r,j))))
        (Matrix.of (fun r j => sign • z (sc (r,j))))
        (Matrix.of (fun r j => z (sd (r,j))))
        (Matrix.of (fun j k => z (sy (j,k)))) (Matrix.of (fun j k => z (su (j,k)))) := by
  rw [← CircuitFamily.polynomial_lift]
  unfold template
  have hpoly := CrossingCircuit.polynomial_compile sign (ScalarAdjoints.inputs O) sa sb sc sd sy
    (Matrix.of (fun j k => sy (j,k))) (Matrix.of (fun j k => su (j,k)))
    (fun j k => by simp only [polynomial_inputs, Matrix.of_apply]) p q zp zm
  have hsu : (fun v : J × K => (Matrix.of (fun j k => su (j,k))) v.1 v.2) = su := by
    funext v
    rcases v with ⟨j,k⟩
    simp only [Matrix.of_apply]
  rw [hsu] at hpoly
  rw [hpoly]
  simp only [orderedAssembly_expansion, map_sum, map_add, map_mul, map_smul,
    polynomial_inputs, Matrix.of_apply, FreeAlgebra.lift_ι_apply]

def sumPrograms (W : ℕ) (f : Fin W → CircuitFamily R O PUnit.{1}) : CircuitFamily R O PUnit.{1} :=
  ((Matrix.CircuitBuilders.parallelFin W f).substitute
    (Matrix.CircuitBuilders.linearFin W (fun _ => (1 : R)) (fun r => (r,PUnit.unit)))).reindexOutputs
      (fun _ => ())

theorem size_sumPrograms (W : ℕ) (f : Fin W → CircuitFamily R O PUnit.{1}) :
    (sumPrograms W f).size = (∑ r, (f r).size) + 2 * W := by
  simp only [sumPrograms, CircuitFamily.size_reindexOutputs, CircuitFamily.size_substitute,
    Matrix.CircuitBuilders.size_parallelFin, Matrix.CircuitBuilders.size_linearFin]

theorem eval_sumPrograms {A : Type*} [Semiring A] [Algebra R A]
    (W : ℕ) (f : Fin W → CircuitFamily R O PUnit.{1}) (z : O → A) :
    (sumPrograms W f).eval (algebraMap R A) z PUnit.unit =
      ∑ r, (f r).eval (algebraMap R A) z PUnit.unit := by
  rw [sumPrograms, CircuitFamily.eval_reindexOutputs, CircuitFamily.eval_substitute,
    Matrix.CircuitBuilders.eval_linearFin]
  simp only [one_smul, Matrix.CircuitBuilders.eval_parallelFin]

theorem sum_assemblies {A : Type*} [Semiring A] (W : ℕ)
    (a b c d : Fin W → Matrix ρ J A) (y u : Matrix J K A) :
    (∑ r, orderedAssembly (a r) (b r) (c r) (d r) y u) =
      orderedAssembly (Matrix.of (fun (r : Fin W × ρ) j => a r.1 r.2 j))
        (Matrix.of (fun (r : Fin W × ρ) j => b r.1 r.2 j))
        (Matrix.of (fun (r : Fin W × ρ) j => c r.1 r.2 j))
        (Matrix.of (fun (r : Fin W × ρ) j => d r.1 r.2 j)) y u := by
  have move (f : Fin W → J → K → A) :
      (∑ r, ∑ j, ∑ k, f r j k) = ∑ j, ∑ k, ∑ r, f r j k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
  simp only [orderedAssembly_expansion, Matrix.of_apply, Fintype.sum_prod_type,
    Finset.sum_add_distrib]
  congr 1 <;> exact move _

def build (bank : CircuitFamily R X O) (sign : R) (W : ℕ)
    (sa sb sc sd : (Fin W × ρ) × J → O) (sy su : J × K → O)
    (p : OrderedMatrixAlgorithm R ρ J K) (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J) (zm : OrderedMatrixAlgorithm R J ρ K) :
    CircuitFamily R X PUnit.{1} :=
  bank.substitute (sumPrograms W (fun r => template sign
    (fun z => sa ((r,z.1),z.2)) (fun z => sb ((r,z.1),z.2))
    (fun z => sc ((r,z.1),z.2)) (fun z => sd ((r,z.1),z.2)) sy su p q zp zm))

theorem size_build (bank : CircuitFamily R X O) (sign : R) (W : ℕ)
    (sa sb sc sd : (Fin W × ρ) × J → O) (sy su : J × K → O)
    (p : OrderedMatrixAlgorithm R ρ J K) (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J) (zm : OrderedMatrixAlgorithm R J ρ K) :
    (build bank sign W sa sb sc sd sy su p q zp zm).size =
      bank.size + W * (p.size + q.size + zp.size + zm.size +
        4 * (Fintype.card J * Fintype.card K)) + 2 * W := by
  simp only [build, CircuitFamily.size_substitute, size_sumPrograms, size_template,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  omega

theorem polynomial_build (bank : CircuitFamily R X O) (sign : R) (W : ℕ)
    (sa sb sc sd : (Fin W × ρ) × J → O) (sy su : J × K → O)
    (p : OrderedMatrixAlgorithm R ρ J K) (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J) (zm : OrderedMatrixAlgorithm R J ρ K) :
    (build bank sign W sa sb sc sd sy su p q zp zm).polynomial PUnit.unit =
      orderedAssembly (Matrix.of (fun r j => bank.polynomial (sa (r,j))))
        (Matrix.of (fun r j => bank.polynomial (sb (r,j))))
        (Matrix.of (fun r j => sign • bank.polynomial (sc (r,j))))
        (Matrix.of (fun r j => bank.polynomial (sd (r,j))))
        (Matrix.of (fun j k => bank.polynomial (sy (j,k))))
        (Matrix.of (fun j k => bank.polynomial (su (j,k)))) := by
  change (build bank sign W sa sb sc sd sy su p q zp zm).eval
    (algebraMap R (FreeAlgebra R X)) (FreeAlgebra.ι R) PUnit.unit = _
  rw [build, CircuitFamily.eval_substitute, eval_sumPrograms]
  change (∑ r, (template sign _ _ _ _ sy su p q zp zm).eval
    (algebraMap R (FreeAlgebra R X)) bank.polynomial PUnit.unit) = _
  simp_rw [eval_template]
  exact sum_assemblies W _ _ _ _ _ _

theorem polynomial_build_crossing {I : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (bank : CircuitFamily R X O) (sign : R) (W : ℕ)
    (a b c d : (Fin W × ρ) → I → J → R)
    (hcoeff : ∀ i j k l, (∑ r, a r i j * b r k l) + sign * (∑ r, c r i l * d r k j) =
      if i = k then (if j = l then 1 else 0) else 0)
    (sa sb sc sd : (Fin W × ρ) × J → O) (sy su : J × K → O)
    (x v : I → X) (y u : Matrix J K X)
    (ha : ∀ r j, bank.polynomial (sa (r,j)) = coefficientRows a (fun i => FreeAlgebra.ι R (x i)) r j)
    (hb : ∀ r j, bank.polynomial (sb (r,j)) = coefficientRows b (fun i => FreeAlgebra.ι R (v i)) r j)
    (hc : ∀ r j, bank.polynomial (sc (r,j)) = coefficientRows c (fun i => FreeAlgebra.ι R (x i)) r j)
    (hd : ∀ r j, bank.polynomial (sd (r,j)) = coefficientRows d (fun i => FreeAlgebra.ι R (v i)) r j)
    (hy : ∀ j k, bank.polynomial (sy (j,k)) = FreeAlgebra.ι R (y j k))
    (hu : ∀ j k, bank.polynomial (su (j,k)) = FreeAlgebra.ι R (u j k))
    (p : OrderedMatrixAlgorithm R ρ J K) (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J) (zm : OrderedMatrixAlgorithm R J ρ K) :
    (build bank sign W sa sb sc sd sy su p q zp zm).polynomial PUnit.unit =
      batchedCrossing (fun i => FreeAlgebra.ι R (x i)) (fun i => FreeAlgebra.ι R (v i))
        (Matrix.of (fun j k => FreeAlgebra.ι R (y j k))) (Matrix.of (fun j k => FreeAlgebra.ι R (u j k))) := by
  rw [polynomial_build]
  have ha' : Matrix.of (fun r j => bank.polynomial (sa (r,j))) =
      coefficientRows a (fun i => FreeAlgebra.ι R (x i)) := by ext r j; exact ha r j
  have hb' : Matrix.of (fun r j => bank.polynomial (sb (r,j))) =
      coefficientRows b (fun i => FreeAlgebra.ι R (v i)) := by ext r j; exact hb r j
  have hc' : Matrix.of (fun r j => sign • bank.polynomial (sc (r,j))) =
      coefficientRows (fun r i j => sign * c r i j) (fun i => FreeAlgebra.ι R (x i)) := by
    ext r j
    rw [Matrix.of_apply,hc,coefficientRows_scale]
  have hd' : Matrix.of (fun r j => bank.polynomial (sd (r,j))) =
      coefficientRows d (fun i => FreeAlgebra.ι R (v i)) := by ext r j; exact hd r j
  have hy' : Matrix.of (fun j k => bank.polynomial (sy (j,k))) =
      Matrix.of (fun j k => FreeAlgebra.ι R (y j k)) := by ext j k; exact hy j k
  have hu' : Matrix.of (fun j k => bank.polynomial (su (j,k))) =
      Matrix.of (fun j k => FreeAlgebra.ι R (u j k)) := by ext j k; exact hu j k
  rw [ha',hb',hc',hd',hy',hu']
  apply directAssembly_eq_crossing
  intro i j k l
  simpa only [mul_assoc,← Finset.mul_sum] using hcoeff i j k l

section Canonical

variable {C n H E W : ℕ} {B : Fin n ↪ Index (H + E)}

theorem grouped_circuit (bank : ModeBank R C n H E W B) (hW : 0 < W) (hWH : W ≤ 2 * H)
    (hBW : ∀ i, doubledEnergy (B i).val = W) (K : Type*) [Fintype K]
    (p : OrderedMatrixAlgorithm R ↥(fullCutoff (H + E)) (Actions E) K)
    (q : OrderedMatrixAlgorithm R K (Actions E) ↥(fullCutoff (H + E)))
    (zp : OrderedMatrixAlgorithm R K ↥(fullCutoff (H + E)) (Actions E))
    (zm : OrderedMatrixAlgorithm R (Actions E) ↥(fullCutoff (H + E)) K) :
    ∃ c : CircuitFamily R (Variables n (Actions E) K) PUnit.{1},
      c.polynomial PUnit.unit = crossingPolynomial (R := R) n (Actions E) K ∧
        c.size = bank.circuit.size + W * (p.size + q.size + zp.size + zm.size +
          4 * (stateCount E * Fintype.card K)) + 2 * W := by
  classical
  let roles := (FiniteTransfer.zeroAuxiliary (R := R) n E K).substitute bank.circuit
  let total := roles.combine (ScalarAdjoints.inputs (R := R) (Variables n (Actions E) K))
  let sa : Rows W (H + E) × Actions E → Outputs n H E W ⊕ Variables n (Actions E) K :=
    fun z => .inl (.inl ((true,true),z))
  let sb : Rows W (H + E) × Actions E → Outputs n H E W ⊕ Variables n (Actions E) K :=
    fun z => .inl (.inl ((true,false),z))
  let sc : Rows W (H + E) × Actions E → Outputs n H E W ⊕ Variables n (Actions E) K :=
    fun z => .inl (.inl ((false,true),z))
  let sd : Rows W (H + E) × Actions E → Outputs n H E W ⊕ Variables n (Actions E) K :=
    fun z => .inl (.inl ((false,false),z))
  let sy : Actions E × K → Outputs n H E W ⊕ Variables n (Actions E) K := fun z => .inr (true,Sum.inr z)
  let su : Actions E × K → Outputs n H E W ⊕ Variables n (Actions E) K := fun z => .inr (false,Sum.inr z)
  let x : Fin n → Variables n (Actions E) K := fun i => (true,Sum.inl i)
  let v : Fin n → Variables n (Actions E) K := fun i => (false,Sum.inl i)
  let y : Matrix (Actions E) K (Variables n (Actions E) K) := Matrix.of fun j k => (true,Sum.inr (j,k))
  let u : Matrix (Actions E) K (Variables n (Actions E) K) := Matrix.of fun j k => (false,Sum.inr (j,k))
  let a := coefficientA R (dualFamily R B) (action H E) (middle (H + E)) (W := W)
  let b := coefficientB R (bareFamily R B) (action H E) (middle (H + E)) (W := W)
  let c := coefficientC R (dualFamily R B) (action H E) (middle (H + E)) (W := W)
  let d := coefficientD R (bareFamily R B) (action H E) (middle (H + E)) (W := W)
  have hcoeff (i j k l) : (∑ r, a r i j * b r k l) + (-(sigma W : R)) * (∑ r, c r i l * d r k j) =
      if i = k then (if j = l then 1 else 0) else 0 := by
    simpa only [a,b,c,d,neg_mul,sub_eq_add_neg] using
      family_coefficient_identity R B (action H E) (middle (H + E)) hW hBW (E := E)
        (fun j => cutoffEmbedding_energy (by omega : E ≤ H + E) j)
        (cutoffEmbedding_covers (H + E)) (by omega) i k j l
  have ha (r j) : total.polynomial (sa (r,j)) = coefficientRows a (fun i => FreeAlgebra.ι R (x i)) r j := by
    rw [show total.polynomial (sa (r,j)) = roles.polynomial (.inl ((true,true),(r,j))) by exact CircuitFamily.polynomial_combine_inl _ _ _]
    rw [CircuitFamily.polynomial_substitute,bank.a_correct]
    simp only [coefficientRows,map_sum,map_smul,FreeAlgebra.lift_ι_apply,FiniteTransfer.polynomial_zeroAuxiliary_left,a,x]
  have hb (r j) : total.polynomial (sb (r,j)) = coefficientRows b (fun i => FreeAlgebra.ι R (v i)) r j := by
    rw [show total.polynomial (sb (r,j)) = roles.polynomial (.inl ((true,false),(r,j))) by exact CircuitFamily.polynomial_combine_inl _ _ _]
    rw [CircuitFamily.polynomial_substitute,bank.b_correct]
    simp only [coefficientRows,map_sum,map_smul,FreeAlgebra.lift_ι_apply,FiniteTransfer.polynomial_zeroAuxiliary_left,b,v]
  have hc (r j) : total.polynomial (sc (r,j)) = coefficientRows c (fun i => FreeAlgebra.ι R (x i)) r j := by
    rw [show total.polynomial (sc (r,j)) = roles.polynomial (.inl ((false,true),(r,j))) by exact CircuitFamily.polynomial_combine_inl _ _ _]
    rw [CircuitFamily.polynomial_substitute,bank.c_correct]
    simp only [coefficientRows,map_sum,map_smul,FreeAlgebra.lift_ι_apply,FiniteTransfer.polynomial_zeroAuxiliary_left,c,x]
  have hd (r j) : total.polynomial (sd (r,j)) = coefficientRows d (fun i => FreeAlgebra.ι R (v i)) r j := by
    rw [show total.polynomial (sd (r,j)) = roles.polynomial (.inl ((false,false),(r,j))) by exact CircuitFamily.polynomial_combine_inl _ _ _]
    rw [CircuitFamily.polynomial_substitute,bank.d_correct]
    simp only [coefficientRows,map_sum,map_smul,FreeAlgebra.lift_ι_apply,FiniteTransfer.polynomial_zeroAuxiliary_left,d,v]
  have hy (j k) : total.polynomial (sy (j,k)) = FreeAlgebra.ι R (y j k) := by
    simp [total,sy,y,polynomial_inputs]
  have hu (j k) : total.polynomial (su (j,k)) = FreeAlgebra.ι R (u j k) := by
    simp [total,su,u,polynomial_inputs]
  let result := build total (-(sigma W : R)) W sa sb sc sd sy su p q zp zm
  refine ⟨result,polynomial_build_crossing total (-(sigma W : R)) W a b c d hcoeff
    sa sb sc sd sy su x v y u ha hb hc hd hy hu p q zp zm,?_⟩
  have htotal : total.size = bank.circuit.size := by
    simp [total,roles,FiniteTransfer.size_zeroAuxiliary]
  simpa only [result,size_build,htotal,Fintype.card_coe,stateCount]

theorem cost_bound (H E W D T P : ℕ) (hW : W ≤ 2 * H) :
    256 * (H + E + 1)^3 * D + W * (P + 4 * T) + 2 * W ≤
      288 * (H + E + 1)^3 * (P + D + T + 1) := by
  let L := H + E + 1
  let M := P + D + T + 1
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hD : D ≤ M := by dsimp [M]; omega
  have hP : P ≤ M := by dsimp [M]; omega
  have hT : T ≤ M := by dsimp [M]; omega
  have hWL : W ≤ 2 * L := by dsimp [L]; omega
  have hcube : L ≤ L^3 := by
    calc
      L = 1 * L := by omega
      _ ≤ L^2 * L := Nat.mul_le_mul_right L (one_le_pow₀ hL)
      _ = L^3 := by ring
  have hbank := Nat.mul_le_mul_left (256 * L^3) hD
  have hproducts : W * (P + 4*T) + 2*W ≤ 14 * L^3 * M := by
    have hpt : P + 4*T ≤ 5*M := by omega
    have hp := Nat.mul_le_mul_left W hpt
    have hone := Nat.mul_le_mul_left (2*W) hM
    have hw := Nat.mul_le_mul_right (7*M) hWL
    have hl := Nat.mul_le_mul_left (14*M) hcube
    nlinarith
  have hsum := Nat.add_le_add hbank hproducts
  have hconstant := Nat.mul_le_mul_right (L^3*M) (by decide : 270 ≤ 288)
  dsimp only [L,M] at *
  nlinarith

theorem finite_transfer (R : Type*) [CommRing R] (n N H E : ℕ)
    (hH : 0 < H) (hcapacity : 2 * H * n ≤ stateCount H - 1)
    (p : OrderedMatrixAlgorithm R ↥(fullCutoff (H + E)) (Actions E) (Batch N E))
    (q : OrderedMatrixAlgorithm R (Batch N E) (Actions E) ↥(fullCutoff (H + E)))
    (zp : OrderedMatrixAlgorithm R (Batch N E) ↥(fullCutoff (H + E)) (Actions E))
    (zm : OrderedMatrixAlgorithm R (Actions E) ↥(fullCutoff (H + E)) (Batch N E)) :
    ∃ s : ℕ, HasCircuit (FiniteTransfer.phi R n N) s ∧
      s ≤ 288 * (H + E + 1)^3 * (p.size + q.size + zp.size + zm.size +
        stateCount (H + E) * stateCount E + stateCount E * batchCount N (stateCount E) + 1) := by
  classical
  obtain ⟨W,B,hW,hWH,hBinj,hBW,_⟩ := exists_dual_family R H (H + E) n hH (by omega) hcapacity
  let B' : Fin n ↪ Index (H + E) := ⟨B,hBinj⟩
  obtain ⟨bank⟩ := ModeBanks.exists_modeBank R n H E W B' hWH hBW
  obtain ⟨c,hc,hsize⟩ := grouped_circuit bank hW hWH hBW (Batch N E) p q zp zm
  refine ⟨c.size,FiniteTransfer.hasCircuit_padding (batchEmbedding N E) c hc,?_⟩
  rw [hsize,Fintype.card_fin]
  have hb := bank.size_le
  have hcost := cost_bound H E W (stateCount (H + E) * stateCount E)
    (stateCount E * batchCount N (stateCount E)) (p.size + q.size + zp.size + zm.size) hWH
  nlinarith

end Canonical

end

end Lemmata.FockCircuits.FiniteModeTransfer
