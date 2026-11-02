module

public import Lemmata.FockCircuits.PrefixExtraction

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits

open scoped BigOperators
open Lemmata.FockCircuits.Matrix

noncomputable section

structure ScalarTransposeAlgorithm (R I O : Type*) [CommSemiring R] [Fintype O]
    (a : O → I → R) where
  circuit : CircuitFamily R O I
  correct : ∀ i, circuit.polynomial i = ∑ o, a o i • FreeAlgebra.ι R o

namespace ScalarTransposeAlgorithm

variable {R I O X P : Type*} [CommSemiring R] [Fintype O]
variable {a : O → I → R}

def size (t : ScalarTransposeAlgorithm R I O a) : ℕ := t.circuit.size

def appendUsing (t : ScalarTransposeAlgorithm R I O a)
    (bank : CircuitFamily R X P) (inputs : O → P) : CircuitFamily R X (P ⊕ I) :=
  bank.extendUsing inputs t.circuit

@[simp] theorem size_appendUsing (t : ScalarTransposeAlgorithm R I O a)
    (bank : CircuitFamily R X P) (inputs : O → P) :
    (t.appendUsing bank inputs).size = bank.size + t.size :=
  CircuitFamily.size_extendUsing bank inputs t.circuit

@[simp] theorem polynomial_appendUsing_old (t : ScalarTransposeAlgorithm R I O a)
    (bank : CircuitFamily R X P) (inputs : O → P) (p : P) :
    (t.appendUsing bank inputs).polynomial (.inl p) = bank.polynomial p :=
  CircuitFamily.polynomial_extendUsing_inl bank inputs t.circuit p

theorem polynomial_appendUsing_new (t : ScalarTransposeAlgorithm R I O a)
    (bank : CircuitFamily R X P) (inputs : O → P) (i : I) :
    (t.appendUsing bank inputs).polynomial (.inr i) =
      ∑ o, a o i • bank.polynomial (inputs o) := by
  rw [appendUsing, CircuitFamily.polynomial_extendUsing_inr, t.correct]
  simp

/-- A proved pairing identity supplies the exact coefficient transpose of an actual linear circuit. -/
def ofAdjoint [Fintype I] [DecidableEq I]
    (forward : CircuitFamily R I O) (transpose : CircuitFamily R O I)
    (hlinear : ∀ o, forward.polynomial o = ∑ i, a o i • FreeAlgebra.ι R i)
    (hadjoint : ∀ (x : I → FreeAlgebra R O) (y : O → FreeAlgebra R O),
      (∑ o, forward.eval (algebraMap R (FreeAlgebra R O)) x o * y o) =
        ∑ i, x i * transpose.eval (algebraMap R (FreeAlgebra R O)) y i) :
    ScalarTransposeAlgorithm R I O a where
  circuit := transpose
  correct := by
    intro i
    let x : I → FreeAlgebra R O := fun j => if j = i then 1 else 0
    have hforward (o : O) : forward.eval (algebraMap R (FreeAlgebra R O)) x o =
        algebraMap R (FreeAlgebra R O) (a o i) := by
      rw [← CircuitFamily.polynomial_lift, hlinear]
      simp [x, Algebra.smul_def, mul_ite]
    have h := hadjoint x (FreeAlgebra.ι R)
    simp_rw [hforward] at h
    simp only [x, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at h
    simpa only [CircuitFamily.polynomial, Algebra.smul_def] using h.symm

end ScalarTransposeAlgorithm

namespace QuinticCompiler

variable {R X O I ρ J K : Type*} [CommSemiring R]
variable [Fintype I] [Fintype ρ] [Fintype J] [Fintype K]

def bankMatrix {L M : Type*} (bank : CircuitFamily R X O) (slots : L × M → O) :
    Matrix L M (FreeAlgebra R X) := Matrix.of (fun l m => bank.polynomial (slots (l, m)))

def contexts (bank : CircuitFamily R X O)
    (sb sd : ρ × J → O) (sy su : J × K → O)
    (p1 : OrderedMatrixAlgorithm R ρ J K) (p2 : OrderedMatrixAlgorithm R J K ρ)
    (p3 : OrderedMatrixAlgorithm R K J ρ) (p4 : OrderedMatrixAlgorithm R ρ K J) :
    CircuitFamily R X (Bool × (ρ × J)) :=
  let s1 := p1.appendUsing bank (Sum.elim sb su)
  let s2 := p2.appendUsing s1 (Sum.elim (fun q => .inl (sy q)) (fun q => .inr (q.2, q.1)))
  let s3 := p3.appendUsing s2 (Sum.elim
    (fun q => .inl (.inl (sy (q.2, q.1))))
    (fun q => .inl (.inl (sd (q.2, q.1)))))
  let s4 := p4.appendUsing s3 (Sum.elim
    (fun q => .inr (q.2, q.1))
    (fun q => .inl (.inl (.inl (su (q.2, q.1))))))
  s4.reindexOutputs (fun q => if q.1 then .inl (.inl (.inr (q.2.2, q.2.1))) else .inr q.2)

theorem size_contexts (bank : CircuitFamily R X O)
    (sb sd : ρ × J → O) (sy su : J × K → O)
    (p1 : OrderedMatrixAlgorithm R ρ J K) (p2 : OrderedMatrixAlgorithm R J K ρ)
    (p3 : OrderedMatrixAlgorithm R K J ρ) (p4 : OrderedMatrixAlgorithm R ρ K J) :
    (contexts bank sb sd sy su p1 p2 p3 p4).size =
      bank.size + p1.size + p2.size + p3.size + p4.size := by
  simp only [contexts, CircuitFamily.size_reindexOutputs, OrderedMatrixAlgorithm.size_appendUsing]

theorem polynomial_contexts_true (bank : CircuitFamily R X O)
    (sb sd : ρ × J → O) (sy su : J × K → O)
    (p1 : OrderedMatrixAlgorithm R ρ J K) (p2 : OrderedMatrixAlgorithm R J K ρ)
    (p3 : OrderedMatrixAlgorithm R K J ρ) (p4 : OrderedMatrixAlgorithm R ρ K J) (r : ρ) (j : J) :
    (contexts bank sb sd sy su p1 p2 p3 p4).polynomial (true, (r, j)) =
      PrefixExtraction.firstContext (bankMatrix bank sb) (bankMatrix bank sy) (bankMatrix bank su) r j := by
  simp [contexts, OrderedMatrixAlgorithm.polynomial_appendUsing_new,
    PrefixExtraction.firstContext, bankMatrix, Matrix.mul_apply]

theorem polynomial_contexts_false (bank : CircuitFamily R X O)
    (sb sd : ρ × J → O) (sy su : J × K → O)
    (p1 : OrderedMatrixAlgorithm R ρ J K) (p2 : OrderedMatrixAlgorithm R J K ρ)
    (p3 : OrderedMatrixAlgorithm R K J ρ) (p4 : OrderedMatrixAlgorithm R ρ K J) (r : ρ) (j : J) :
    (contexts bank sb sd sy su p1 p2 p3 p4).polynomial (false, (r, j)) =
      PrefixExtraction.secondContext (bankMatrix bank sd) (bankMatrix bank sy) (bankMatrix bank su) r j := by
  simp [contexts, OrderedMatrixAlgorithm.polynomial_appendUsing_new,
    PrefixExtraction.secondContext, bankMatrix, Matrix.mul_apply]

def extracted (bank : CircuitFamily R X (Bool × (ρ × J)))
    {a c : ρ → I → J → R}
    (ta : ScalarTransposeAlgorithm R I (ρ × J) (fun q i => a q.1 i q.2))
    (tc : ScalarTransposeAlgorithm R I (ρ × J) (fun q i => c q.1 i q.2)) :
    CircuitFamily R X (Bool × I) :=
  let s1 := ta.appendUsing bank (fun q => (true, q))
  let s2 := tc.appendUsing s1 (fun q => .inl (false, q))
  s2.reindexOutputs (fun q => if q.1 then .inl (.inr q.2) else .inr q.2)

theorem size_extracted (bank : CircuitFamily R X (Bool × (ρ × J)))
    {a c : ρ → I → J → R}
    (ta : ScalarTransposeAlgorithm R I (ρ × J) (fun q i => a q.1 i q.2))
    (tc : ScalarTransposeAlgorithm R I (ρ × J) (fun q i => c q.1 i q.2)) :
    (extracted bank ta tc).size = bank.size + ta.size + tc.size := by
  simp only [extracted, CircuitFamily.size_reindexOutputs, ScalarTransposeAlgorithm.size_appendUsing]

theorem polynomial_extracted_true (bank : CircuitFamily R X (Bool × (ρ × J)))
    {a c : ρ → I → J → R}
    (ta : ScalarTransposeAlgorithm R I (ρ × J) (fun q i => a q.1 i q.2))
    (tc : ScalarTransposeAlgorithm R I (ρ × J) (fun q i => c q.1 i q.2)) (i : I) :
    (extracted bank ta tc).polynomial (true, i) = ∑ r, ∑ j, a r i j • bank.polynomial (true, (r, j)) := by
  simp [extracted, ScalarTransposeAlgorithm.polynomial_appendUsing_new, Fintype.sum_prod_type]

theorem polynomial_extracted_false (bank : CircuitFamily R X (Bool × (ρ × J)))
    {a c : ρ → I → J → R}
    (ta : ScalarTransposeAlgorithm R I (ρ × J) (fun q i => a q.1 i q.2))
    (tc : ScalarTransposeAlgorithm R I (ρ × J) (fun q i => c q.1 i q.2)) (i : I) :
    (extracted bank ta tc).polynomial (false, i) = ∑ r, ∑ j, c r i j • bank.polynomial (false, (r, j)) := by
  simp [extracted, ScalarTransposeAlgorithm.polynomial_appendUsing_new, Fintype.sum_prod_type]

def leftWeighted (bank : CircuitFamily R X (Bool × I)) (x : I → X) :
    CircuitFamily R X (Bool × I) :=
  let inputBank : CircuitFamily R X I := CircuitBuilders.family (fun i => CircuitBuilders.input (x i))
  let multiply : CircuitFamily R ((Bool × I) ⊕ I) (Bool × I) :=
    CircuitBuilders.family (fun p => CircuitBuilders.mul
      (CircuitBuilders.input (.inr p.2)) (CircuitBuilders.input (.inl p)))
  (bank.combine inputBank).substitute multiply

theorem size_leftWeighted (bank : CircuitFamily R X (Bool × I)) (x : I → X) :
    (leftWeighted bank x).size = bank.size + 2 * Fintype.card I := by
  simp [leftWeighted]

theorem polynomial_leftWeighted (bank : CircuitFamily R X (Bool × I)) (x : I → X)
    (b : Bool) (i : I) :
    (leftWeighted bank x).polynomial (b, i) = FreeAlgebra.ι R (x i) * bank.polynomial (b, i) := by
  simp [leftWeighted, CircuitFamily.polynomial]

def finish (bank : CircuitFamily R X (Bool × I)) (x w : I → X) : CircuitFamily R X PUnit :=
  Assembly.finish (leftWeighted bank x) w

theorem size_finish (bank : CircuitFamily R X (Bool × I)) (x w : I → X) :
    (finish bank x w).size = bank.size + 5 * Fintype.card I := by
  rw [finish, Assembly.size_finish, size_leftWeighted]
  omega

theorem polynomial_finish (bank : CircuitFamily R X (Bool × I)) (x w : I → X) :
    (finish bank x w).polynomial PUnit.unit =
      ∑ i, FreeAlgebra.ι R (x i) * (bank.polynomial (true, i) + bank.polynomial (false, i)) *
        FreeAlgebra.ι R (w i) := by
  rw [finish, Assembly.polynomial_finish]
  simp only [polynomial_leftWeighted, mul_add]

def compile (bank : CircuitFamily R X O)
    (sb sd : ρ × J → O) (sy su : J × K → O)
    (p1 : OrderedMatrixAlgorithm R ρ J K) (p2 : OrderedMatrixAlgorithm R J K ρ)
    (p3 : OrderedMatrixAlgorithm R K J ρ) (p4 : OrderedMatrixAlgorithm R ρ K J)
    {a c : ρ → I → J → R}
    (ta : ScalarTransposeAlgorithm R I (ρ × J) (fun q i => a q.1 i q.2))
    (tc : ScalarTransposeAlgorithm R I (ρ × J) (fun q i => c q.1 i q.2))
    (x w : I → X) : CircuitFamily R X PUnit :=
  finish (extracted (contexts bank sb sd sy su p1 p2 p3 p4) ta tc) x w

theorem size_compile (bank : CircuitFamily R X O)
    (sb sd : ρ × J → O) (sy su : J × K → O)
    (p1 : OrderedMatrixAlgorithm R ρ J K) (p2 : OrderedMatrixAlgorithm R J K ρ)
    (p3 : OrderedMatrixAlgorithm R K J ρ) (p4 : OrderedMatrixAlgorithm R ρ K J)
    {a c : ρ → I → J → R}
    (ta : ScalarTransposeAlgorithm R I (ρ × J) (fun q i => a q.1 i q.2))
    (tc : ScalarTransposeAlgorithm R I (ρ × J) (fun q i => c q.1 i q.2)) (x w : I → X) :
    (compile bank sb sd sy su p1 p2 p3 p4 ta tc x w).size =
      bank.size + p1.size + p2.size + p3.size + p4.size + ta.size + tc.size + 5 * Fintype.card I := by
  rw [compile, size_finish, size_extracted, size_contexts]

theorem polynomial_compile (bank : CircuitFamily R X O)
    (sb sd : ρ × J → O) (sy su : J × K → O)
    (p1 : OrderedMatrixAlgorithm R ρ J K) (p2 : OrderedMatrixAlgorithm R J K ρ)
    (p3 : OrderedMatrixAlgorithm R K J ρ) (p4 : OrderedMatrixAlgorithm R ρ K J)
    {a c : ρ → I → J → R}
    (ta : ScalarTransposeAlgorithm R I (ρ × J) (fun q i => a q.1 i q.2))
    (tc : ScalarTransposeAlgorithm R I (ρ × J) (fun q i => c q.1 i q.2)) (x w : I → X) :
    (compile bank sb sd sy su p1 p2 p3 p4 ta tc x w).polynomial PUnit.unit =
      ∑ i, FreeAlgebra.ι R (x i) *
        PrefixExtraction.coefficients a c (bankMatrix bank sb) (bankMatrix bank sd)
          (bankMatrix bank sy) (bankMatrix bank su) i * FreeAlgebra.ι R (w i) := by
  rw [compile, polynomial_finish]
  simp only [polynomial_extracted_true, polynomial_extracted_false,
    polynomial_contexts_true, polynomial_contexts_false,
    PrefixExtraction.coefficients, PrefixExtraction.scalarTranspose]

theorem polynomial_compile_crossing [DecidableEq I] [DecidableEq J]
    (bank : CircuitFamily R X O) (sb sd : ρ × J → O) (sy su : J × K → O)
    (p1 : OrderedMatrixAlgorithm R ρ J K) (p2 : OrderedMatrixAlgorithm R J K ρ)
    (p3 : OrderedMatrixAlgorithm R K J ρ) (p4 : OrderedMatrixAlgorithm R ρ K J)
    (a b c d : ρ → I → J → R)
    (ta : ScalarTransposeAlgorithm R I (ρ × J) (fun q i => a q.1 i q.2))
    (tc : ScalarTransposeAlgorithm R I (ρ × J) (fun q i => c q.1 i q.2))
    (h : ∀ i j k l, (∑ r, a r i j * b r k l) + (∑ r, c r i l * d r k j) =
      if i = k then (if j = l then 1 else 0) else 0)
    (x v w : I → X) (y u : Matrix J K X)
    (hb : ∀ r j, bank.polynomial (sb (r, j)) = coefficientRows b (fun i => FreeAlgebra.ι R (v i)) r j)
    (hd : ∀ r j, bank.polynomial (sd (r, j)) = coefficientRows d (fun i => FreeAlgebra.ι R (v i)) r j)
    (hy : ∀ j q, bank.polynomial (sy (j, q)) = FreeAlgebra.ι R (y j q))
    (hu : ∀ j q, bank.polynomial (su (j, q)) = FreeAlgebra.ι R (u j q)) :
    (compile bank sb sd sy su p1 p2 p3 p4 ta tc x w).polynomial PUnit.unit =
      ∑ i, ∑ j, ∑ q, FreeAlgebra.ι R (x i) * FreeAlgebra.ι R (y j q) *
        FreeAlgebra.ι R (v i) * FreeAlgebra.ι R (u j q) * FreeAlgebra.ι R (w i) := by
  rw [polynomial_compile]
  have hb' : bankMatrix bank sb = coefficientRows b (fun i => FreeAlgebra.ι R (v i)) := by
    funext r j
    exact hb r j
  have hd' : bankMatrix bank sd = coefficientRows d (fun i => FreeAlgebra.ι R (v i)) := by
    funext r j
    exact hd r j
  have hy' : bankMatrix bank sy = Matrix.of (fun j q => FreeAlgebra.ι R (y j q)) := by
    funext j q
    exact hy j q
  have hu' : bankMatrix bank su = Matrix.of (fun j q => FreeAlgebra.ι R (u j q)) := by
    funext j q
    exact hu j q
  rw [hb', hd', hy', hu']
  exact PrefixExtraction.quintic_crossing a b c d h
    (fun i => FreeAlgebra.ι R (x i)) (fun i => FreeAlgebra.ι R (v i))
    (fun i => FreeAlgebra.ι R (w i)) (Matrix.of fun j q => FreeAlgebra.ι R (y j q))
    (Matrix.of fun j q => FreeAlgebra.ι R (u j q))

end QuinticCompiler

end

end Lemmata.FockCircuits
