module

public import Lemmata.FockCircuits.Matrix.BilinearCircuit

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.BilinearScheme

open scoped BigOperators

noncomputable section

variable {K A B C L M N : Type*} [CommSemiring K]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]
variable [Fintype A] [Fintype B] [Fintype C]
variable [Fintype L] [Fintype M] [Fintype N]

abbrev MatrixInput (L M N : Type*) := (L × M) ⊕ (M × N)

def inputFamily (s : BilinearScheme K A B C) :
    CircuitFamily K (MatrixInput (A × L) (B × M) (C × N))
      (Fin s.rank × MatrixInput L M N) :=
  let lf : CircuitFamily K (MatrixInput (A × L) (B × M) (C × N))
      (Fin s.rank × (L × M)) :=
    CircuitBuilders.linearFamily (fun q i => s.left q.1 i)
      (fun q i => Sum.inl ((i.1, q.2.1), (i.2, q.2.2)))
  let rf : CircuitFamily K (MatrixInput (A × L) (B × M) (C × N))
      (Fin s.rank × (M × N)) :=
    CircuitBuilders.linearFamily (fun q j => s.right q.1 j)
      (fun q j => Sum.inr ((j.1, q.2.1), (j.2, q.2.2)))
  (lf.combine rf).reindexOutputs (fun q => match q.2 with
    | .inl p => .inl (q.1, p)
    | .inr p => .inr (q.1, p))

theorem size_inputFamily (s : BilinearScheme K A B C) :
    (inputFamily (L := L) (M := M) (N := N) s).size =
      2 * s.rank * (Fintype.card A * Fintype.card B * Fintype.card L * Fintype.card M +
        Fintype.card B * Fintype.card C * Fintype.card M * Fintype.card N) := by
  simp only [inputFamily, CircuitFamily.size_reindexOutputs, CircuitFamily.size_combine,
    CircuitBuilders.size_linearFamily, Fintype.card_prod, Fintype.card_fin]
  ring

def leftBlock {D : Type*} [Semiring D] [Algebra K D]
    (s : BilinearScheme K A B C) (x : MatrixInput (A × L) (B × M) (C × N) → D)
    (t : Fin s.rank) (l : L) (m : M) : D :=
  ∑ i : A × B, s.left t i • x (.inl ((i.1, l), (i.2, m)))

def rightBlock {D : Type*} [Semiring D] [Algebra K D]
    (s : BilinearScheme K A B C) (x : MatrixInput (A × L) (B × M) (C × N) → D)
    (t : Fin s.rank) (m : M) (n : N) : D :=
  ∑ j : B × C, s.right t j • x (.inr ((j.1, m), (j.2, n)))

theorem eval_inputFamily {D : Type*} [Semiring D] [Algebra K D]
    (s : BilinearScheme K A B C) (x : MatrixInput (A × L) (B × M) (C × N) → D)
    (t : Fin s.rank) (p : MatrixInput L M N) :
    (inputFamily s).eval (algebraMap K D) x (t, p) =
      Sum.elim (fun p => leftBlock s x t p.1 p.2)
        (fun p => rightBlock s x t p.1 p.2) p := by
  cases p with
  | inl p => simp [inputFamily, CircuitBuilders.eval_linearFamily, leftBlock]
  | inr p => simp [inputFamily, CircuitBuilders.eval_linearFamily, rightBlock]

def products (s : BilinearScheme K A B C) (p : OrderedMatrixAlgorithm K L M N) :
    CircuitFamily K (MatrixInput (A × L) (B × M) (C × N)) (Fin s.rank × (L × N)) :=
  (inputFamily s).substitute (CircuitBuilders.copies s.rank p.circuit)

theorem eval_products {D : Type*} [Semiring D] [Algebra K D]
    (s : BilinearScheme K A B C) (p : OrderedMatrixAlgorithm K L M N)
    (x : MatrixInput (A × L) (B × M) (C × N) → D) (t : Fin s.rank) (l : L) (n : N) :
    (products s p).eval (algebraMap K D) x (t, (l, n)) =
      ∑ m, leftBlock s x t l m * rightBlock s x t m n := by
  rw [products, CircuitFamily.eval_substitute, CircuitBuilders.eval_copies]
  have hx : (fun i => (inputFamily s).eval (algebraMap K D) x (t, i)) =
      Sum.elim (fun p => leftBlock s x t p.1 p.2)
        (fun p => rightBlock s x t p.1 p.2) := by
    funext i
    exact eval_inputFamily s x t i
  rw [hx]
  simpa only [Matrix.mul_apply, Matrix.of_apply] using
    p.eval_correct (Matrix.of (leftBlock s x t)) (Matrix.of (rightBlock s x t)) l n

def outputFamily (s : BilinearScheme K A B C) :
    CircuitFamily K (Fin s.rank × (L × N)) ((A × L) × (C × N)) :=
  CircuitBuilders.linearFamily (fun o t => s.output t (o.2.1, o.1.1))
    (fun o t => (t, (o.1.2, o.2.2)))

theorem size_outputFamily (s : BilinearScheme K A B C) :
    (outputFamily (L := L) (N := N) s).size =
      2 * s.rank * Fintype.card A * Fintype.card C * Fintype.card L * Fintype.card N := by
  simp only [outputFamily, CircuitBuilders.size_linearFamily, Fintype.card_fin,
    Fintype.card_prod]
  ring

def blockCircuit (s : BilinearScheme K A B C) (p : OrderedMatrixAlgorithm K L M N) :
    CircuitFamily K (MatrixInput (A × L) (B × M) (C × N)) ((A × L) × (C × N)) :=
  (products s p).substitute (outputFamily s)

theorem size_blockCircuit (s : BilinearScheme K A B C) (p : OrderedMatrixAlgorithm K L M N) :
    (blockCircuit s p).size = s.rank * p.size + 2 * s.rank *
      (Fintype.card A * Fintype.card B * Fintype.card L * Fintype.card M +
        Fintype.card B * Fintype.card C * Fintype.card M * Fintype.card N +
        Fintype.card A * Fintype.card C * Fintype.card L * Fintype.card N) := by
  rw [blockCircuit, CircuitFamily.size_substitute, products, CircuitFamily.size_substitute,
    size_inputFamily, CircuitBuilders.size_copies, size_outputFamily]
  simp only [OrderedMatrixAlgorithm.size]
  ring

theorem eval_blockCircuit {D : Type*} [Semiring D] [Algebra K D]
    (s : BilinearScheme K A B C) (p : OrderedMatrixAlgorithm K L M N)
    (x : MatrixInput (A × L) (B × M) (C × N) → D) (i : A) (k : C) (l : L) (n : N) :
    (blockCircuit s p).eval (algebraMap K D) x ((i, l), (k, n)) =
      ∑ j : B × M, x (.inl ((i, l), j)) * x (.inr (j, (k, n))) := by
  rw [blockCircuit, CircuitFamily.eval_substitute, outputFamily,
    CircuitBuilders.eval_linearFamily]
  simp_rw [eval_products, Finset.smul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ m : M, ∑ j : B, x (.inl ((i, l), (j, m))) *
        x (.inr ((j, m), (k, n))) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact s.ordered_identity (fun a => x (.inl ((a.1, l), (a.2, m))))
        (fun b => x (.inr ((b.1, m), (b.2, n)))) i k
    _ = _ := by rw [Finset.sum_comm, Fintype.sum_prod_type]

/-- One recursive step uses only scalar linear maps and ordered recursive products. -/
def blockStep (s : BilinearScheme K A B C) (p : OrderedMatrixAlgorithm K L M N) :
    OrderedMatrixAlgorithm K (A × L) (B × M) (C × N) where
  circuit := blockCircuit s p
  correct := fun i k => eval_blockCircuit s p (FreeAlgebra.ι K) i.1 k.1 i.2 k.2

theorem size_blockStep (s : BilinearScheme K A B C) (p : OrderedMatrixAlgorithm K L M N) :
    (s.blockStep p).size = s.rank * p.size + 2 * s.rank *
      (Fintype.card A * Fintype.card B * Fintype.card L * Fintype.card M +
        Fintype.card B * Fintype.card C * Fintype.card M * Fintype.card N +
        Fintype.card A * Fintype.card C * Fintype.card L * Fintype.card N) :=
  size_blockCircuit s p

end

end Lemmata.FockCircuits.Matrix.BilinearScheme
