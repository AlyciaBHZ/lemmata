module

public import Lemmata.FockCircuits.QuinticCompiler
public import Lemmata.FockCircuits.SparseCircuit

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.ScalarAdjoints

open scoped BigOperators
open Lemmata.FockCircuits.Matrix

noncomputable section

variable {R : Type*} [CommSemiring R]

def inputs (D : Type*) [Fintype D] : CircuitFamily R D D :=
  CircuitBuilders.family (fun i => CircuitBuilders.input i)

@[simp] theorem size_inputs (D : Type*) [Fintype D] : (inputs (R := R) D).size = 0 := by
  simp [inputs]

@[simp] theorem eval_inputs {D A : Type*} [Fintype D] [Add A] [Mul A]
    (s : R → A) (x : D → A) (i : D) : (inputs D).eval s x i = x i := by
  simp [inputs]

def scatterMatrix {D : Type*} [DecidableEq D] (target : D → D) (a : D → R) : D → D → R :=
  fun i j => (if j = i then 1 else 0) + if i = target j then a j else 0

def scatterTranspose {D : Type*} [Fintype D] [DecidableEq D]
    (target : D → D) (a : D → R) : ScalarTransposeAlgorithm R D D (scatterMatrix target a) :=
  ScalarTransposeAlgorithm.ofAdjoint
    (SparseCircuit.scatter (inputs D) target a) (SparseCircuit.gather (inputs D) target a)
    (by
      intro i
      change (SparseCircuit.scatter (inputs D) target a).eval
        (algebraMap R (FreeAlgebra R D)) (FreeAlgebra.ι R) i = _
      rw [SparseCircuit.scatter_matrix (inputs D) target a (FreeAlgebra.ι R)
        (scatterMatrix target a) (fun _ _ => rfl)]
      simp only [eval_inputs]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Algebra.smul_def]
      exact (Algebra.commutes (scatterMatrix target a i j) (FreeAlgebra.ι R j)).symm)
    (by
      intro x y
      simpa only [eval_inputs] using
        SparseCircuit.scatter_gather_adjoint (inputs D) (inputs D) target a x y)

theorem size_scatterTranspose {D : Type*} [Fintype D] [DecidableEq D]
    (target : D → D) (a : D → R) :
    (scatterTranspose target a).size = 2 * Fintype.card D := by
  change (SparseCircuit.gather (inputs D) target a).size = _
  rw [SparseCircuit.size_gather, size_inputs, zero_add]

def diagonalCircuit {D : Type*} [Fintype D] (a : D → R) : CircuitFamily R D D :=
  CircuitBuilders.family (fun i => CircuitBuilders.mul
    (CircuitBuilders.scalar (a i)) (CircuitBuilders.input i))

def diagonalTranspose {D : Type*} [Fintype D] [DecidableEq D] (a : D → R) :
    ScalarTransposeAlgorithm R D D (fun o i => if i = o then a o else 0) where
  circuit := diagonalCircuit a
  correct := by
    intro i
    simp [diagonalCircuit, CircuitFamily.polynomial, Algebra.smul_def, apply_ite, ite_mul]

theorem size_diagonalTranspose {D : Type*} [Fintype D] [DecidableEq D] (a : D → R) :
    (diagonalTranspose a).size = Fintype.card D := by
  simp [diagonalTranspose, ScalarTransposeAlgorithm.size, diagonalCircuit]

def injectionTranspose {I O : Type*} [Fintype I] [Fintype O] [DecidableEq O]
    (index : I ↪ O) : ScalarTransposeAlgorithm R I O (fun o i => if index i = o then 1 else 0) where
  circuit := CircuitBuilders.family (fun i => CircuitBuilders.input (index i))
  correct := by
    intro i
    simp [CircuitFamily.polynomial, ite_smul]

theorem size_injectionTranspose {I O : Type*} [Fintype I] [Fintype O] [DecidableEq O]
    (index : I ↪ O) : (injectionTranspose (R := R) index).size = 0 := by
  simp [injectionTranspose, ScalarTransposeAlgorithm.size]

def compose {I O P : Type*} [Fintype I] [Fintype O] [Fintype P]
    {a : O → I → R} {b : P → O → R}
    (ta : ScalarTransposeAlgorithm R I O a) (tb : ScalarTransposeAlgorithm R O P b) :
    ScalarTransposeAlgorithm R I P (fun p i => ∑ o, a o i * b p o) where
  circuit := tb.circuit.substitute ta.circuit
  correct := by
    intro i
    rw [CircuitFamily.polynomial_substitute, ta.correct]
    simp only [map_sum, map_smul, FreeAlgebra.lift_ι_apply, tb.correct,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]

theorem size_compose {I O P : Type*} [Fintype I] [Fintype O] [Fintype P]
    {a : O → I → R} {b : P → O → R}
    (ta : ScalarTransposeAlgorithm R I O a) (tb : ScalarTransposeAlgorithm R O P b) :
    (compose ta tb).size = tb.size + ta.size :=
  CircuitFamily.size_substitute tb.circuit ta.circuit

end

end Lemmata.FockCircuits.ScalarAdjoints
