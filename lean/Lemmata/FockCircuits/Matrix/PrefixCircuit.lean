module

public import Lemmata.FockCircuits.Matrix.BilinearPower
public import Lemmata.FockCircuits.Matrix.CircuitWithin

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix

open scoped BigOperators

noncomputable section

universe u

variable {K : Type u} [CommSemiring K]
variable {L M N : Type*} [Fintype M]

/-- Every intermediate value is right-only or has one left prefix. -/
def PrefixSafe (p : OrderedMatrixAlgorithm K L M N) : Prop :=
  ∀ (D : Type u) [Semiring D] [Algebra K D] (Q : Subalgebra K D) (V : Submodule K D),
    (∀ u ∈ V, ∀ v ∈ Q, u * v ∈ V) →
    ∀ left : L × M → D, ∀ right : M × N → D,
    (∀ i, left i ∈ V) → (∀ i, right i ∈ Q) →
    CircuitWithin p.circuit (Sum.elim left right) (Q.toSubmodule ⊔ V)

namespace BilinearScheme

variable {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]
variable [Fintype A] [Fintype B] [Fintype C]
variable [Fintype L] [Fintype N]

theorem blockStep_prefixSafe (s : BilinearScheme K A B C)
    (p : OrderedMatrixAlgorithm K L M N) (hp : PrefixSafe p) : PrefixSafe (s.blockStep p) := by
  intro D _ _ Q V hmul left right hleft hright
  let x : MatrixInput (A × L) (B × M) (C × N) → D := Sum.elim left right
  let S : Submodule K D := Q.toSubmodule ⊔ V
  have hscalar (a : K) : algebraMap K D a ∈ S :=
    (le_sup_left : Q.toSubmodule ≤ S) (Q.algebraMap_mem a)
  have hleftS (i : (A × L) × (B × M)) : x (.inl i) ∈ S :=
    (le_sup_right : V ≤ S) (hleft i)
  have hrightS (i : (B × M) × (C × N)) : x (.inr i) ∈ S :=
    (le_sup_left : Q.toSubmodule ≤ S) (hright i)
  have hbank : CircuitWithin (inputFamily s) x S := by
    unfold inputFamily
    apply CircuitWithin.reindexOutputs
    apply CircuitWithin.combine
    · exact CircuitBuilders.within_linearFamily x S hscalar _ _ (fun q i => hleftS _)
    · exact CircuitBuilders.within_linearFamily x S hscalar _ _ (fun q i => hrightS _)
  have hLB (t : Fin s.rank) (l : L) (m : M) : leftBlock s x t l m ∈ V := by
    apply V.sum_mem
    intro i hi
    exact V.smul_mem _ (hleft _)
  have hRB (t : Fin s.rank) (m : M) (n : N) : rightBlock s x t m n ∈ Q := by
    apply Q.toSubmodule.sum_mem
    intro i hi
    exact Q.toSubmodule.smul_mem _ (hright _)
  have hcopies : CircuitWithin (CircuitBuilders.copies s.rank p.circuit)
      ((inputFamily s).eval (algebraMap K D) x) S := by
    apply CircuitBuilders.within_copies
    intro t
    have heq : (fun i => (inputFamily s).eval (algebraMap K D) x (t, i)) =
        Sum.elim (fun i => leftBlock s x t i.1 i.2)
          (fun i => rightBlock s x t i.1 i.2) := by
      funext i
      exact eval_inputFamily s x t i
    rw [heq]
    exact hp D Q V hmul _ _ (fun i => hLB t i.1 i.2) (fun i => hRB t i.1 i.2)
  have hproducts : CircuitWithin (products s p) x S := hbank.substitute hcopies
  have hproductV (t : Fin s.rank) (l : L) (n : N) :
      (products s p).eval (algebraMap K D) x (t, (l, n)) ∈ V := by
    rw [eval_products]
    apply V.sum_mem
    intro m hm
    exact hmul _ (hLB t l m) _ (hRB t m n)
  have hout : CircuitWithin (outputFamily s)
      ((products s p).eval (algebraMap K D) x) S := by
    apply CircuitBuilders.within_linearFamily _ S hscalar
    intro o t
    exact (le_sup_right : V ≤ S) (hproductV t o.1.2 o.2.2)
  exact hproducts.substitute hout

theorem unitAlgorithm_prefixSafe : PrefixSafe (unitAlgorithm (K := K)) := by
  intro D _ _ Q V hmul left right hleft hright
  let S : Submodule K D := Q.toSubmodule ⊔ V
  apply CircuitWithin.reindexOutputs
  apply CircuitBuilders.within_mul
  · apply CircuitBuilders.within_input
    exact (le_sup_right : V ≤ S) (hleft _)
  · apply CircuitBuilders.within_input
    exact (le_sup_left : Q.toSubmodule ≤ S) (hright _)
  · simp only [CircuitBuilders.eval_input, Sum.elim_inl, Sum.elim_inr]
    exact (le_sup_right : V ≤ S) (hmul _ (hleft _) _ (hright _))

theorem recursive_prefixSafe {A B C : Type} [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Fintype A] [Fintype B] [Fintype C] (s : BilinearScheme K A B C) (n : ℕ) :
    PrefixSafe (s.recursive n) := by
  induction n with
  | zero => exact unitAlgorithm_prefixSafe
  | succ n ih => exact blockStep_prefixSafe s (s.recursive n) ih

end BilinearScheme

end

end Lemmata.FockCircuits.Matrix
