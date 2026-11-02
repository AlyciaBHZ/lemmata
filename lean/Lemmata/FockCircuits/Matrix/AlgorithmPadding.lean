module

public import Lemmata.FockCircuits.Matrix.PrefixCircuit

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix

noncomputable section

variable {K X Y : Type*} [CommSemiring K]

def paddingBank [Fintype Y] (e : X ↪ Y) : CircuitFamily K X Y :=
  CircuitBuilders.family (Function.extend e (fun x => CircuitBuilders.input x)
    (fun _ => CircuitBuilders.scalar 0))

theorem size_paddingBank [Fintype Y] (e : X ↪ Y) : (paddingBank (K := K) e).size = 0 := by
  classical
  rw [paddingBank, CircuitBuilders.size_family]
  apply Finset.sum_eq_zero
  intro y hy
  by_cases he : ∃ x, e x = y
  · obtain ⟨x, rfl⟩ := he
    rw [e.injective.extend_apply]
    rfl
  · rw [Function.extend_apply' _ _ _ he]
    rfl

theorem eval_paddingBank [Fintype Y] {D : Type*} [Semiring D] [Algebra K D]
    (e : X ↪ Y) (x : X → D) :
    (paddingBank (K := K) e).eval (algebraMap K D) x = Function.extend e x (fun _ => 0) := by
  classical
  funext y
  rw [paddingBank, CircuitBuilders.eval_family]
  by_cases he : ∃ z, e z = y
  · obtain ⟨z, rfl⟩ := he
    rw [e.injective.extend_apply, e.injective.extend_apply]
    rfl
  · rw [Function.extend_apply' _ _ _ he, Function.extend_apply' _ _ _ he]
    simp only [CircuitBuilders.eval_scalar, map_zero]

theorem within_paddingBank [Fintype Y] {D : Type*} [Semiring D] [Algebra K D]
    (e : X ↪ Y) (x : X → D) (S : Submodule K D) (hx : ∀ i, x i ∈ S) :
    CircuitWithin (paddingBank (K := K) e) x S := by
  classical
  unfold paddingBank CircuitBuilders.family
  apply CircuitWithin.reindexOutputs
  apply CircuitBuilders.within_parallelFin
  intro j
  let y := (Fintype.equivFin Y).symm j
  by_cases he : ∃ z, e z = y
  · obtain ⟨z, hz⟩ := he
    change CircuitWithin (Function.extend e (fun z => CircuitBuilders.input z)
      (fun _ => CircuitBuilders.scalar 0) y) x S
    rw [← hz, e.injective.extend_apply]
    exact CircuitBuilders.within_input z x S (hx z)
  · change CircuitWithin (Function.extend e (fun z => CircuitBuilders.input z)
      (fun _ => CircuitBuilders.scalar 0) y) x S
    rw [Function.extend_apply' _ _ _ he]
    exact CircuitBuilders.within_scalar 0 x S (by simpa only [map_zero] using S.zero_mem)

namespace OrderedMatrixAlgorithm

open scoped BigOperators

variable {L M N L' M' N' : Type*}
variable [Fintype L] [Fintype M] [Fintype N]
variable [Fintype L'] [Fintype M'] [Fintype N']

def inputEmbedding (eL : L' ↪ L) (eM : M' ↪ M) (eN : N' ↪ N) :
    ((L' × M') ⊕ (M' × N')) ↪ ((L × M) ⊕ (M × N)) :=
  (eL.prodMap eM).sumMap (eM.prodMap eN)

theorem padded_product_sum {D : Type*} [Semiring D] [Algebra K D]
    (eL : L' ↪ L) (eM : M' ↪ M) (eN : N' ↪ N)
    (x : ((L' × M') ⊕ (M' × N')) → D) (l : L') (n : N') :
    (∑ m : M, Function.extend (inputEmbedding eL eM eN) x (fun _ => 0) (.inl (eL l, m)) *
        Function.extend (inputEmbedding eL eM eN) x (fun _ => 0) (.inr (m, eN n))) =
      ∑ m : M', x (.inl (l, m)) * x (.inr (m, n)) := by
  classical
  symm
  apply Fintype.sum_of_injective eM eM.injective
  · intro m hm
    have hout : ¬ ∃ z, inputEmbedding eL eM eN z = Sum.inl (eL l, m) := by
      rintro ⟨z, hz⟩
      cases z with
      | inl z =>
          change Sum.inl (eL z.1, eM z.2) = Sum.inl (eL l, m) at hz
          exact hm ⟨z.2, congrArg Prod.snd (Sum.inl.inj hz)⟩
      | inr z => cases hz
    rw [Function.extend_apply' _ _ _ hout, zero_mul]
  · intro m
    have hleft : Sum.inl (eL l, eM m) = inputEmbedding eL eM eN (.inl (l, m)) := rfl
    have hright : Sum.inr (eM m, eN n) = inputEmbedding eL eM eN (.inr (m, n)) := rfl
    rw [hleft, hright, (inputEmbedding eL eM eN).injective.extend_apply,
      (inputEmbedding eL eM eN).injective.extend_apply]

def paddedCircuit (p : Lemmata.FockCircuits.OrderedMatrixAlgorithm K L M N)
    (eL : L' ↪ L) (eM : M' ↪ M) (eN : N' ↪ N) :
    CircuitFamily K ((L' × M') ⊕ (M' × N')) (L' × N') :=
  ((paddingBank (inputEmbedding eL eM eN)).substitute p.circuit).reindexOutputs
    (fun o => (eL o.1, eN o.2))

theorem eval_paddedCircuit {D : Type*} [Semiring D] [Algebra K D]
    (p : Lemmata.FockCircuits.OrderedMatrixAlgorithm K L M N)
    (eL : L' ↪ L) (eM : M' ↪ M) (eN : N' ↪ N)
    (x : ((L' × M') ⊕ (M' × N')) → D) (l : L') (n : N') :
    (paddedCircuit p eL eM eN).eval (algebraMap K D) x (l, n) =
      ∑ m, x (.inl (l, m)) * x (.inr (m, n)) := by
  let old := Function.extend (inputEmbedding eL eM eN) x (fun _ => 0)
  rw [paddedCircuit, CircuitFamily.eval_reindexOutputs, CircuitFamily.eval_substitute,
    eval_paddingBank]
  have heq : old = Sum.elim (fun i => old (.inl i)) (fun i => old (.inr i)) := by
    funext i
    cases i <;> rfl
  change p.circuit.eval (algebraMap K D) old (eL l, eN n) = _
  rw [heq]
  have hp := p.eval_correct (Matrix.of (fun l m => old (.inl (l, m))))
    (Matrix.of (fun m n => old (.inr (m, n)))) (eL l) (eN n)
  change p.circuit.eval (algebraMap K D)
    (Sum.elim (fun i => old (.inl i)) (fun i => old (.inr i))) (eL l, eN n) =
    ∑ m : M, old (.inl (eL l, m)) * old (.inr (m, eN n)) at hp
  exact hp.trans (padded_product_sum (K := K) eL eM eN x l n)

def pad (p : Lemmata.FockCircuits.OrderedMatrixAlgorithm K L M N)
    (eL : L' ↪ L) (eM : M' ↪ M) (eN : N' ↪ N) :
    Lemmata.FockCircuits.OrderedMatrixAlgorithm K L' M' N' where
  circuit := paddedCircuit p eL eM eN
  correct := fun l n => eval_paddedCircuit p eL eM eN (FreeAlgebra.ι K) l n

theorem size_pad (p : Lemmata.FockCircuits.OrderedMatrixAlgorithm K L M N)
    (eL : L' ↪ L) (eM : M' ↪ M) (eN : N' ↪ N) : (pad p eL eM eN).size = p.size := by
  simp only [pad, Lemmata.FockCircuits.OrderedMatrixAlgorithm.size, paddedCircuit,
    CircuitFamily.size_reindexOutputs, CircuitFamily.size_substitute, size_paddingBank, zero_add]

theorem pad_prefixSafe (p : Lemmata.FockCircuits.OrderedMatrixAlgorithm K L M N)
    (hp : PrefixSafe p) (eL : L' ↪ L) (eM : M' ↪ M) (eN : N' ↪ N) :
    PrefixSafe (pad p eL eM eN) := by
  classical
  intro D _ _ Q V hmul left right hleft hright
  let x := Sum.elim left right
  let e := inputEmbedding eL eM eN
  let old := Function.extend e x (fun _ => 0)
  let S : Submodule K D := Q.toSubmodule ⊔ V
  have holdL (i : L × M) : old (.inl i) ∈ V := by
    by_cases he : ∃ z, e z = Sum.inl i
    · obtain ⟨z, hz⟩ := he
      cases z with
      | inl z =>
          change Function.extend e x (fun _ => 0) (.inl i) ∈ V
          rw [← hz, e.injective.extend_apply]
          exact hleft z
      | inr z => cases hz
    · change Function.extend e x (fun _ => 0) (.inl i) ∈ V
      rw [Function.extend_apply' _ _ _ he]
      exact V.zero_mem
  have holdR (i : M × N) : old (.inr i) ∈ Q := by
    by_cases he : ∃ z, e z = Sum.inr i
    · obtain ⟨z, hz⟩ := he
      cases z with
      | inl z => cases hz
      | inr z =>
          change Function.extend e x (fun _ => 0) (.inr i) ∈ Q
          rw [← hz, e.injective.extend_apply]
          exact hright z
    · change Function.extend e x (fun _ => 0) (.inr i) ∈ Q
      rw [Function.extend_apply' _ _ _ he]
      exact Q.zero_mem
  apply CircuitWithin.reindexOutputs
  apply CircuitWithin.substitute
  · apply within_paddingBank e x S
    intro i
    cases i with
    | inl i => exact (le_sup_right : V ≤ S) (hleft i)
    | inr i => exact (le_sup_left : Q.toSubmodule ≤ S) (hright i)
  · rw [eval_paddingBank]
    have heq : old = Sum.elim (fun i => old (.inl i)) (fun i => old (.inr i)) := by
      funext i
      cases i <;> rfl
    change CircuitWithin p.circuit old S
    rw [heq]
    exact hp D Q V hmul _ _ holdL holdR

end OrderedMatrixAlgorithm

end

end Lemmata.FockCircuits.Matrix
