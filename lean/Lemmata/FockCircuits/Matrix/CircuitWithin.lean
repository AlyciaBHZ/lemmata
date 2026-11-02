module

public import Lemmata.FockCircuits.Matrix.CircuitBuilders

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix

variable {K X O D : Type*} [CommSemiring K] [Semiring D] [Algebra K D]

def CircuitWithin (c : CircuitFamily K X O) (x : X → D) (S : Submodule K D) : Prop :=
  ∀ i, c.circuit.eval (algebraMap K D) x i ∈ S

namespace CircuitWithin

theorem output {c : CircuitFamily K X O} {x : X → D} {S : Submodule K D}
    (h : CircuitWithin c x S) (o : O) : c.eval (algebraMap K D) x o ∈ S :=
  h (c.output o)

theorem reindexOutputs {P : Type*} {c : CircuitFamily K X O} {x : X → D}
    {S : Submodule K D} (h : CircuitWithin c x S) (f : P → O) :
    CircuitWithin (c.reindexOutputs f) x S := h

theorem combine {P : Type*} {c : CircuitFamily K X O} {d : CircuitFamily K X P}
    {x : X → D} {S : Submodule K D} (hc : CircuitWithin c x S)
    (hd : CircuitWithin d x S) : CircuitWithin (c.combine d) x S := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    change (c.circuit.append d.circuit).eval (algebraMap K D) x (Fin.castAdd _ j) ∈ S
    rw [Circuit.eval_append_left]
    exact hc j
  · intro j
    change ((c.circuit.append d.circuit).eval (algebraMap K D) x ∘
      Fin.natAdd c.nodeCount) j ∈ S
    rw [Circuit.eval_append_right]
    exact hd j

theorem substitute {Y : Type*} {c : CircuitFamily K Y X} {d : CircuitFamily K X O}
    {x : Y → D} {S : Submodule K D} (hc : CircuitWithin c x S)
    (hd : CircuitWithin d (c.eval (algebraMap K D) x) S) :
    CircuitWithin (c.substitute d) x S := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    change (c.circuit.substitute c.output d.circuit).eval (algebraMap K D) x
      (Fin.castAdd _ j) ∈ S
    rw [Circuit.eval_substitute_left]
    exact hc j
  · intro j
    change ((c.circuit.substitute c.output d.circuit).eval (algebraMap K D) x ∘
      Fin.natAdd c.nodeCount) j ∈ S
    rw [Circuit.eval_substitute_right]
    exact hd j

theorem mapInputs {Y : Type*} {c : CircuitFamily K X O} {x : Y → D}
    {S : Submodule K D} (f : X → Y) (h : CircuitWithin c (x ∘ f) S) :
    CircuitWithin (c.mapInputs f) x S := by
  intro i
  change (c.circuit.mapInputs f).eval (algebraMap K D) x i ∈ S
  rw [Circuit.eval_mapInputs]
  exact h i

end CircuitWithin

namespace CircuitBuilders

theorem within_scalar (r : K) (x : X → D) (S : Submodule K D)
    (hr : algebraMap K D r ∈ S) : CircuitWithin (scalar r) x S := by
  intro i
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact hr

theorem within_input (i : X) (x : X → D) (S : Submodule K D)
    (hi : x i ∈ S) : CircuitWithin (input i) x S := by
  intro j
  change Fin 1 at j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact hi

theorem within_add {a b : CircuitFamily K X Unit} {x : X → D} {S : Submodule K D}
    (ha : CircuitWithin a x S) (hb : CircuitWithin b x S) : CircuitWithin (add a b) x S := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change (add a b).eval (algebraMap K D) x () ∈ S
    rw [eval_add]
    exact S.add_mem (ha.output ()) (hb.output ())
  · change ((a.combine b).circuit.snoc _).eval (algebraMap K D) x j.castSucc ∈ S
    rw [Circuit.eval_snoc_castSucc]
    exact ha.combine hb j

theorem within_mul {a b : CircuitFamily K X Unit} {x : X → D} {S : Submodule K D}
    (ha : CircuitWithin a x S) (hb : CircuitWithin b x S)
    (hm : a.eval (algebraMap K D) x () * b.eval (algebraMap K D) x () ∈ S) :
    CircuitWithin (mul a b) x S := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change (mul a b).eval (algebraMap K D) x () ∈ S
    rwa [eval_mul]
  · change ((a.combine b).circuit.snoc _).eval (algebraMap K D) x j.castSucc ∈ S
    rw [Circuit.eval_snoc_castSucc]
    exact ha.combine hb j

theorem within_parallelFin (x : X → D) (S : Submodule K D) (n : ℕ)
    (f : Fin n → CircuitFamily K X O) (hf : ∀ i, CircuitWithin (f i) x S) :
    CircuitWithin (parallelFin n f) x S := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      exact ((hf 0).combine (ih _ (fun i => hf i.succ))).reindexOutputs _

theorem within_linearFin (x : X → D) (S : Submodule K D)
    (hscalar : ∀ r : K, algebraMap K D r ∈ S) (n : ℕ)
    (a : Fin n → K) (wire : Fin n → X) (hwire : ∀ i, x (wire i) ∈ S) :
    CircuitWithin (linearFin n a wire) x S := by
  induction n with
  | zero => exact within_scalar 0 x S (hscalar 0)
  | succ n ih =>
      apply within_add
      · apply within_mul (within_scalar _ x S (hscalar _)) (within_input _ x S (hwire 0))
        simpa only [eval_scalar, eval_input, ← Algebra.smul_def] using S.smul_mem (a 0) (hwire 0)
      · exact ih _ _ (fun i => hwire i.succ)

theorem within_linear {J : Type*} [Fintype J] (x : X → D) (S : Submodule K D)
    (hscalar : ∀ r : K, algebraMap K D r ∈ S) (a : J → K) (wire : J → X)
    (hwire : ∀ i, x (wire i) ∈ S) : CircuitWithin (linear a wire) x S :=
  within_linearFin x S hscalar _ _ _ (fun i => hwire _)

theorem within_linearFamily {J : Type*} [Fintype J] [Fintype O]
    (x : X → D) (S : Submodule K D) (hscalar : ∀ r : K, algebraMap K D r ∈ S)
    (a : O → J → K) (wire : O → J → X) (hwire : ∀ o i, x (wire o i) ∈ S) :
    CircuitWithin (linearFamily a wire) x S :=
  (within_parallelFin x S _ _ (fun o => within_linear x S hscalar _ _
    (hwire ((Fintype.equivFin O).symm o)))).reindexOutputs _

theorem within_copies (r : ℕ) (p : CircuitFamily K X O)
    (x : Fin r × X → D) (S : Submodule K D)
    (h : ∀ q, CircuitWithin p (fun i => x (q, i)) S) :
    CircuitWithin (copies r p) x S :=
  within_parallelFin x S r _ (fun q => CircuitWithin.mapInputs _ (h q))

end CircuitBuilders

end Lemmata.FockCircuits.Matrix
