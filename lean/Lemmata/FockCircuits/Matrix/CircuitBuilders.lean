module

public import Lemmata.FockCircuits.Circuit
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.CircuitBuilders

open scoped BigOperators

variable {R X O : Type*}

def scalar (r : R) : CircuitFamily R X Unit :=
  ⟨1, .snoc .nil (.scalar r), fun _ => 0⟩

def input (x : X) : CircuitFamily R X Unit :=
  ⟨1, .snoc .nil (.input x), fun _ => 0⟩

def add (a b : CircuitFamily R X Unit) : CircuitFamily R X Unit :=
  let bank := a.combine b
  ⟨bank.nodeCount + 1,
    bank.circuit.snoc (.add (bank.output (.inl ())) (bank.output (.inr ()))),
    fun _ => Fin.last bank.nodeCount⟩

def mul (a b : CircuitFamily R X Unit) : CircuitFamily R X Unit :=
  let bank := a.combine b
  ⟨bank.nodeCount + 1,
    bank.circuit.snoc (.mul (bank.output (.inl ())) (bank.output (.inr ()))),
    fun _ => Fin.last bank.nodeCount⟩

@[simp] theorem size_scalar (r : R) : (scalar (X := X) r).size = 0 := rfl
@[simp] theorem size_input (x : X) : (input (R := R) x).size = 0 := rfl

@[simp] theorem size_add (a b : CircuitFamily R X Unit) :
    (add a b).size = a.size + b.size + 1 := by
  simp only [add, CircuitFamily.size, Circuit.size_snoc, Gate.cost,
    CircuitFamily.combine, Circuit.size_append]

@[simp] theorem size_mul (a b : CircuitFamily R X Unit) :
    (mul a b).size = a.size + b.size + 1 := by
  simp only [mul, CircuitFamily.size, Circuit.size_snoc, Gate.cost,
    CircuitFamily.combine, Circuit.size_append]

@[simp] theorem eval_scalar {A : Type*} [Add A] [Mul A]
    (s : R → A) (x : X → A) (r : R) : (scalar r).eval s x () = s r := rfl

@[simp] theorem eval_input {A : Type*} [Add A] [Mul A]
    (s : R → A) (x : X → A) (i : X) : (input i).eval s x () = x i := rfl

@[simp] theorem eval_add {A : Type*} [Add A] [Mul A]
    (s : R → A) (x : X → A) (a b : CircuitFamily R X Unit) :
    (add a b).eval s x () = a.eval s x () + b.eval s x () := by
  simp only [add, CircuitFamily.eval, Function.comp_apply,
    Circuit.eval_snoc_last, Gate.eval]
  exact congrArg₂ (· + ·) (CircuitFamily.eval_combine_inl a b s x ())
    (CircuitFamily.eval_combine_inr a b s x ())

@[simp] theorem eval_mul {A : Type*} [Add A] [Mul A]
    (s : R → A) (x : X → A) (a b : CircuitFamily R X Unit) :
    (mul a b).eval s x () = a.eval s x () * b.eval s x () := by
  simp only [mul, CircuitFamily.eval, Function.comp_apply,
    Circuit.eval_snoc_last, Gate.eval]
  exact congrArg₂ (· * ·) (CircuitFamily.eval_combine_inl a b s x ())
    (CircuitFamily.eval_combine_inr a b s x ())

def parallelFin : (n : ℕ) → (Fin n → CircuitFamily R X O) →
    CircuitFamily R X (Fin n × O)
  | 0, _ => ⟨0, .nil, fun p => Fin.elim0 p.1⟩
  | n + 1, f => ((f 0).combine (parallelFin n (fun i => f i.succ))).reindexOutputs
      (fun p => Fin.cases (.inl p.2) (fun i => .inr (i, p.2)) p.1)

@[simp] theorem size_parallelFin (n : ℕ) (f : Fin n → CircuitFamily R X O) :
    (parallelFin n f).size = ∑ i, (f i).size := by
  induction n with
  | zero => simp [parallelFin, CircuitFamily.size, Circuit.size]
  | succ n ih =>
      simp only [parallelFin, CircuitFamily.size_reindexOutputs, CircuitFamily.size_combine,
        ih, Fin.sum_univ_succ]

@[simp] theorem eval_parallelFin {A : Type*} [Add A] [Mul A]
    (s : R → A) (x : X → A) (n : ℕ) (f : Fin n → CircuitFamily R X O)
    (i : Fin n) (o : O) : (parallelFin n f).eval s x (i, o) = (f i).eval s x o := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [parallelFin]
      · simp [parallelFin, ih]

def linearFin [Zero R] : (n : ℕ) → (Fin n → R) → (Fin n → X) →
    CircuitFamily R X Unit
  | 0, _, _ => scalar 0
  | n + 1, a, wire => add (mul (scalar (a 0)) (input (wire 0)))
      (linearFin n (fun i => a i.succ) (fun i => wire i.succ))

@[simp] theorem size_linearFin [Zero R] (n : ℕ) (a : Fin n → R) (wire : Fin n → X) :
    (linearFin n a wire).size = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [linearFin, size_add, size_mul, size_scalar, size_input, ih]
      omega

theorem eval_linearFin [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]
    (x : X → A) (n : ℕ) (a : Fin n → R) (wire : Fin n → X) :
    (linearFin n a wire).eval (algebraMap R A) x () = ∑ i, a i • x (wire i) := by
  induction n with
  | zero => simp [linearFin]
  | succ n ih => simp [linearFin, ih, Fin.sum_univ_succ, Algebra.smul_def]

noncomputable def linear [Zero R] {J : Type*} [Fintype J]
    (a : J → R) (wire : J → X) : CircuitFamily R X Unit :=
  linearFin (Fintype.card J) (a ∘ (Fintype.equivFin J).symm)
    (wire ∘ (Fintype.equivFin J).symm)

@[simp] theorem size_linear [Zero R] {J : Type*} [Fintype J]
    (a : J → R) (wire : J → X) : (linear a wire).size = 2 * Fintype.card J :=
  size_linearFin _ _ _

theorem eval_linear [CommSemiring R] {A J : Type*} [Semiring A] [Algebra R A]
    [Fintype J] (x : X → A) (a : J → R) (wire : J → X) :
    (linear a wire).eval (algebraMap R A) x () = ∑ i, a i • x (wire i) := by
  rw [linear, eval_linearFin]
  exact (Fintype.equivFin J).symm.sum_comp (fun i => a i • x (wire i))

noncomputable def family [Fintype O] (f : O → CircuitFamily R X Unit) :
    CircuitFamily R X O :=
  (parallelFin (Fintype.card O) (f ∘ (Fintype.equivFin O).symm)).reindexOutputs
    (fun o => (Fintype.equivFin O o, ()))

@[simp] theorem size_family [Fintype O] (f : O → CircuitFamily R X Unit) :
    (family f).size = ∑ o, (f o).size := by
  rw [family, CircuitFamily.size_reindexOutputs, size_parallelFin]
  exact (Fintype.equivFin O).symm.sum_comp (fun o => (f o).size)

@[simp] theorem eval_family {A : Type*} [Add A] [Mul A] [Fintype O]
    (s : R → A) (x : X → A) (f : O → CircuitFamily R X Unit) (o : O) :
    (family f).eval s x o = (f o).eval s x () := by
  simp [family]

noncomputable def linearFamily [Zero R] {J : Type*} [Fintype J] [Fintype O]
    (a : O → J → R) (wire : O → J → X) : CircuitFamily R X O :=
  family (fun o => linear (a o) (wire o))

@[simp] theorem size_linearFamily [Zero R] {J : Type*} [Fintype J] [Fintype O]
    (a : O → J → R) (wire : O → J → X) :
    (linearFamily a wire).size = 2 * Fintype.card J * Fintype.card O := by
  simp only [linearFamily, size_family, size_linear, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
  ring

theorem eval_linearFamily [CommSemiring R] {A J : Type*}
    [Semiring A] [Algebra R A] [Fintype J] [Fintype O]
    (x : X → A) (a : O → J → R) (wire : O → J → X) (o : O) :
    (linearFamily a wire).eval (algebraMap R A) x o = ∑ j, a o j • x (wire o j) := by
  rw [linearFamily, eval_family, eval_linear]

def copies (r : ℕ) (p : CircuitFamily R X O) : CircuitFamily R (Fin r × X) (Fin r × O) :=
  parallelFin r (fun q => p.mapInputs (fun x => (q, x)))

@[simp] theorem size_copies (r : ℕ) (p : CircuitFamily R X O) :
    (copies r p).size = r * p.size := by
  simp [copies]

@[simp] theorem eval_copies {A : Type*} [Add A] [Mul A]
    (r : ℕ) (s : R → A) (x : Fin r × X → A) (p : CircuitFamily R X O)
    (q : Fin r) (o : O) :
    (copies r p).eval s x (q, o) = p.eval s (fun i => x (q, i)) o := by
  simp [copies, Function.comp_def]

end Lemmata.FockCircuits.Matrix.CircuitBuilders
