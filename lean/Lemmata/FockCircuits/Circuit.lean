module

public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits

universe u v w

inductive Gate (R : Type u) (X : Type v) (n : ℕ) where
  | scalar : R → Gate R X n
  | input : X → Gate R X n
  | copy : Fin n → Gate R X n
  | add : Fin n → Fin n → Gate R X n
  | mul : Fin n → Fin n → Gate R X n

namespace Gate

variable {R : Type u} {X : Type v} {A : Type w} {n : ℕ}

def cost : Gate R X n → ℕ
  | scalar _ => 0
  | input _ => 0
  | copy _ => 0
  | add _ _ => 1
  | mul _ _ => 1

def eval [Add A] [Mul A] (scalarValue : R → A) (inputValue : X → A)
    (values : Fin n → A) : Gate R X n → A
  | scalar r => scalarValue r
  | input x => inputValue x
  | copy i => values i
  | add i j => values i + values j
  | mul i j => values i * values j

def mapInputs {Y : Type*} (f : X → Y) : Gate R X n → Gate R Y n
  | scalar r => scalar r
  | input x => input (f x)
  | copy i => copy i
  | add i j => add i j
  | mul i j => mul i j

def mapScalars {S : Type*} (f : R → S) : Gate R X n → Gate S X n
  | scalar r => scalar (f r)
  | input x => input x
  | copy i => copy i
  | add i j => add i j
  | mul i j => mul i j

@[simp] theorem cost_mapScalars {S : Type*} (f : R → S) (g : Gate R X n) :
    (g.mapScalars f).cost = g.cost := by
  cases g <;> rfl

@[simp] theorem eval_mapScalars [Add A] [Mul A] {S : Type*} (f : R → S)
    (s : S → A) (x : X → A) (values : Fin n → A) (g : Gate R X n) :
    (g.mapScalars f).eval s x values = g.eval (s ∘ f) x values := by
  cases g <;> rfl

def reindex {m : ℕ} (f : Fin n → Fin m) : Gate R X n → Gate R X m
  | scalar r => scalar r
  | input x => input x
  | copy i => copy (f i)
  | add i j => add (f i) (f j)
  | mul i j => mul (f i) (f j)

@[simp] theorem cost_reindex {m : ℕ} (f : Fin n → Fin m) (g : Gate R X n) :
    (g.reindex f).cost = g.cost := by
  cases g <;> rfl

@[simp] theorem eval_reindex [Add A] [Mul A] {m : ℕ} (f : Fin n → Fin m)
    (s : R → A) (x : X → A) (values : Fin m → A) (g : Gate R X n) :
    (g.reindex f).eval s x values = g.eval s x (values ∘ f) := by
  cases g <;> rfl

/-- A wire alias is free; only addition and multiplication count as arithmetic gates. -/
def substitute {Y : Type*} {m : ℕ} (inputs : X → Fin m) (refs : Fin n → Fin m) :
    Gate R X n → Gate R Y m
  | scalar r => scalar r
  | input x => copy (inputs x)
  | copy i => copy (refs i)
  | add i j => add (refs i) (refs j)
  | mul i j => mul (refs i) (refs j)

@[simp] theorem cost_substitute {Y : Type*} {m : ℕ} (inputs : X → Fin m)
    (refs : Fin n → Fin m) (g : Gate R X n) :
    (g.substitute (Y := Y) inputs refs).cost = g.cost := by
  cases g <;> rfl

@[simp] theorem eval_substitute [Add A] [Mul A] {Y : Type*} {m : ℕ}
    (inputs : X → Fin m) (refs : Fin n → Fin m) (s : R → A)
    (y : Y → A) (values : Fin m → A) (g : Gate R X n) :
    (g.substitute inputs refs).eval s y values =
      g.eval s (values ∘ inputs) (values ∘ refs) := by
  cases g <;> rfl

def CopyFree : Gate R X n → Prop
  | copy _ => False
  | _ => True

@[simp] theorem copyFree_reindex {m : ℕ} (f : Fin n → Fin m) (g : Gate R X n) :
    (g.reindex f).CopyFree = g.CopyFree := by
  cases g <;> rfl

@[simp] theorem cost_mapInputs {Y : Type*} (f : X → Y) (g : Gate R X n) :
    (g.mapInputs f).cost = g.cost := by
  cases g <;> rfl

@[simp] theorem eval_mapInputs [Add A] [Mul A] {Y : Type*} (f : X → Y)
    (s : R → A) (x : Y → A) (values : Fin n → A) (g : Gate R X n) :
    (g.mapInputs f).eval s x values = g.eval s (x ∘ f) values := by
  cases g <;> rfl

end Gate

/-- Each gate refers only to earlier nodes; an output may be reused arbitrarily. -/
inductive Circuit (R : Type u) (X : Type v) : ℕ → Type (max u v) where
  | nil : Circuit R X 0
  | snoc {n : ℕ} : Circuit R X n → Gate R X n → Circuit R X (n + 1)

namespace Circuit

variable {R : Type u} {X : Type v} {A : Type w}

def size : {n : ℕ} → Circuit R X n → ℕ
  | _, nil => 0
  | _, snoc c g => c.size + g.cost

def eval [Add A] [Mul A] (s : R → A) (x : X → A) :
    {n : ℕ} → Circuit R X n → Fin n → A
  | _, nil => Fin.elim0
  | _, snoc c g => Fin.snoc (c.eval s x) (g.eval s x (c.eval s x))

@[simp] theorem size_nil : (nil : Circuit R X 0).size = 0 := rfl

@[simp] theorem size_snoc {n : ℕ} (c : Circuit R X n) (g : Gate R X n) :
    (c.snoc g).size = c.size + g.cost := rfl

@[simp] theorem eval_snoc_castSucc [Add A] [Mul A] {n : ℕ} (s : R → A)
    (x : X → A) (c : Circuit R X n) (g : Gate R X n) (i : Fin n) :
    (c.snoc g).eval s x i.castSucc = c.eval s x i := by
  exact Fin.snoc_castSucc _ _ _

@[simp] theorem eval_snoc_last [Add A] [Mul A] {n : ℕ} (s : R → A)
    (x : X → A) (c : Circuit R X n) (g : Gate R X n) :
    (c.snoc g).eval s x (Fin.last n) = g.eval s x (c.eval s x) := by
  exact Fin.snoc_last _ _

def mapInputs {Y : Type*} (f : X → Y) :
    {n : ℕ} → Circuit R X n → Circuit R Y n
  | _, nil => nil
  | _, snoc c g => (c.mapInputs f).snoc (g.mapInputs f)

def mapScalars {S : Type*} (f : R → S) :
    {n : ℕ} → Circuit R X n → Circuit S X n
  | _, nil => nil
  | _, snoc c g => (c.mapScalars f).snoc (g.mapScalars f)

@[simp] theorem size_mapScalars {S : Type*} (f : R → S) {n : ℕ}
    (c : Circuit R X n) : (c.mapScalars f).size = c.size := by
  induction c with
  | nil => rfl
  | snoc c g ih => simp only [mapScalars, size_snoc, ih, Gate.cost_mapScalars]

@[simp] theorem eval_mapScalars [Add A] [Mul A] {S : Type*} (f : R → S)
    (s : S → A) (x : X → A) {n : ℕ} (c : Circuit R X n) :
    (c.mapScalars f).eval s x = c.eval (s ∘ f) x := by
  induction c with
  | nil => rfl
  | snoc c g ih => simp only [mapScalars, eval, ih, Gate.eval_mapScalars]

@[simp] theorem size_mapInputs {Y : Type*} (f : X → Y) {n : ℕ}
    (c : Circuit R X n) : (c.mapInputs f).size = c.size := by
  induction c with
  | nil => rfl
  | snoc c g ih => simp only [mapInputs, size_snoc, ih, Gate.cost_mapInputs]

@[simp] theorem eval_mapInputs [Add A] [Mul A] {Y : Type*} (f : X → Y)
    (s : R → A) (x : Y → A) {n : ℕ} (c : Circuit R X n) :
    (c.mapInputs f).eval s x = c.eval s (x ∘ f) := by
  induction c with
  | nil => rfl
  | snoc c g ih =>
      simp only [mapInputs, eval, ih, Gate.eval_mapInputs]

theorem size_le_nodes {n : ℕ} (c : Circuit R X n) : c.size ≤ n := by
  induction c with
  | nil => exact Nat.le_refl 0
  | @snoc n c g ih =>
      have hg : g.cost ≤ 1 := by cases g <;> simp [Gate.cost]
      exact Nat.add_le_add ih hg

def append {n : ℕ} (c : Circuit R X n) :
    {m : ℕ} → Circuit R X m → Circuit R X (n + m)
  | _, nil => c
  | _, snoc d g => (c.append d).snoc (g.reindex (Fin.natAdd n))

@[simp] theorem size_append {n m : ℕ} (c : Circuit R X n) (d : Circuit R X m) :
    (c.append d).size = c.size + d.size := by
  induction d with
  | nil => simp [append]
  | snoc d g ih => simp [append, ih, Nat.add_assoc]

theorem eval_append_left [Add A] [Mul A] (s : R → A) (x : X → A)
    {n m : ℕ} (c : Circuit R X n) (d : Circuit R X m) (i : Fin n) :
    (c.append d).eval s x (Fin.castAdd m i) = c.eval s x i := by
  induction d with
  | nil => rfl
  | snoc d g ih =>
      simpa only [append, eval, Fin.snoc_castAdd] using ih

theorem eval_append_right [Add A] [Mul A] (s : R → A) (x : X → A)
    {n m : ℕ} (c : Circuit R X n) (d : Circuit R X m) :
    (c.append d).eval s x ∘ Fin.natAdd n = d.eval s x := by
  induction d with
  | nil => funext i; exact Fin.elim0 i
  | snoc d g ih =>
      simp only [append, eval, Fin.snoc_comp_natAdd, Gate.eval_reindex, ih]

theorem eval_hom {B : Type*} [Semiring A] [Semiring B] (f : A →+* B)
    (s : R → A) (x : X → A) {n : ℕ} (c : Circuit R X n) :
    c.eval (f ∘ s) (f ∘ x) = f ∘ c.eval s x := by
  induction c with
  | nil => funext i; exact Fin.elim0 i
  | snoc c g ih =>
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [eval_snoc_last]
        cases g <;> simp [Gate.eval, ih, Function.comp_apply]
      · simp only [eval_snoc_castSucc, ih, Function.comp_apply]

def substitute {Y : Type*} {n : ℕ} (c : Circuit R Y n) (inputs : X → Fin n) :
    {m : ℕ} → Circuit R X m → Circuit R Y (n + m)
  | _, nil => c
  | m + 1, snoc d g =>
      (c.substitute inputs d).snoc
        (g.substitute (Fin.castAdd m ∘ inputs) (Fin.natAdd n))

@[simp] theorem size_substitute {Y : Type*} {n m : ℕ}
    (c : Circuit R Y n) (inputs : X → Fin n) (d : Circuit R X m) :
    (c.substitute inputs d).size = c.size + d.size := by
  induction d with
  | nil => simp [substitute]
  | snoc d g ih => simp [substitute, ih, Nat.add_assoc]

theorem eval_substitute_left [Add A] [Mul A] {Y : Type*} (s : R → A) (y : Y → A)
    {n m : ℕ} (c : Circuit R Y n) (inputs : X → Fin n)
    (d : Circuit R X m) (i : Fin n) :
    (c.substitute inputs d).eval s y (Fin.castAdd m i) = c.eval s y i := by
  induction d with
  | nil => rfl
  | snoc d g ih =>
      simpa only [substitute, eval, Fin.snoc_castAdd] using ih

theorem eval_substitute_right [Add A] [Mul A] {Y : Type*} (s : R → A) (y : Y → A)
    {n m : ℕ} (c : Circuit R Y n) (inputs : X → Fin n) (d : Circuit R X m) :
    (c.substitute inputs d).eval s y ∘ Fin.natAdd n =
      d.eval s (c.eval s y ∘ inputs) := by
  induction d with
  | nil => funext i; exact Fin.elim0 i
  | @snoc m d g ih =>
      have hin :
          (c.substitute inputs d).eval s y ∘ (Fin.castAdd m ∘ inputs) =
            c.eval s y ∘ inputs := by
        funext x
        exact c.eval_substitute_left s y inputs d (inputs x)
      simp only [substitute, eval, Fin.snoc_comp_natAdd, Gate.eval_substitute, ih, hin]

def CopyFree : {n : ℕ} → Circuit R X n → Prop
  | _, nil => True
  | _, snoc c g => c.CopyFree ∧ g.CopyFree

theorem eraseCopies [Add A] [Mul A] (s : R → A) (x : X → A)
    {n : ℕ} (c : Circuit R X n) :
    ∃ (m : ℕ) (d : Circuit R X m) (refs : Fin n → Fin m),
      d.CopyFree ∧ d.size = c.size ∧ d.eval s x ∘ refs = c.eval s x := by
  induction c with
  | nil => exact ⟨0, nil, Fin.elim0, trivial, rfl, rfl⟩
  | @snoc n c g ih =>
      obtain ⟨m, d, refs, hd, hs, he⟩ := ih
      cases g with
      | copy i =>
          refine ⟨m, d, Fin.snoc refs (refs i), hd, ?_, ?_⟩
          · simp only [size_snoc, Gate.cost, Nat.add_zero]
            exact hs
          · funext j
            refine Fin.lastCases ?_ (fun k => ?_) j
            · simpa only [Function.comp_apply, Fin.snoc_last, eval_snoc_last,
                Gate.eval] using congrFun he i
            · simpa only [Function.comp_apply, Fin.snoc_castSucc, eval_snoc_castSucc] using
                congrFun he k
      | scalar r =>
          refine ⟨m + 1, d.snoc (.scalar r),
            Fin.snoc (Fin.castSucc ∘ refs) (Fin.last m), ⟨hd, trivial⟩, ?_, ?_⟩
          · simp only [size_snoc, Gate.cost, Nat.add_zero]
            exact hs
          · funext j
            refine Fin.lastCases ?_ (fun k => ?_) j
            · simp only [Function.comp_apply, Fin.snoc_last, eval_snoc_last,
                Gate.eval]
            · simpa only [Function.comp_apply, Fin.snoc_castSucc, eval_snoc_castSucc] using
                congrFun he k
      | input a =>
          refine ⟨m + 1, d.snoc (.input a),
            Fin.snoc (Fin.castSucc ∘ refs) (Fin.last m), ⟨hd, trivial⟩, ?_, ?_⟩
          · simp only [size_snoc, Gate.cost, Nat.add_zero]
            exact hs
          · funext j
            refine Fin.lastCases ?_ (fun k => ?_) j
            · simp only [Function.comp_apply, Fin.snoc_last, eval_snoc_last,
                Gate.eval]
            · simpa only [Function.comp_apply, Fin.snoc_castSucc, eval_snoc_castSucc] using
                congrFun he k
      | add i j =>
          refine ⟨m + 1, d.snoc (.add (refs i) (refs j)),
            Fin.snoc (Fin.castSucc ∘ refs) (Fin.last m), ⟨hd, trivial⟩, ?_, ?_⟩
          · simp only [size_snoc, Gate.cost, hs]
          · funext z
            refine Fin.lastCases ?_ (fun k => ?_) z
            · simp only [Function.comp_apply, Fin.snoc_last, eval_snoc_last,
                Gate.eval]
              exact congrArg₂ (· + ·) (congrFun he i) (congrFun he j)
            · simpa only [Function.comp_apply, Fin.snoc_castSucc, eval_snoc_castSucc] using
                congrFun he k
      | mul i j =>
          refine ⟨m + 1, d.snoc (.mul (refs i) (refs j)),
            Fin.snoc (Fin.castSucc ∘ refs) (Fin.last m), ⟨hd, trivial⟩, ?_, ?_⟩
          · simp only [size_snoc, Gate.cost, hs]
          · funext z
            refine Fin.lastCases ?_ (fun k => ?_) z
            · simp only [Function.comp_apply, Fin.snoc_last, eval_snoc_last,
                Gate.eval]
              exact congrArg₂ (· * ·) (congrFun he i) (congrFun he j)
            · simpa only [Function.comp_apply, Fin.snoc_castSucc, eval_snoc_castSucc] using
                congrFun he k

section Polynomials

variable [CommSemiring R]

noncomputable def polynomial {n : ℕ} (c : Circuit R X n) :
    Fin n → FreeAlgebra R X :=
  c.eval (algebraMap R (FreeAlgebra R X)) (FreeAlgebra.ι R)

@[simp] theorem polynomial_append_left {n m : ℕ} (c : Circuit R X n)
    (d : Circuit R X m) (i : Fin n) :
    (c.append d).polynomial (Fin.castAdd m i) = c.polynomial i :=
  c.eval_append_left _ _ d i

@[simp] theorem polynomial_append_right {n m : ℕ} (c : Circuit R X n)
    (d : Circuit R X m) (i : Fin m) :
    (c.append d).polynomial (Fin.natAdd n i) = d.polynomial i :=
  congrFun (c.eval_append_right _ _ d) i

@[simp] theorem polynomial_snoc_last {n : ℕ} (c : Circuit R X n)
    (g : Gate R X n) :
    (c.snoc g).polynomial (Fin.last n) =
      g.eval (algebraMap R (FreeAlgebra R X)) (FreeAlgebra.ι R) c.polynomial :=
  c.eval_snoc_last _ _ g

theorem polynomial_lift {B : Type*} [Semiring B] [Algebra R B]
    (x : X → B) {n : ℕ} (c : Circuit R X n) (i : Fin n) :
    FreeAlgebra.lift R x (c.polynomial i) = c.eval (algebraMap R B) x i := by
  have h := c.eval_hom (FreeAlgebra.lift R x).toRingHom
    (algebraMap R (FreeAlgebra R X)) (FreeAlgebra.ι R)
  have hi := congrFun h i
  simpa [polynomial, Function.comp_def] using hi.symm

end Polynomials

end Circuit

structure CircuitFamily (R : Type u) (X : Type v) (O : Type w) where
  nodeCount : ℕ
  circuit : Circuit R X nodeCount
  output : O → Fin nodeCount

namespace CircuitFamily

variable {R : Type u} {X : Type v} {O : Type w}

def size (c : CircuitFamily R X O) : ℕ := c.circuit.size

def eval {A : Type*} [Add A] [Mul A] (c : CircuitFamily R X O)
    (s : R → A) (x : X → A) : O → A :=
  c.circuit.eval s x ∘ c.output

noncomputable def polynomial [CommSemiring R] (c : CircuitFamily R X O) :
    O → FreeAlgebra R X :=
  c.eval (algebraMap R (FreeAlgebra R X)) (FreeAlgebra.ι R)

theorem polynomial_lift [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]
    (c : CircuitFamily R X O) (x : X → A) (o : O) :
    FreeAlgebra.lift R x (c.polynomial o) = c.eval (algebraMap R A) x o :=
  c.circuit.polynomial_lift x (c.output o)

def reindexOutputs {P : Type*} (c : CircuitFamily R X O) (f : P → O) :
    CircuitFamily R X P where
  nodeCount := c.nodeCount
  circuit := c.circuit
  output := c.output ∘ f

@[simp] theorem size_reindexOutputs {P : Type*} (c : CircuitFamily R X O) (f : P → O) :
    (c.reindexOutputs f).size = c.size := rfl

@[simp] theorem eval_reindexOutputs {A P : Type*} [Add A] [Mul A]
    (c : CircuitFamily R X O) (f : P → O) (s : R → A) (x : X → A) (p : P) :
    (c.reindexOutputs f).eval s x p = c.eval s x (f p) := rfl

@[simp] theorem polynomial_reindexOutputs [CommSemiring R] {P : Type*}
    (c : CircuitFamily R X O) (f : P → O) (p : P) :
    (c.reindexOutputs f).polynomial p = c.polynomial (f p) := rfl

def mapScalars {S : Type*} (c : CircuitFamily R X O) (f : R → S) :
    CircuitFamily S X O where
  nodeCount := c.nodeCount
  circuit := c.circuit.mapScalars f
  output := c.output

@[simp] theorem size_mapScalars {S : Type*} (c : CircuitFamily R X O) (f : R → S) :
    (c.mapScalars f).size = c.size := by
  simp only [size, mapScalars, Circuit.size_mapScalars]

@[simp] theorem eval_mapScalars {A S : Type*} [Add A] [Mul A]
    (c : CircuitFamily R X O) (f : R → S) (s : S → A) (x : X → A) :
    (c.mapScalars f).eval s x = c.eval (s ∘ f) x := by
  simp only [eval, mapScalars, Circuit.eval_mapScalars]

def mapInputs {Y : Type*} (c : CircuitFamily R X O) (f : X → Y) :
    CircuitFamily R Y O where
  nodeCount := c.nodeCount
  circuit := c.circuit.mapInputs f
  output := c.output

@[simp] theorem size_mapInputs {Y : Type*} (c : CircuitFamily R X O) (f : X → Y) :
    (c.mapInputs f).size = c.size := by
  simp only [size, mapInputs, Circuit.size_mapInputs]

@[simp] theorem eval_mapInputs {A Y : Type*} [Add A] [Mul A]
    (c : CircuitFamily R X O) (f : X → Y) (s : R → A) (x : Y → A) :
    (c.mapInputs f).eval s x = c.eval s (x ∘ f) := by
  simp only [eval, mapInputs, Circuit.eval_mapInputs]

def combine {P : Type*} (c : CircuitFamily R X O) (d : CircuitFamily R X P) :
    CircuitFamily R X (O ⊕ P) where
  nodeCount := c.nodeCount + d.nodeCount
  circuit := c.circuit.append d.circuit
  output := Sum.elim (Fin.castAdd d.nodeCount ∘ c.output)
    (Fin.natAdd c.nodeCount ∘ d.output)

@[simp] theorem size_combine {P : Type*} (c : CircuitFamily R X O)
    (d : CircuitFamily R X P) :
    (c.combine d).size = c.size + d.size := by
  simp only [size, combine, Circuit.size_append]

@[simp] theorem eval_combine_inl {A P : Type*} [Add A] [Mul A]
    (c : CircuitFamily R X O) (d : CircuitFamily R X P) (s : R → A)
    (x : X → A) (o : O) :
    (c.combine d).eval s x (Sum.inl o) = c.eval s x o := by
  simp only [eval, combine, Function.comp_apply, Sum.elim_inl,
    Circuit.eval_append_left]

@[simp] theorem eval_combine_inr {A P : Type*} [Add A] [Mul A]
    (c : CircuitFamily R X O) (d : CircuitFamily R X P) (s : R → A)
    (x : X → A) (p : P) :
    (c.combine d).eval s x (Sum.inr p) = d.eval s x p := by
  exact congrFun (c.circuit.eval_append_right s x d.circuit) (d.output p)

def substitute {Y : Type*} (c : CircuitFamily R Y X) (d : CircuitFamily R X O) :
    CircuitFamily R Y O where
  nodeCount := c.nodeCount + d.nodeCount
  circuit := c.circuit.substitute c.output d.circuit
  output := Fin.natAdd c.nodeCount ∘ d.output

@[simp] theorem size_substitute {Y : Type*} (c : CircuitFamily R Y X)
    (d : CircuitFamily R X O) :
    (c.substitute d).size = c.size + d.size := by
  simp only [size, substitute, Circuit.size_substitute]

@[simp] theorem eval_substitute {A Y : Type*} [Add A] [Mul A]
    (c : CircuitFamily R Y X) (d : CircuitFamily R X O) (s : R → A) (y : Y → A) :
    (c.substitute d).eval s y = d.eval s (c.eval s y) := by
  funext o
  exact congrFun (c.circuit.eval_substitute_right s y c.output d.circuit) (d.output o)

theorem polynomial_substitute [CommSemiring R] {Y : Type*}
    (c : CircuitFamily R Y X) (d : CircuitFamily R X O) (o : O) :
    (c.substitute d).polynomial o =
      FreeAlgebra.lift R c.polynomial (d.polynomial o) := by
  change (c.substitute d).eval (algebraMap R (FreeAlgebra R Y)) (FreeAlgebra.ι R) o = _
  rw [eval_substitute]
  exact (d.polynomial_lift c.polynomial o).symm

/-- Append a shared subroutine while keeping every old output available. -/
def extendUsing {Y I P : Type*} (c : CircuitFamily R Y O)
    (inputs : I → O) (d : CircuitFamily R I P) : CircuitFamily R Y (O ⊕ P) where
  nodeCount := c.nodeCount + d.nodeCount
  circuit := c.circuit.substitute (c.output ∘ inputs) d.circuit
  output := Sum.elim (Fin.castAdd d.nodeCount ∘ c.output)
    (Fin.natAdd c.nodeCount ∘ d.output)

@[simp] theorem size_extendUsing {Y I P : Type*} (c : CircuitFamily R Y O)
    (inputs : I → O) (d : CircuitFamily R I P) :
    (c.extendUsing inputs d).size = c.size + d.size := by
  exact Circuit.size_substitute c.circuit (c.output ∘ inputs) d.circuit

@[simp] theorem eval_extendUsing_inl {A Y I P : Type*} [Add A] [Mul A]
    (c : CircuitFamily R Y O) (inputs : I → O) (d : CircuitFamily R I P)
    (s : R → A) (y : Y → A) (o : O) :
    (c.extendUsing inputs d).eval s y (Sum.inl o) = c.eval s y o := by
  exact c.circuit.eval_substitute_left s y (c.output ∘ inputs) d.circuit (c.output o)

@[simp] theorem eval_extendUsing_inr {A Y I P : Type*} [Add A] [Mul A]
    (c : CircuitFamily R Y O) (inputs : I → O) (d : CircuitFamily R I P)
    (s : R → A) (y : Y → A) (p : P) :
    (c.extendUsing inputs d).eval s y (Sum.inr p) =
      d.eval s (c.eval s y ∘ inputs) p := by
  exact congrFun
    (c.circuit.eval_substitute_right s y (c.output ∘ inputs) d.circuit) (d.output p)

@[simp] theorem polynomial_extendUsing_inl [CommSemiring R] {Y I P : Type*}
    (c : CircuitFamily R Y O) (inputs : I → O) (d : CircuitFamily R I P) (o : O) :
    (c.extendUsing inputs d).polynomial (Sum.inl o) = c.polynomial o :=
  eval_extendUsing_inl c inputs d _ _ o

@[simp] theorem polynomial_extendUsing_inr [CommSemiring R] {Y I P : Type*}
    (c : CircuitFamily R Y O) (inputs : I → O) (d : CircuitFamily R I P) (p : P) :
    (c.extendUsing inputs d).polynomial (Sum.inr p) =
      FreeAlgebra.lift R (c.polynomial ∘ inputs) (d.polynomial p) := by
  change (c.extendUsing inputs d).eval _ _ (Sum.inr p) = _
  rw [eval_extendUsing_inr]
  exact (d.polynomial_lift (c.polynomial ∘ inputs) p).symm

end CircuitFamily

section CircuitBounds

variable {R : Type u} [CommSemiring R] {X : Type v}

def HasCircuit (p : FreeAlgebra R X) (s : ℕ) : Prop :=
  ∃ (n : ℕ) (c : Circuit R X n) (i : Fin n), c.polynomial i = p ∧ c.size ≤ s

namespace HasCircuit

theorem scalar (r : R) : HasCircuit (algebraMap R (FreeAlgebra R X) r) 0 := by
  refine ⟨1, Circuit.nil.snoc (.scalar r), Fin.last 0, ?_, ?_⟩
  · simp only [Circuit.polynomial_snoc_last, Gate.eval]
  · exact Nat.le_refl 0

theorem input (x : X) : HasCircuit (FreeAlgebra.ι R x) 0 := by
  refine ⟨1, Circuit.nil.snoc (.input x), Fin.last 0, ?_, ?_⟩
  · simp only [Circuit.polynomial_snoc_last, Gate.eval]
  · exact Nat.le_refl 0

theorem mono {p : FreeAlgebra R X} {s t : ℕ} (h : HasCircuit p s) (hst : s ≤ t) :
    HasCircuit p t := by
  obtain ⟨n, c, i, hp, hc⟩ := h
  exact ⟨n, c, i, hp, hc.trans hst⟩

theorem exists_copyFree {p : FreeAlgebra R X} {s : ℕ} (h : HasCircuit p s) :
    ∃ (n : ℕ) (c : Circuit R X n) (i : Fin n),
      c.CopyFree ∧ c.polynomial i = p ∧ c.size ≤ s := by
  obtain ⟨n, c, i, hp, hc⟩ := h
  obtain ⟨m, d, refs, hd, hs, he⟩ :=
    c.eraseCopies (algebraMap R (FreeAlgebra R X)) (FreeAlgebra.ι R)
  refine ⟨m, d, refs i, hd, ?_, ?_⟩
  · exact (congrFun he i).trans hp
  · simpa only [hs] using hc

theorem add {p q : FreeAlgebra R X} {s t : ℕ}
    (hp : HasCircuit p s) (hq : HasCircuit q t) :
    HasCircuit (p + q) (s + t + 1) := by
  obtain ⟨n, c, i, hi, hc⟩ := hp
  obtain ⟨m, d, j, hj, hd⟩ := hq
  refine ⟨n + m + 1,
    (c.append d).snoc (.add (Fin.castAdd m i) (Fin.natAdd n j)),
    Fin.last (n + m), ?_, ?_⟩
  · simp only [Circuit.polynomial_snoc_last, Gate.eval,
      Circuit.polynomial_append_left, Circuit.polynomial_append_right, hi, hj]
  · simpa only [Circuit.size_snoc, Circuit.size_append, Gate.cost] using
      Nat.add_le_add_right (Nat.add_le_add hc hd) 1

theorem mul {p q : FreeAlgebra R X} {s t : ℕ}
    (hp : HasCircuit p s) (hq : HasCircuit q t) :
    HasCircuit (p * q) (s + t + 1) := by
  obtain ⟨n, c, i, hi, hc⟩ := hp
  obtain ⟨m, d, j, hj, hd⟩ := hq
  refine ⟨n + m + 1,
    (c.append d).snoc (.mul (Fin.castAdd m i) (Fin.natAdd n j)),
    Fin.last (n + m), ?_, ?_⟩
  · simp only [Circuit.polynomial_snoc_last, Gate.eval,
      Circuit.polynomial_append_left, Circuit.polynomial_append_right, hi, hj]
  · simpa only [Circuit.size_snoc, Circuit.size_append, Gate.cost] using
      Nat.add_le_add_right (Nat.add_le_add hc hd) 1

end HasCircuit

theorem exists_circuit (p : FreeAlgebra R X) : ∃ s, HasCircuit p s := by
  induction p using FreeAlgebra.induction with
  | grade0 r => exact ⟨0, HasCircuit.scalar r⟩
  | grade1 x => exact ⟨0, HasCircuit.input x⟩
  | mul p q hp hq =>
      obtain ⟨s, hs⟩ := hp
      obtain ⟨t, ht⟩ := hq
      exact ⟨s + t + 1, hs.mul ht⟩
  | add p q hp hq =>
      obtain ⟨s, hs⟩ := hp
      obtain ⟨t, ht⟩ := hq
      exact ⟨s + t + 1, hs.add ht⟩

end CircuitBounds

end Lemmata.FockCircuits
