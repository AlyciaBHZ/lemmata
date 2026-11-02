module

public import Lemmata.FockCircuits.Circuit
public import Mathlib.Data.Matrix.Mul

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits

universe u v

section OrderedProducts

variable {A : Type u} [Semiring A]
variable {ρ : Type*} {ι : Type*} {κ : Type*}
variable [Fintype ρ] [Fintype ι] [Fintype κ]

def orderedAssembly (a b c d : Matrix ρ ι A) (y u : Matrix ι κ A) : A :=
  ∑ l, ∑ q,
    ((((a * y).transpose * b) q l +
      (c.transpose * (y.transpose * d.transpose).transpose) l q) * u l q)

omit [Fintype κ] in
theorem firstProduct_expansion (a b : Matrix ρ ι A) (y : Matrix ι κ A)
    (q : κ) (l : ι) :
    ((a * y).transpose * b) q l =
      ∑ r, ∑ j, a r j * y j q * b r l := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]

omit [Fintype κ] in
theorem secondProduct_expansion (c d : Matrix ρ ι A) (y : Matrix ι κ A)
    (l : ι) (q : κ) :
    (c.transpose * (y.transpose * d.transpose).transpose) l q =
      ∑ r, ∑ j, c r l * y j q * d r j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, mul_assoc]

theorem orderedAssembly_expansion (a b c d : Matrix ρ ι A)
    (y u : Matrix ι κ A) :
    orderedAssembly a b c d y u =
      ∑ l, ∑ q,
        ((∑ r, ∑ j, a r j * y j q * b r l * u l q) +
         (∑ r, ∑ j, c r l * y j q * d r j * u l q)) := by
  simp only [orderedAssembly, firstProduct_expansion, secondProduct_expansion,
    add_mul, Finset.sum_mul]

end OrderedProducts

section Coefficients

variable {R : Type u} [CommSemiring R] {A : Type v} [Semiring A] [Algebra R A]
variable {I : Type*} {J : Type*} [Fintype I] [Fintype J]

def colouredCrossing (x v : I → A) (y u : J → A) : A :=
  ∑ i, ∑ j, x i * y j * v i * u j

theorem contract_crossing_coefficients [DecidableEq I] [DecidableEq J]
    (coeff : I → J → I → J → R)
    (h : ∀ i j k l, coeff i j k l = if i = k then (if j = l then 1 else 0) else 0)
    (x v : I → A) (y u : J → A) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      coeff i j k l • (x i * y j * v k * u l)) =
        colouredCrossing x v y u := by
  simp [h, colouredCrossing]

def coefficientRows {ρ : Type*} (a : ρ → I → J → R) (x : I → A) :
    Matrix ρ J A :=
  fun r j => ∑ i, a r i j • x i

omit [Fintype J] in
theorem coefficientRows_middle {ρ : Type*} (a b : ρ → I → J → R)
    (x v : I → A) (y : A) (r : ρ) (j l : J) :
    coefficientRows a x r j * y * coefficientRows b v r l =
      ∑ i, ∑ k, (a r i j * b r k l) • (x i * y * v k) := by
  simp only [coefficientRows, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm]

private theorem sum_move_first {ρ B C D : Type*}
    [Fintype ρ] [Fintype B] [Fintype C] [Fintype D]
    (f : ρ → B → C → D → A) :
    (∑ r, ∑ b, ∑ c, ∑ d, f r b c d) =
      ∑ b, ∑ c, ∑ d, ∑ r, f r b c d := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]

theorem directAssembly_coefficient_expansion {ρ K : Type*}
    [Fintype ρ] [Fintype K]
    (a b c d : ρ → I → J → R) (x v : I → A) (y : Matrix J K A)
    (l : J) (q : K) :
    (((coefficientRows a x * y).transpose * coefficientRows b v) q l +
      ((coefficientRows c x).transpose *
        (y.transpose * (coefficientRows d v).transpose).transpose) l q) =
      ∑ i, ∑ j, ∑ k,
        ((∑ r, a r i j * b r k l) + (∑ r, c r i l * d r k j)) •
          (x i * y j q * v k) := by
  simp only [firstProduct_expansion, secondProduct_expansion,
    coefficientRows_middle]
  have hab :
      (∑ r, ∑ j, ∑ i, ∑ k,
        (a r i j * b r k l) • (x i * y j q * v k)) =
        ∑ i, ∑ j, ∑ k, ∑ r,
          (a r i j * b r k l) • (x i * y j q * v k) := by
    rw [sum_move_first]
    exact Finset.sum_comm
  have hcd :
      (∑ r, ∑ j, ∑ i, ∑ k,
        (c r i l * d r k j) • (x i * y j q * v k)) =
        ∑ i, ∑ j, ∑ k, ∑ r,
          (c r i l * d r k j) • (x i * y j q * v k) := by
    rw [sum_move_first]
    exact Finset.sum_comm
  rw [hab, hcd]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_smul, ← add_smul]

def batchedCrossing {K : Type*} [Fintype K] (x v : I → A)
    (y u : Matrix J K A) : A :=
  ∑ i, ∑ j, ∑ q, x i * y j q * v i * u j q

theorem directAssembly_eq_crossing {ρ K : Type*}
    [Fintype ρ] [Fintype K] [DecidableEq I] [DecidableEq J]
    (a b c d : ρ → I → J → R)
    (h : ∀ i j k l,
      (∑ r, a r i j * b r k l) + (∑ r, c r i l * d r k j) =
        if i = k then (if j = l then 1 else 0) else 0)
    (x v : I → A) (y u : Matrix J K A) :
    orderedAssembly (coefficientRows a x) (coefficientRows b v)
      (coefficientRows c x) (coefficientRows d v) y u =
        batchedCrossing x v y u := by
  have hz (l : J) (q : K) :
      (((coefficientRows a x * y).transpose * coefficientRows b v) q l +
        ((coefficientRows c x).transpose *
          (y.transpose * (coefficientRows d v).transpose).transpose) l q) =
        ∑ i, x i * y l q * v i := by
    rw [directAssembly_coefficient_expansion]
    simp [h]
  simp only [orderedAssembly, hz, Finset.sum_mul]
  change (∑ l, ∑ q, ∑ i, x i * y l q * v i * u l q) =
    ∑ i, ∑ l, ∑ q, x i * y l q * v i * u l q
  calc
    _ = ∑ l, ∑ i, ∑ q, x i * y l q * v i * u l q := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

end Coefficients

/-- An exact shared DAG certificate for an ordered generic matrix product. -/
structure OrderedMatrixAlgorithm (R : Type*) [CommSemiring R]
    (L : Type*) (M : Type*) (N : Type*) [Fintype M] where
  circuit : CircuitFamily R ((L × M) ⊕ (M × N)) (L × N)
  correct : ∀ l n, circuit.polynomial (l, n) =
    ∑ m, FreeAlgebra.ι R (Sum.inl (l, m)) * FreeAlgebra.ι R (Sum.inr (m, n))

namespace OrderedMatrixAlgorithm

variable {R : Type*} [CommSemiring R]
variable {L : Type*} {M : Type*} {N : Type*} [Fintype M]

def size (a : OrderedMatrixAlgorithm R L M N) : ℕ := a.circuit.size

theorem eval_correct (a : OrderedMatrixAlgorithm R L M N)
    {A : Type*} [Semiring A] [Algebra R A] (left : Matrix L M A)
    (right : Matrix M N A) (l : L) (n : N) :
    a.circuit.eval (algebraMap R A)
      (Sum.elim (fun p => left p.1 p.2) (fun p => right p.1 p.2)) (l, n) =
        (left * right) l n := by
  rw [← CircuitFamily.polynomial_lift, a.correct]
  simp [Matrix.mul_apply]

def run {X : Type*} (a : OrderedMatrixAlgorithm R L M N)
    (bank : CircuitFamily R X ((L × M) ⊕ (M × N))) :
    CircuitFamily R X (L × N) :=
  bank.substitute a.circuit

@[simp] theorem size_run {X : Type*} (a : OrderedMatrixAlgorithm R L M N)
    (bank : CircuitFamily R X ((L × M) ⊕ (M × N))) :
    (a.run bank).size = bank.size + a.size :=
  CircuitFamily.size_substitute bank a.circuit

theorem polynomial_run {X : Type*} (a : OrderedMatrixAlgorithm R L M N)
    (bank : CircuitFamily R X ((L × M) ⊕ (M × N))) (l : L) (n : N) :
    (a.run bank).polynomial (l, n) =
      ∑ m, bank.polynomial (Sum.inl (l, m)) * bank.polynomial (Sum.inr (m, n)) := by
  rw [run, CircuitFamily.polynomial_substitute, a.correct]
  simp

theorem polynomial_run_eq_mul {X : Type*} (a : OrderedMatrixAlgorithm R L M N)
    (bank : CircuitFamily R X ((L × M) ⊕ (M × N))) (l : L) (n : N) :
    (a.run bank).polynomial (l, n) =
      (Matrix.of (fun l m => bank.polynomial (Sum.inl (l, m))) *
        Matrix.of (fun m n => bank.polynomial (Sum.inr (m, n)))) l n := by
  exact a.polynomial_run bank l n

def appendUsing {X O : Type*} (a : OrderedMatrixAlgorithm R L M N)
    (bank : CircuitFamily R X O) (inputs : ((L × M) ⊕ (M × N)) → O) :
    CircuitFamily R X (O ⊕ (L × N)) :=
  bank.extendUsing inputs a.circuit

@[simp] theorem size_appendUsing {X O : Type*} (a : OrderedMatrixAlgorithm R L M N)
    (bank : CircuitFamily R X O) (inputs : ((L × M) ⊕ (M × N)) → O) :
    (a.appendUsing bank inputs).size = bank.size + a.size :=
  CircuitFamily.size_extendUsing bank inputs a.circuit

@[simp] theorem polynomial_appendUsing_old {X O : Type*}
    (a : OrderedMatrixAlgorithm R L M N) (bank : CircuitFamily R X O)
    (inputs : ((L × M) ⊕ (M × N)) → O) (o : O) :
    (a.appendUsing bank inputs).polynomial (Sum.inl o) = bank.polynomial o :=
  CircuitFamily.polynomial_extendUsing_inl bank inputs a.circuit o

theorem polynomial_appendUsing_new {X O : Type*}
    (a : OrderedMatrixAlgorithm R L M N) (bank : CircuitFamily R X O)
    (inputs : ((L × M) ⊕ (M × N)) → O) (l : L) (n : N) :
    (a.appendUsing bank inputs).polynomial (Sum.inr (l, n)) =
      ∑ m, bank.polynomial (inputs (Sum.inl (l, m))) *
        bank.polynomial (inputs (Sum.inr (m, n))) := by
  rw [appendUsing, CircuitFamily.polynomial_extendUsing_inr, a.correct]
  simp

end OrderedMatrixAlgorithm

namespace FourProducts

variable {R X O ρ J K : Type*} [CommSemiring R]
variable [Fintype ρ] [Fintype J]

def build (bank : CircuitFamily R X O)
    (sa sb sc sd : ρ × J → O) (sy : J × K → O)
    (p : OrderedMatrixAlgorithm R ρ J K)
    (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J)
    (zm : OrderedMatrixAlgorithm R J ρ K) :
    CircuitFamily R X (Bool × (J × K)) :=
  let c1 := p.appendUsing bank (Sum.elim sa sy)
  let c2 := q.appendUsing c1 (Sum.elim
    (fun v => Sum.inl (sy (v.2, v.1)))
    (fun v => Sum.inl (sd (v.2, v.1))))
  let c3 := zp.appendUsing c2 (Sum.elim
    (fun v => Sum.inl (Sum.inr (v.2, v.1)))
    (fun v => Sum.inl (Sum.inl (sb v))))
  let c4 := zm.appendUsing c3 (Sum.elim
    (fun v => Sum.inl (Sum.inl (Sum.inl (sc (v.2, v.1)))))
    (fun v => Sum.inl (Sum.inr (v.2, v.1))))
  c4.reindexOutputs (fun v =>
    if v.1 then Sum.inl (Sum.inr (v.2.2, v.2.1)) else Sum.inr v.2)

theorem size_build (bank : CircuitFamily R X O)
    (sa sb sc sd : ρ × J → O) (sy : J × K → O)
    (p : OrderedMatrixAlgorithm R ρ J K)
    (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J)
    (zm : OrderedMatrixAlgorithm R J ρ K) :
    (build bank sa sb sc sd sy p q zp zm).size =
      bank.size + p.size + q.size + zp.size + zm.size := by
  simp only [build, CircuitFamily.size_reindexOutputs,
    OrderedMatrixAlgorithm.size_appendUsing]

theorem polynomial_build_true (bank : CircuitFamily R X O)
    (sa sb sc sd : ρ × J → O) (sy : J × K → O)
    (p : OrderedMatrixAlgorithm R ρ J K)
    (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J)
    (zm : OrderedMatrixAlgorithm R J ρ K) (l : J) (t : K) :
    (build bank sa sb sc sd sy p q zp zm).polynomial (true, (l, t)) =
      ∑ r, (∑ j, bank.polynomial (sa (r, j)) * bank.polynomial (sy (j, t))) *
        bank.polynomial (sb (r, l)) := by
  simp [build, OrderedMatrixAlgorithm.polynomial_appendUsing_new]

theorem polynomial_build_false (bank : CircuitFamily R X O)
    (sa sb sc sd : ρ × J → O) (sy : J × K → O)
    (p : OrderedMatrixAlgorithm R ρ J K)
    (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J)
    (zm : OrderedMatrixAlgorithm R J ρ K) (l : J) (t : K) :
    (build bank sa sb sc sd sy p q zp zm).polynomial (false, (l, t)) =
      ∑ r, bank.polynomial (sc (r, l)) *
        (∑ j, bank.polynomial (sy (j, t)) * bank.polynomial (sd (r, j))) := by
  simp [build, OrderedMatrixAlgorithm.polynomial_appendUsing_new]

end FourProducts

namespace Assembly

variable {R X O : Type*}

structure State (R X O : Type*) where
  nodes : ℕ
  circuit : Circuit R X nodes
  bank : Bool → O → Fin nodes
  total : Fin nodes

def initial [Zero R] (c : CircuitFamily R X (Bool × O)) : State R X O where
  nodes := c.nodeCount + 1
  circuit := c.circuit.snoc (.scalar 0)
  bank := fun b o => (c.output (b, o)).castSucc
  total := Fin.last c.nodeCount

def step (s : State R X O) (u : O → X) (o : O) : State R X O where
  nodes := s.nodes + 4
  circuit :=
    (((s.circuit.snoc (.add (s.bank true o) (s.bank false o))).snoc (.input (u o))).snoc
      (.mul (Fin.last s.nodes).castSucc (Fin.last (s.nodes + 1)))).snoc
      (.add (Fin.castAdd 3 s.total) (Fin.last (s.nodes + 2)))
  bank := fun b p => Fin.castAdd 4 (s.bank b p)
  total := Fin.last (s.nodes + 3)

def bankValue {A : Type*} [Add A] [Mul A] (s : State R X O)
    (r : R → A) (x : X → A) (b : Bool) (o : O) : A :=
  s.circuit.eval r x (s.bank b o)

def totalValue {A : Type*} [Add A] [Mul A] (s : State R X O)
    (r : R → A) (x : X → A) : A :=
  s.circuit.eval r x s.total

private theorem castAdd_one {n : ℕ} (i : Fin n) :
    Fin.castAdd 1 i = i.castSucc := rfl

private theorem bankValue_step {A : Type*} [Add A] [Mul A]
    (s : State R X O) (u : O → X) (o p : O) (r : R → A) (x : X → A) (b : Bool) :
    bankValue (step s u o) r x b p = bankValue s r x b p := by
  simp [bankValue, step, Circuit.eval, Fin.snoc_castAdd, castAdd_one]

private theorem totalValue_step {A : Type*} [Add A] [Mul A]
    (s : State R X O) (u : O → X) (o : O) (r : R → A) (x : X → A) :
    totalValue (step s u o) r x =
      totalValue s r x + (bankValue s r x true o + bankValue s r x false o) * x (u o) := by
  simp [totalValue, bankValue, step, Circuit.eval, Gate.eval, Fin.snoc_castAdd, castAdd_one]

private theorem size_step (s : State R X O) (u : O → X) (o : O) :
    (step s u o).circuit.size = s.circuit.size + 3 := by
  simp [step, Circuit.size_snoc, Gate.cost, Nat.add_assoc]

def fold (s : State R X O) (u : O → X) : List O → State R X O
  | [] => s
  | o :: os => fold (step s u o) u os

private theorem bankValue_fold {A : Type*} [Add A] [Mul A]
    (s : State R X O) (u : O → X) (os : List O)
    (r : R → A) (x : X → A) (b : Bool) (o : O) :
    bankValue (fold s u os) r x b o = bankValue s r x b o := by
  induction os generalizing s with
  | nil => rfl
  | cons p ps ih => simp only [fold, ih, bankValue_step]

private theorem size_fold (s : State R X O) (u : O → X) (os : List O) :
    (fold s u os).circuit.size = s.circuit.size + 3 * os.length := by
  induction os generalizing s with
  | nil => simp [fold]
  | cons o os ih =>
      simp [fold, ih, size_step, Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

private theorem totalValue_fold {A : Type*} [Semiring A]
    (s : State R X O) (u : O → X) (os : List O) (r : R → A) (x : X → A) :
    totalValue (fold s u os) r x =
      totalValue s r x +
        (os.map fun o => (bankValue s r x true o + bankValue s r x false o) * x (u o)).sum := by
  induction os generalizing s with
  | nil => simp [fold]
  | cons o os ih =>
      simp only [fold, ih, totalValue_step, bankValue_step, List.map_cons, List.sum_cons]
      rw [add_assoc]

noncomputable def finish [Zero R] [Fintype O]
    (c : CircuitFamily R X (Bool × O)) (u : O → X) : CircuitFamily R X PUnit := by
  classical
  let s := fold (initial c) u (Finset.univ.toList)
  exact ⟨s.nodes, s.circuit, fun _ => s.total⟩

theorem size_finish [Zero R] [Fintype O]
    (c : CircuitFamily R X (Bool × O)) (u : O → X) :
    (finish c u).size = c.size + 3 * Fintype.card O := by
  classical
  simp [finish, CircuitFamily.size, size_fold, initial, Circuit.size_snoc, Gate.cost]

theorem eval_finish [CommSemiring R] {A : Type*} [Semiring A] [Fintype O]
    (c : CircuitFamily R X (Bool × O)) (u : O → X) (r : R →+* A) (x : X → A) :
    (finish c u).eval r x PUnit.unit =
      ∑ o, (c.eval r x (true, o) + c.eval r x (false, o)) * x (u o) := by
  classical
  change totalValue (fold (initial c) u Finset.univ.toList) r x = _
  rw [totalValue_fold]
  simp [totalValue, bankValue, initial, Gate.eval,
    CircuitFamily.eval, Finset.sum_map_toList]

theorem polynomial_finish [CommSemiring R] [Fintype O]
    (c : CircuitFamily R X (Bool × O)) (u : O → X) :
    (finish c u).polynomial PUnit.unit =
      ∑ o, (c.polynomial (true, o) + c.polynomial (false, o)) *
        FreeAlgebra.ι R (u o) :=
  eval_finish c u (algebraMap R (FreeAlgebra R X)) (FreeAlgebra.ι R)

theorem polynomial_finish_eq_orderedAssembly [CommSemiring R]
    {ρ : Type*} {J : Type*} {K : Type*} [Fintype ρ] [Fintype J] [Fintype K]
    (g : CircuitFamily R X (Bool × (J × K)))
    (a b c d : Matrix ρ J (FreeAlgebra R X)) (y u : Matrix J K X)
    (hplus : ∀ l q, g.polynomial (true, (l, q)) =
      ((a * Matrix.of (fun j q => FreeAlgebra.ι R (y j q))).transpose * b) q l)
    (hminus : ∀ l q, g.polynomial (false, (l, q)) =
      (c.transpose *
        ((Matrix.of (fun j q => FreeAlgebra.ι R (y j q))).transpose * d.transpose).transpose) l q) :
    (finish g (fun p => u p.1 p.2)).polynomial PUnit.unit =
      orderedAssembly a b c d
        (Matrix.of (fun j q => FreeAlgebra.ι R (y j q)))
        (Matrix.of (fun j q => FreeAlgebra.ι R (u j q))) := by
  rw [polynomial_finish]
  simp only [Fintype.sum_prod_type, hplus, hminus, orderedAssembly, Matrix.of_apply]

theorem size_finish_matrix [Zero R]
    {J : Type*} {K : Type*} [Fintype J] [Fintype K]
    (g : CircuitFamily R X (Bool × (J × K))) (u : Matrix J K X) :
    (finish g (fun p => u p.1 p.2)).size =
      g.size + 3 * (Fintype.card J * Fintype.card K) := by
  rw [size_finish, Fintype.card_prod]

noncomputable def compile [CommSemiring R]
    {ρ J K : Type*} [Fintype ρ] [Fintype J] [Fintype K]
    (bank : CircuitFamily R X O)
    (sa sb sc sd : ρ × J → O) (sy : J × K → O) (u : J × K → X)
    (p : OrderedMatrixAlgorithm R ρ J K)
    (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J)
    (zm : OrderedMatrixAlgorithm R J ρ K) : CircuitFamily R X PUnit :=
  finish (FourProducts.build bank sa sb sc sd sy p q zp zm) u

theorem size_compile [CommSemiring R]
    {ρ J K : Type*} [Fintype ρ] [Fintype J] [Fintype K]
    (bank : CircuitFamily R X O)
    (sa sb sc sd : ρ × J → O) (sy : J × K → O) (u : J × K → X)
    (p : OrderedMatrixAlgorithm R ρ J K)
    (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J)
    (zm : OrderedMatrixAlgorithm R J ρ K) :
    (compile bank sa sb sc sd sy u p q zp zm).size =
      bank.size + p.size + q.size + zp.size + zm.size +
        3 * (Fintype.card J * Fintype.card K) := by
  simp only [compile, size_finish, FourProducts.size_build, Fintype.card_prod]

theorem polynomial_compile_eq_orderedAssembly [CommSemiring R]
    {ρ J K : Type*} [Fintype ρ] [Fintype J] [Fintype K]
    (bank : CircuitFamily R X O)
    (sa sb sc sd : ρ × J → O) (sy : J × K → O) (y u : Matrix J K X)
    (hy : ∀ j t, bank.polynomial (sy (j, t)) = FreeAlgebra.ι R (y j t))
    (p : OrderedMatrixAlgorithm R ρ J K)
    (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J)
    (zm : OrderedMatrixAlgorithm R J ρ K) :
    (compile bank sa sb sc sd sy (fun v => u v.1 v.2) p q zp zm).polynomial PUnit.unit =
      orderedAssembly
        (Matrix.of (fun r j => bank.polynomial (sa (r, j))))
        (Matrix.of (fun r j => bank.polynomial (sb (r, j))))
        (Matrix.of (fun r j => bank.polynomial (sc (r, j))))
        (Matrix.of (fun r j => bank.polynomial (sd (r, j))))
        (Matrix.of (fun j t => FreeAlgebra.ι R (y j t)))
        (Matrix.of (fun j t => FreeAlgebra.ι R (u j t))) := by
  apply polynomial_finish_eq_orderedAssembly
  · intro l t
    rw [FourProducts.polynomial_build_true]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, hy]
  · intro l t
    rw [FourProducts.polynomial_build_false]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, hy]

end Assembly

end Lemmata.FockCircuits
