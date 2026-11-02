module

public import Lemmata.FockCircuits.Circuit

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.SparseCircuit

variable {R X D : Type*}

def addScaled (i j : D) (a : R) : CircuitFamily R D PUnit.{1} where
  nodeCount := 5
  circuit := (((((Circuit.nil.snoc (.input i)).snoc (.input j)).snoc (.scalar a)).snoc
    (.mul 1 2)).snoc (.add 0 3))
  output := fun _ => 4

@[simp] theorem size_addScaled (i j : D) (a : R) : (addScaled i j a).size = 2 := rfl

@[simp] theorem eval_addScaled {A : Type*} [Add A] [Mul A]
    (i j : D) (a : R) (r : R → A) (x : D → A) :
    (addScaled i j a).eval r x PUnit.unit = x i + x j * r a := rfl

def step [DecidableEq D] (bank : CircuitFamily R X (D ⊕ D))
    (source target : D) (a : R) : CircuitFamily R X (D ⊕ D) :=
  (bank.extendUsing (fun b : Bool => if b then Sum.inl source else Sum.inr target)
    (addScaled false true a)).reindexOutputs (Sum.elim
      (fun i => Sum.inl (Sum.inl i))
      (fun i => if i = target then Sum.inr PUnit.unit else Sum.inl (Sum.inr i)))

@[simp] theorem size_step [DecidableEq D] (bank : CircuitFamily R X (D ⊕ D))
    (source target : D) (a : R) :
    (step bank source target a).size = bank.size + 2 := by
  simp [step]

@[simp] theorem eval_step_input [DecidableEq D] {A : Type*} [Add A] [Mul A]
    (bank : CircuitFamily R X (D ⊕ D)) (source target : D) (a : R)
    (r : R → A) (x : X → A) (i : D) :
    (step bank source target a).eval r x (Sum.inl i) = bank.eval r x (Sum.inl i) := by
  simp [step]

theorem eval_step_output [DecidableEq D] {A : Type*} [Add A] [Mul A]
    (bank : CircuitFamily R X (D ⊕ D)) (source target : D) (a : R)
    (r : R → A) (x : X → A) (i : D) :
    (step bank source target a).eval r x (Sum.inr i) =
      if i = target then bank.eval r x (Sum.inr i) + bank.eval r x (Sum.inl source) * r a
      else bank.eval r x (Sum.inr i) := by
  by_cases hi : i = target <;> simp [step, hi]

def run [DecidableEq D] (bank : CircuitFamily R X (D ⊕ D)) :
    List (D × D × R) → CircuitFamily R X (D ⊕ D)
  | [] => bank
  | a :: rest => run (step bank a.1 a.2.1 a.2.2) rest

theorem size_run [DecidableEq D] (bank : CircuitFamily R X (D ⊕ D))
    (steps : List (D × D × R)) :
    (run bank steps).size = bank.size + 2 * steps.length := by
  induction steps generalizing bank with
  | nil => simp [run]
  | cons a rest ih => rw [run, ih, size_step]; simp [List.length_cons]; omega

@[simp] theorem eval_run_input [DecidableEq D] {A : Type*} [Add A] [Mul A]
    (bank : CircuitFamily R X (D ⊕ D)) (steps : List (D × D × R))
    (r : R → A) (x : X → A) (i : D) :
    (run bank steps).eval r x (Sum.inl i) = bank.eval r x (Sum.inl i) := by
  induction steps generalizing bank with
  | nil => rfl
  | cons a rest ih => rw [run, ih, eval_step_input]

theorem eval_run_output [DecidableEq D] {A : Type*} [Semiring A]
    (bank : CircuitFamily R X (D ⊕ D)) (steps : List (D × D × R))
    (r : R → A) (x : X → A) (i : D) :
    (run bank steps).eval r x (Sum.inr i) = bank.eval r x (Sum.inr i) +
      (steps.map fun a => if i = a.2.1 then bank.eval r x (Sum.inl a.1) * r a.2.2 else 0).sum := by
  induction steps generalizing bank with
  | nil => simp [run]
  | cons a rest ih =>
    rw [run, ih, eval_step_output]
    simp only [eval_step_input, List.map_cons, List.sum_cons]
    by_cases hi : i = a.2.1 <;> simp [hi, add_assoc]

noncomputable def scatter [Fintype D] [DecidableEq D]
    (bank : CircuitFamily R X D) (target : D → D) (a : D → R) : CircuitFamily R X D :=
  (run (bank.reindexOutputs (Sum.elim id id))
    (Finset.univ.toList.map fun i => (i, target i, a i))).reindexOutputs Sum.inr

@[simp] theorem size_scatter [Fintype D] [DecidableEq D]
    (bank : CircuitFamily R X D) (target : D → D) (a : D → R) :
    (scatter bank target a).size = bank.size + 2 * Fintype.card D := by
  simp [scatter, size_run]

theorem eval_scatter [Fintype D] [DecidableEq D] {A : Type*} [Semiring A]
    (bank : CircuitFamily R X D) (target : D → D) (a : D → R)
    (r : R → A) (x : X → A) (i : D) :
    (scatter bank target a).eval r x i = bank.eval r x i +
      ∑ j, if i = target j then bank.eval r x j * r (a j) else 0 := by
  simp [scatter, eval_run_output, List.map_map, Function.comp_def,
    Finset.sum_map_toList]

theorem scatter_realizes_linearMap [CommRing R] [Fintype D] [DecidableEq D]
    {M : Type*} [AddCommGroup M] [Module R M]
    (bank : CircuitFamily R X D) (target : D → D) (a : D → R)
    (x : X → R) (b : D → M) (T : M →ₗ[R] M)
    (hT : ∀ j, T (b j) = b j + a j • b (target j)) :
    (∑ i, (scatter bank target a).eval id x i • b i) =
      T (∑ j, bank.eval id x j • b j) := by
  simp only [map_sum, map_smul, hT, smul_add, smul_smul,
    Finset.sum_add_distrib, eval_scatter, id_eq, add_smul, Finset.sum_smul]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [ite_smul, eq_comm]

theorem scatter_matrix [CommSemiring R] [Fintype D] [DecidableEq D]
    {A : Type*} [Semiring A] [Algebra R A]
    (bank : CircuitFamily R X D) (target : D → D) (a : D → R)
    (x : X → A) (T : D → D → R)
    (hT : ∀ i j, T i j =
      (if j = i then 1 else 0) + if i = target j then a j else 0) (i : D) :
    (scatter bank target a).eval (algebraMap R A) x i =
      ∑ j, bank.eval (algebraMap R A) x j * algebraMap R A (T i j) := by
  have ht (j : D) :
      bank.eval (algebraMap R A) x j * algebraMap R A (T i j) =
        (if j = i then bank.eval (algebraMap R A) x j else 0) +
        if i = target j then bank.eval (algebraMap R A) x j * algebraMap R A (a j)
        else 0 := by
    rw [hT, map_add, mul_add]
    by_cases hji : j = i
    · by_cases hit : i = target j
      · simp only [ite_eq_left hji, ite_eq_left hit, map_one, mul_one]
      · simp only [ite_eq_left hji, ite_eq_right hit, map_one, map_zero,
          mul_one, mul_zero, add_zero]
    · by_cases hit : i = target j
      · simp only [ite_eq_right hji, ite_eq_left hit, map_one, map_zero,
          mul_one, mul_zero, zero_add]
      · simp only [ite_eq_right hji, ite_eq_right hit, map_zero, mul_zero, add_zero]
  simp_rw [ht]
  rw [Finset.sum_add_distrib, eval_scatter]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

set_option backward.isDefEq.respectTransparency false in
theorem scatter_basis_matrix [CommRing R] [Fintype D] [DecidableEq D]
    {E M A : Type*} [AddCommGroup M] [Module R M] [Semiring A] [Algebra R A]
    (b : Module.Basis E R M) (index : D → E) (hindex : Function.Injective index)
    (T : M →ₗ[R] M) (bank : CircuitFamily R X D) (target : D → D) (a : D → R)
    (hT : ∀ j, T (b (index j)) = b (index j) + a j • b (index (target j)))
    (x : X → A) (i : D) :
    (scatter bank target a).eval (algebraMap R A) x i =
      ∑ j, bank.eval (algebraMap R A) x j * algebraMap R A (b.repr (T (b (index j))) (index i)) := by
  classical
  apply scatter_matrix
  intro k j
  simp [hT, Finsupp.single_apply, hindex.eq_iff, eq_comm]

noncomputable def gather [Fintype D] [DecidableEq D]
    (bank : CircuitFamily R X D) (target : D → D) (a : D → R) : CircuitFamily R X D :=
  (run (bank.reindexOutputs (Sum.elim id id))
    (Finset.univ.toList.map fun j => (target j, j, a j))).reindexOutputs Sum.inr

@[simp] theorem size_gather [Fintype D] [DecidableEq D]
    (bank : CircuitFamily R X D) (target : D → D) (a : D → R) :
    (gather bank target a).size = bank.size + 2 * Fintype.card D := by
  simp [gather, size_run]

theorem eval_gather [Fintype D] [DecidableEq D] {A : Type*} [Semiring A]
    (bank : CircuitFamily R X D) (target : D → D) (a : D → R)
    (r : R → A) (x : X → A) (j : D) :
    (gather bank target a).eval r x j = bank.eval r x j +
      bank.eval r x (target j) * r (a j) := by
  simp [gather, eval_run_output, List.map_map, Function.comp_def,
    Finset.sum_map_toList]

theorem scatter_gather_adjoint [CommSemiring R] [Fintype D] [DecidableEq D]
    {Y A : Type*} [Semiring A] [Algebra R A]
    (left : CircuitFamily R X D) (right : CircuitFamily R Y D)
    (target : D → D) (a : D → R) (x : X → A) (y : Y → A) :
    (∑ i, (scatter left target a).eval (algebraMap R A) x i *
      right.eval (algebraMap R A) y i) =
      ∑ j, left.eval (algebraMap R A) x j *
        (gather right target a).eval (algebraMap R A) y j := by
  simp only [eval_scatter, eval_gather, add_mul, mul_add, Finset.sum_mul,
    Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [mul_assoc, Algebra.commutes (a j) (right.eval (algebraMap R A) y (target j))]

end Lemmata.FockCircuits.SparseCircuit
