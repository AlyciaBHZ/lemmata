module

public import Lemmata.FockCircuits.CrossingPadding
public import Lemmata.FockCircuits.SourceBanks

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lemmata.FockCircuits.CircuitFamily

variable {R X O P : Type*} [CommSemiring R]

@[simp] theorem polynomial_combine_inl (c : CircuitFamily R X O) (d : CircuitFamily R X P) (o : O) :
    (c.combine d).polynomial (.inl o) = c.polynomial o :=
  eval_combine_inl c d (algebraMap R (FreeAlgebra R X)) (FreeAlgebra.ι R) o

@[simp] theorem polynomial_combine_inr (c : CircuitFamily R X O) (d : CircuitFamily R X P) (p : P) :
    (c.combine d).polynomial (.inr p) = d.polynomial p :=
  eval_combine_inr c d (algebraMap R (FreeAlgebra R X)) (FreeAlgebra.ι R) p

theorem polynomial_mapInputs {Y : Type*} (c : CircuitFamily R X O) (f : X → Y) (o : O) :
    (c.mapInputs f).polynomial o =
      FreeAlgebra.lift R (fun x => FreeAlgebra.ι R (f x)) (c.polynomial o) := by
  change (c.mapInputs f).eval (algebraMap R _) (FreeAlgebra.ι R) o = _
  rw [eval_mapInputs]
  exact (c.polynomial_lift (fun x => FreeAlgebra.ι R (f x)) o).symm

end Lemmata.FockCircuits.CircuitFamily

namespace Lemmata.FockCircuits.Positional

open CrossingPadding
open scoped BigOperators

noncomputable section

variable {R X : Type*} [CommRing R]

def quartic (R : Type*) [CommSemiring R] (n : ℕ) : FreeAlgebra R (Fin 4 × Fin n) :=
  ∑ i, ∑ j, FreeAlgebra.ι R (0, i) * FreeAlgebra.ι R (1, j) *
    FreeAlgebra.ι R (2, i) * FreeAlgebra.ι R (3, j)

def quintic (R : Type*) [CommSemiring R] (n : ℕ) : FreeAlgebra R (Fin 5 × Fin n) :=
  ∑ i, ∑ j, FreeAlgebra.ι R (0, i) * FreeAlgebra.ι R (1, j) *
    FreeAlgebra.ι R (2, i) * FreeAlgebra.ι R (3, j) * FreeAlgebra.ι R (4, i)

def gridQuintic (R : Type*) [CommSemiring R] (n : ℕ) (J K : Type*) [Fintype J] [Fintype K] :
    FreeAlgebra R (Variables n J K ⊕ Fin n) :=
  ∑ i, ∑ j, ∑ k, FreeAlgebra.ι R (.inl (true, Sum.inl i)) *
    FreeAlgebra.ι R (.inl (true, Sum.inr (j, k))) * FreeAlgebra.ι R (.inl (false, Sum.inl i)) *
    FreeAlgebra.ι R (.inl (false, Sum.inr (j, k))) * FreeAlgebra.ι R (.inr i)

def colourBank {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin n ↪ J × K) (x y : Fin n → X) : CircuitFamily R X (Fin n ⊕ (J × K)) :=
  (Matrix.CircuitBuilders.family (fun i => Matrix.CircuitBuilders.input (R := R) (x i))).combine
    (SourceBanks.sourceBank e y)

@[simp] theorem size_colourBank {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin n ↪ J × K) (x y : Fin n → X) : (colourBank (R := R) e x y).size = 0 := by
  simp [colourBank, SourceBanks.size_sourceBank]

@[simp] theorem polynomial_colourBank_left {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin n ↪ J × K) (x y : Fin n → X) (i : Fin n) :
    (colourBank (R := R) e x y).polynomial (.inl i) = FreeAlgebra.ι R (x i) := by
  simp [colourBank, CircuitFamily.polynomial]

@[simp] theorem polynomial_colourBank_right {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin n ↪ J × K) (x y : Fin n → X) (j : J) (k : K) :
    (colourBank (R := R) e x y).polynomial (.inr (j, k)) =
      Function.extend e (fun i => FreeAlgebra.ι R (y i)) (fun _ => 0) (j, k) := by
  rw [colourBank, CircuitFamily.polynomial_combine_inr, SourceBanks.polynomial_sourceBank]

def labelBank {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin n ↪ J × K) (x y v u : Fin n → X) : CircuitFamily R X (Variables n J K) :=
  ((colourBank e x y).combine (colourBank e v u)).reindexOutputs
    (fun p => if p.1 then .inl p.2 else .inr p.2)

@[simp] theorem size_labelBank {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin n ↪ J × K) (x y v u : Fin n → X) : (labelBank (R := R) e x y v u).size = 0 := by
  simp [labelBank]

@[simp] theorem polynomial_labelBank_left {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin n ↪ J × K) (x y v u : Fin n → X) (b : Bool) (i : Fin n) :
    (labelBank (R := R) e x y v u).polynomial (b, .inl i) =
      FreeAlgebra.ι R (if b then x i else v i) := by
  cases b <;> simp [labelBank]

@[simp] theorem polynomial_labelBank_right {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin n ↪ J × K) (x y v u : Fin n → X) (b : Bool) (j : J) (k : K) :
    (labelBank (R := R) e x y v u).polynomial (b, .inr (j, k)) =
      Function.extend e (fun i => FreeAlgebra.ι R (if b then y i else u i)) (fun _ => 0) (j, k) := by
  cases b <;> simp [labelBank]

theorem sum_padded {A B : Type*} [Zero A] [AddCommMonoid B] {n : ℕ} {J K : Type*}
    [Fintype J] [Fintype K] (e : Fin n ↪ J × K) (y u : Fin n → A) (f : A → A → B)
    (hzero : f 0 0 = 0) :
    (∑ j, ∑ k, f (Function.extend e y (fun _ => 0) (j, k))
      (Function.extend e u (fun _ => 0) (j, k))) = ∑ i, f (y i) (u i) := by
  classical
  rw [← Fintype.sum_prod_type (fun p : J × K =>
    f (Function.extend e y (fun _ => 0) p) (Function.extend e u (fun _ => 0) p))]
  symm
  apply Fintype.sum_of_injective e e.injective
  · intro p hp
    rw [Function.extend_apply' _ _ _ hp, Function.extend_apply' _ _ _ hp]
    exact hzero
  · intro i
    rw [e.injective.extend_apply, e.injective.extend_apply]

theorem hasCircuit_quartic {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin n ↪ J × K) (c : CircuitFamily R (Variables n J K) PUnit)
    (hc : c.polynomial PUnit.unit = crossingPolynomial (R := R) n J K) :
    HasCircuit (quartic R n) c.size := by
  let b := labelBank (R := R) e (fun i => ((0 : Fin 4), i)) (fun i => ((1 : Fin 4), i))
    (fun i => ((2 : Fin 4), i)) (fun i => ((3 : Fin 4), i))
  let d := b.substitute c
  refine ⟨d.nodeCount, d.circuit, d.output PUnit.unit, ?_, ?_⟩
  · change d.polynomial PUnit.unit = _
    rw [CircuitFamily.polynomial_substitute, hc]
    simp only [crossingPolynomial, batchedCrossing, map_sum, map_mul, FreeAlgebra.lift_ι_apply,
      b, polynomial_labelBank_left, polynomial_labelBank_right, Matrix.of_apply,
      Bool.false_eq_true, ↓reduceIte]
    unfold quartic
    apply Finset.sum_congr rfl
    intro i hi
    apply sum_padded e _ _ (fun y u => FreeAlgebra.ι R ((0 : Fin 4), i) * y *
      FreeAlgebra.ι R ((2 : Fin 4), i) * u)
    simp
  · change d.size ≤ c.size
    simp [d, b]

theorem hasCircuit_quintic {n : ℕ} {J K : Type*} [Fintype J] [Fintype K]
    (e : Fin n ↪ J × K) (c : CircuitFamily R (Variables n J K ⊕ Fin n) PUnit)
    (hc : c.polynomial PUnit.unit = gridQuintic R n J K) :
    HasCircuit (quintic R n) c.size := by
  let b := labelBank (R := R) e (fun i => ((0 : Fin 5), i)) (fun i => ((1 : Fin 5), i))
    (fun i => ((2 : Fin 5), i)) (fun i => ((3 : Fin 5), i))
  let w : CircuitFamily R (Fin 5 × Fin n) (Fin n) :=
    Matrix.CircuitBuilders.family (fun i => Matrix.CircuitBuilders.input ((4 : Fin 5), i))
  let d := (b.combine w).substitute c
  refine ⟨d.nodeCount, d.circuit, d.output PUnit.unit, ?_, ?_⟩
  · change d.polynomial PUnit.unit = _
    rw [CircuitFamily.polynomial_substitute, hc]
    simp only [gridQuintic, map_sum, map_mul, FreeAlgebra.lift_ι_apply,
      CircuitFamily.polynomial_combine_inl, CircuitFamily.polynomial_combine_inr,
      b, polynomial_labelBank_left, polynomial_labelBank_right,
      Bool.false_eq_true, ↓reduceIte]
    have hw (i : Fin n) : w.polynomial i = FreeAlgebra.ι R ((4 : Fin 5), i) := by
      simp [w, CircuitFamily.polynomial]
    simp only [hw]
    unfold quintic
    apply Finset.sum_congr rfl
    intro i hi
    apply sum_padded e _ _ (fun y u => FreeAlgebra.ι R ((0 : Fin 5), i) * y *
      FreeAlgebra.ι R ((2 : Fin 5), i) * u * FreeAlgebra.ι R ((4 : Fin 5), i))
    simp
  · change d.size ≤ c.size
    simp [d, b, w]

end

end Lemmata.FockCircuits.Positional
