module

public import Lemmata.FockCircuits.Patterns
public import Lemmata.FockCircuits.Matrix.CircuitBuilders

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.Patterns

open Lemmata.FockCircuits.Matrix

variable {R P C : Type*} [CommSemiring R] [DecidableEq P]

abbrev Extended (P C : Type*) := (P ⊕ Unit) × C

def oldVariable (z : P × C) : Extended P C := (Sum.inl z.1, z.2)

def newVariable (i : C) : Extended P C := (Sum.inr (), i)

noncomputable def word {X : Type*} (w : List X) : FreeAlgebra R X :=
  (w.map (FreeAlgebra.ι R)).prod

@[simp] theorem word_nil {X : Type*} : word (R := R) ([] : List X) = 1 := rfl

@[simp] theorem word_cons {X : Type*} (x : X) (w : List X) :
    word (R := R) (x :: w) = FreeAlgebra.ι R x * word w := rfl

@[simp] theorem word_append {X : Type*} (u v : List X) :
    word (R := R) (u ++ v) = word u * word v := by
  simp only [word, List.map_append, List.prod_append]

noncomputable def singletonSubstitution [Fintype C] (p : P) (z : P × C) :
    FreeAlgebra R (Extended P C) :=
  if z.1 = p then FreeAlgebra.ι R (oldVariable z) * ∑ i : C, FreeAlgebra.ι R (newVariable i)
  else FreeAlgebra.ι R (oldVariable z)

noncomputable def adjacentSubstitution (p : P) (z : P × C) :
    FreeAlgebra R (Extended P C) :=
  if z.1 = p then FreeAlgebra.ι R (oldVariable z) * FreeAlgebra.ι R (newVariable z.2)
  else FreeAlgebra.ι R (oldVariable z)

theorem lift_word_unmarked {X : Type*} (f : P × C → FreeAlgebra R X)
    (g : P × C → X) (p : P) (w : List (P × C))
    (h : ∀ z ∈ w, z.1 ≠ p) (hf : ∀ z, z.1 ≠ p → f z = FreeAlgebra.ι R (g z)) :
    FreeAlgebra.lift R f (word w) = word (w.map g) := by
  simp only [word, map_list_prod, List.map_map, Function.comp_def, FreeAlgebra.lift_ι_apply]
  apply congrArg List.prod
  apply List.map_congr_left
  intro z hz
  exact hf z (h z hz)

theorem singleton_insertion [Fintype C] (p : P) (i : C) (u v : List (P × C))
    (hu : ∀ z ∈ u, z.1 ≠ p) (hv : ∀ z ∈ v, z.1 ≠ p) :
    FreeAlgebra.lift R (singletonSubstitution (R := R) p) (word (u ++ (p, i) :: v)) =
      ∑ j : C, word (u.map oldVariable ++ oldVariable (p, i) :: newVariable j :: v.map oldVariable) := by
  rw [word_append, word_cons, map_mul, map_mul, FreeAlgebra.lift_ι_apply]
  rw [lift_word_unmarked _ oldVariable p u hu
      (fun z hz => by simp only [singletonSubstitution, hz, ite_false]),
    lift_word_unmarked _ oldVariable p v hv
      (fun z hz => by simp only [singletonSubstitution, hz, ite_false])]
  simp only [singletonSubstitution, ite_true, word_append, word_cons,
    mul_assoc, Finset.sum_mul, Finset.mul_sum]

theorem adjacent_expansion (p : P) (i : C) (u v : List (P × C))
    (hu : ∀ z ∈ u, z.1 ≠ p) (hv : ∀ z ∈ v, z.1 ≠ p) :
    FreeAlgebra.lift R (adjacentSubstitution (R := R) p) (word (u ++ (p, i) :: v)) =
      word (u.map oldVariable ++ oldVariable (p, i) :: newVariable i :: v.map oldVariable) := by
  rw [word_append, word_cons, map_mul, map_mul, FreeAlgebra.lift_ι_apply]
  rw [lift_word_unmarked _ oldVariable p u hu
      (fun z hz => by simp only [adjacentSubstitution, hz, ite_false]),
    lift_word_unmarked _ oldVariable p v hv
      (fun z hz => by simp only [adjacentSubstitution, hz, ite_false])]
  simp only [adjacentSubstitution, ite_true, word_append, word_cons, mul_assoc]

noncomputable def oldInputs [Fintype P] [Fintype C] :
    CircuitFamily R (Extended P C) (P × C) :=
  CircuitBuilders.family fun z => CircuitBuilders.input (oldVariable z)

noncomputable def singletonSum [Fintype C] : CircuitFamily R (Extended P C) Unit :=
  CircuitBuilders.linear (fun _ : C => (1 : R)) newVariable

noncomputable def singletonProducts [Fintype P] [Fintype C] (p : P) :
    CircuitFamily R ((P × C) ⊕ Unit) (P × C) :=
  CircuitBuilders.family fun z =>
    if z.1 = p then CircuitBuilders.mul (CircuitBuilders.input (Sum.inl z))
      (CircuitBuilders.input (Sum.inr ())) else CircuitBuilders.input (Sum.inl z)

noncomputable def singletonInsertion [Fintype P] [Fintype C] (p : P) :
    CircuitFamily R (Extended P C) (P × C) :=
  (oldInputs.combine singletonSum).substitute (singletonProducts p)

theorem size_oldInputs [Fintype P] [Fintype C] :
    (oldInputs (R := R) (P := P) (C := C)).size = 0 := by
  simp [oldInputs]

theorem size_singletonProducts [Fintype P] [Fintype C] (p : P) :
    (singletonProducts (R := R) (C := C) p).size = Fintype.card C := by
  classical
  rw [singletonProducts, CircuitBuilders.size_family]
  calc
    _ = ∑ z : P × C, if z.1 = p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      split_ifs <;> simp
    _ = Fintype.card C := by
      rw [Fintype.sum_prod_type]
      calc
        _ = ∑ x : P, if x = p then Fintype.card C else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxp : x = p <;> simp [hxp]
        _ = _ := by simp

theorem size_singletonInsertion [Fintype P] [Fintype C] (p : P) :
    (singletonInsertion (R := R) (C := C) p).size = 3 * Fintype.card C := by
  rw [singletonInsertion, CircuitFamily.size_substitute, CircuitFamily.size_combine,
    size_oldInputs, size_singletonProducts]
  simp [singletonSum]
  omega

theorem eval_singletonInsertion [Fintype P] [Fintype C]
    {A : Type*} [Semiring A] [Algebra R A] (p : P)
    (x : Extended P C → A) (z : P × C) :
    (singletonInsertion (R := R) p).eval (algebraMap R A) x z =
      if z.1 = p then x (oldVariable z) * ∑ i : C, x (newVariable i)
      else x (oldVariable z) := by
  classical
  rw [singletonInsertion, CircuitFamily.eval_substitute]
  simp only [singletonProducts, CircuitBuilders.eval_family]
  by_cases hz : z.1 = p
  · simp [hz, oldInputs, singletonSum, CircuitBuilders.eval_linear]
  · simp [hz, oldInputs]

theorem polynomial_singletonInsertion [Fintype P] [Fintype C] (p : P) (z : P × C) :
    (singletonInsertion (R := R) p).polynomial z = singletonSubstitution (R := R) p z :=
  eval_singletonInsertion p (FreeAlgebra.ι R) z

noncomputable def adjacentExpansion [Fintype P] [Fintype C] (p : P) :
    CircuitFamily R (Extended P C) (P × C) :=
  CircuitBuilders.family fun z =>
    if z.1 = p then CircuitBuilders.mul (CircuitBuilders.input (oldVariable z))
      (CircuitBuilders.input (newVariable z.2)) else CircuitBuilders.input (oldVariable z)

theorem size_adjacentExpansion [Fintype P] [Fintype C] (p : P) :
    (adjacentExpansion (R := R) (C := C) p).size = Fintype.card C := by
  classical
  rw [adjacentExpansion, CircuitBuilders.size_family]
  calc
    _ = ∑ z : P × C, if z.1 = p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      split_ifs <;> simp
    _ = Fintype.card C := by
      rw [Fintype.sum_prod_type]
      calc
        _ = ∑ x : P, if x = p then Fintype.card C else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxp : x = p <;> simp [hxp]
        _ = _ := by simp

theorem polynomial_adjacentExpansion [Fintype P] [Fintype C] (p : P) (z : P × C) :
    (adjacentExpansion (R := R) p).polynomial z = adjacentSubstitution (R := R) p z := by
  classical
  change (adjacentExpansion p).eval
    (algebraMap R (FreeAlgebra R (Extended P C))) (FreeAlgebra.ι R) z = _
  by_cases hz : z.1 = p <;> simp [adjacentExpansion, adjacentSubstitution, hz]

theorem singletonInsertion_hasCircuit [Fintype P] [Fintype C] (p : P)
    {f : FreeAlgebra R (P × C)} {s : ℕ} (hf : HasCircuit f s) :
    HasCircuit (FreeAlgebra.lift R (singletonSubstitution (R := R) p) f)
      (3 * Fintype.card C + s) := by
  have h := substitute_circuit hf (singletonInsertion (R := R) (C := C) p)
  have hp : (singletonInsertion (R := R) (C := C) p).polynomial = singletonSubstitution (R := R) p := by
    funext z
    exact polynomial_singletonInsertion p z
  simpa only [hp, size_singletonInsertion] using h

theorem adjacentExpansion_hasCircuit [Fintype P] [Fintype C] (p : P)
    {f : FreeAlgebra R (P × C)} {s : ℕ} (hf : HasCircuit f s) :
    HasCircuit (FreeAlgebra.lift R (adjacentSubstitution (R := R) p) f)
      (Fintype.card C + s) := by
  have h := substitute_circuit hf (adjacentExpansion (R := R) (C := C) p)
  have hp : (adjacentExpansion (R := R) (C := C) p).polynomial = adjacentSubstitution (R := R) p := by
    funext z
    exact polynomial_adjacentExpansion p z
  simpa only [hp, size_adjacentExpansion] using h

noncomputable def pattern {B : Type*} [Fintype B] [DecidableEq B] [Fintype C]
    (w : List (B × P)) : FreeAlgebra R (P × C) :=
  ∑ f : B → C, word (w.map fun z => (z.2, f z.1))

theorem sum_split_label {B A : Type*} [Fintype B] [DecidableEq B] [Fintype C]
    [AddCommMonoid A] (a : B) (f : (B → C) → A) :
    (∑ g : B → C, f g) =
      ∑ i : C, ∑ g : {b : B // b ≠ a} → C,
        f ((Equiv.funSplitAt a C).symm (i, g)) := by
  classical
  simpa only [Fintype.sum_prod_type] using ((Equiv.funSplitAt a C).symm.sum_comp f).symm

theorem split_label_same {B : Type*} [DecidableEq B] (a : B)
    (i : C) (g : {b : B // b ≠ a} → C) :
    (Equiv.funSplitAt a C).symm (i, g) a = i := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

theorem split_label_other {B : Type*} [DecidableEq B] (a : B)
    (i : C) (g : {b : B // b ≠ a} → C) (b : {b : B // b ≠ a}) :
    (Equiv.funSplitAt a C).symm (i, g) b.val = g b := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt, b.property]

theorem singleton_pattern {B : Type*} [Fintype B] [DecidableEq B] [Fintype C]
    (a : B) (b : {b : B // b ≠ a}) (p : P)
    (u v : List ({b : B // b ≠ a} × P))
    (hu : ∀ z ∈ u, z.2 ≠ p) (hv : ∀ z ∈ v, z.2 ≠ p) :
    FreeAlgebra.lift R (singletonSubstitution (R := R) p)
        (pattern (R := R) (C := C) (u ++ (b, p) :: v)) =
      pattern (R := R) (C := C)
        ((u.map fun z => (z.1.val, Sum.inl z.2)) ++
          (b.val, Sum.inl p) :: (a, Sum.inr ()) ::
            v.map (fun z => (z.1.val, Sum.inl z.2))) := by
  classical
  unfold pattern
  rw [map_sum]
  calc
    _ = ∑ g : {b : B // b ≠ a} → C, ∑ i : C,
        word ((u.map fun z => (Sum.inl z.2, g z.1)) ++
          (Sum.inl p, g b) :: (Sum.inr (), i) ::
            v.map (fun z => (Sum.inl z.2, g z.1))) := by
      apply Finset.sum_congr rfl
      intro g hg
      have hu' : ∀ z ∈ u.map (fun z => (z.2, g z.1)), z.1 ≠ p := by
        intro z hz
        obtain ⟨x, hx, hxz⟩ := List.mem_map.mp hz
        rw [← hxz]
        exact hu x hx
      have hv' : ∀ z ∈ v.map (fun z => (z.2, g z.1)), z.1 ≠ p := by
        intro z hz
        obtain ⟨x, hx, hxz⟩ := List.mem_map.mp hz
        rw [← hxz]
        exact hv x hx
      simpa only [List.map_append, List.map_cons, List.map_map,
        Function.comp_def, oldVariable, newVariable] using
        singleton_insertion (R := R) p (g b)
          (u.map fun z => (z.2, g z.1)) (v.map fun z => (z.2, g z.1)) hu' hv'
    _ = ∑ i : C, ∑ g : {b : B // b ≠ a} → C,
        word ((u.map fun z => (Sum.inl z.2, g z.1)) ++
          (Sum.inl p, g b) :: (Sum.inr (), i) ::
            v.map (fun z => (Sum.inl z.2, g z.1))) := Finset.sum_comm
    _ = _ := by
      rw [sum_split_label a]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro g hg
      simp only [List.map_append, List.map_cons, List.map_map,
        Function.comp_def, split_label_other, split_label_same]

theorem adjacent_pattern {B : Type*} [Fintype B] [DecidableEq B] [Fintype C]
    (b : B) (p : P) (u v : List (B × P))
    (hu : ∀ z ∈ u, z.2 ≠ p) (hv : ∀ z ∈ v, z.2 ≠ p) :
    FreeAlgebra.lift R (adjacentSubstitution (R := R) p)
        (pattern (R := R) (C := C) (u ++ (b, p) :: v)) =
      pattern (R := R) (C := C)
        ((u.map fun z => (z.1, Sum.inl z.2)) ++
          (b, Sum.inl p) :: (b, Sum.inr ()) ::
            v.map (fun z => (z.1, Sum.inl z.2))) := by
  classical
  unfold pattern
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  have hu' : ∀ z ∈ u.map (fun z => (z.2, g z.1)), z.1 ≠ p := by
    intro z hz
    obtain ⟨x, hx, hxz⟩ := List.mem_map.mp hz
    rw [← hxz]
    exact hu x hx
  have hv' : ∀ z ∈ v.map (fun z => (z.2, g z.1)), z.1 ≠ p := by
    intro z hz
    obtain ⟨x, hx, hxz⟩ := List.mem_map.mp hz
    rw [← hxz]
    exact hv x hx
  simpa only [List.map_append, List.map_cons, List.map_map,
    Function.comp_def, oldVariable, newVariable] using
    adjacent_expansion (R := R) p (g b)
      (u.map fun z => (z.2, g z.1)) (v.map fun z => (z.2, g z.1)) hu' hv'

theorem rename_hasCircuit {X Y : Type*} (f : X → Y)
    {p : FreeAlgebra R X} {s : ℕ} (h : HasCircuit p s) :
    HasCircuit (FreeAlgebra.lift R (fun x => FreeAlgebra.ι R (f x)) p) s := by
  obtain ⟨n, c, i, hp, hs⟩ := h
  refine ⟨n, c.mapInputs f, i, ?_, ?_⟩
  · rw [← hp, Circuit.polynomial_lift]
    change (c.mapInputs f).eval (algebraMap R (FreeAlgebra R Y)) (FreeAlgebra.ι R) i = _
    exact congrFun (Circuit.eval_mapInputs f
      (algebraMap R (FreeAlgebra R Y)) (FreeAlgebra.ι R) c) i
  · simpa only [Circuit.size_mapInputs] using hs

theorem pattern_mapRows {B Q : Type*} [Fintype B] [DecidableEq B] [Fintype C]
    (f : P → Q) (w : List (B × P)) :
    FreeAlgebra.lift R (fun z : P × C => FreeAlgebra.ι R (f z.1, z.2))
        (pattern (R := R) (C := C) w) =
      pattern (R := R) (C := C) (w.map fun z => (z.1, f z.2)) := by
  classical
  simp only [pattern, map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  simp only [word, map_list_prod, List.map_map, Function.comp_def, FreeAlgebra.lift_ι_apply]

theorem pattern_nil {B : Type*} [Fintype B] [DecidableEq B] [Fintype C] :
    pattern (R := R) (C := C) ([] : List (B × P)) =
      algebraMap R (FreeAlgebra R (P × C)) (Fintype.card (B → C) : R) := by
  classical
  simp [pattern]

theorem pattern_nil_hasCircuit {B : Type*} [Fintype B] [DecidableEq B] [Fintype C] :
    HasCircuit (pattern (R := R) (C := C) ([] : List (B × P))) 0 := by
  classical
  rw [pattern_nil]
  exact HasCircuit.scalar _

theorem singleton_first_pattern {B : Type*} [Fintype B] [DecidableEq B] [Fintype C]
    (a : B) (w : List ({b : B // b ≠ a} × P)) :
    pattern (R := R) (C := C)
        ((a, Sum.inr ()) :: w.map (fun z => (z.1.val, Sum.inl z.2))) =
      (∑ i : C, FreeAlgebra.ι R (newVariable (P := P) i)) *
        FreeAlgebra.lift R (fun z => FreeAlgebra.ι R (oldVariable z))
          (pattern (R := R) (C := C) w) := by
  classical
  unfold pattern
  rw [sum_split_label a, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  simp only [List.map_cons, List.map_map, Function.comp_def,
    split_label_same, split_label_other, word_cons, newVariable, word,
    map_list_prod, FreeAlgebra.lift_ι_apply, oldVariable, List.prod_cons]

theorem singletonSum_hasCircuit [Fintype C] :
    HasCircuit (∑ i : C, FreeAlgebra.ι R (newVariable (P := P) i))
      (2 * Fintype.card C) := by
  let c := singletonSum (R := R) (P := P) (C := C)
  refine ⟨c.nodeCount, c.circuit, c.output (), ?_, ?_⟩
  · change c.polynomial () = _
    simp only [c, CircuitFamily.polynomial, singletonSum, CircuitBuilders.eval_linear, one_smul]
  · change c.size ≤ _
    simp [c, singletonSum]

theorem singleton_first_hasCircuit [Fintype C]
    {f : FreeAlgebra R (P × C)} {s : ℕ} (h : HasCircuit f s) :
    HasCircuit ((∑ i : C, FreeAlgebra.ι R (newVariable (P := P) i)) *
      FreeAlgebra.lift R (fun z => FreeAlgebra.ι R (oldVariable z)) f)
      (2 * Fintype.card C + s + 1) :=
  singletonSum_hasCircuit.mul (rename_hasCircuit oldVariable h)

end Lemmata.FockCircuits.Patterns
