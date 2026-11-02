module

public import Lemmata.FockCircuits.Circuit
public import Mathlib.Data.List.Chain
public import Mathlib.Logic.Relation
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Order.Setoid.Basic
public import Mathlib.Tactic.Push

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Patterns

variable {α : Type*} [DecidableEq α]

inductive Step : List α → List α → Prop where
  | singleton (u v : List α) (a : α) (h : (u ++ a :: v).count a = 1) :
      Step (u ++ a :: v) (u ++ v)
  | adjacent (u v : List α) (a : α) :
      Step (u ++ a :: a :: v) (u ++ a :: v)

abbrev Reduces := Relation.ReflTransGen (Step (α := α))

def Terminal (w : List α) : Prop :=
  (∀ a ∈ w, 2 ≤ w.count a) ∧ w.IsChain (· ≠ ·)

theorem Step.length_lt {w v : List α} (h : Step w v) : v.length < w.length := by
  cases h <;> simp only [List.length_append, List.length_cons] <;> omega

theorem step_or_terminal (w : List α) : (∃ v, Step w v) ∨ Terminal w := by
  classical
  by_cases hc : ∀ a ∈ w, 2 ≤ w.count a
  · by_cases ha : w.IsChain (· ≠ ·)
    · exact Or.inr ⟨hc, ha⟩
    · rw [List.isChain_iff_forall_rel_of_append_cons_cons] at ha
      push Not at ha
      obtain ⟨a, b, u, v, hw, hab⟩ := ha
      subst b
      subst w
      exact Or.inl ⟨u ++ a :: v, Step.adjacent u v a⟩
  · push Not at hc
    obtain ⟨a, ha, hc⟩ := hc
    have hp : 0 < w.count a := List.count_pos_iff.mpr ha
    have hone : w.count a = 1 := by omega
    obtain ⟨u, v, hw⟩ := List.mem_iff_append.mp ha
    subst w
    exact Or.inl ⟨u ++ v, Step.singleton u v a hone⟩

theorem exists_terminal (w : List α) :
    ∃ v, Reduces w v ∧ Terminal v ∧ v.length ≤ w.length := by
  have aux : ∀ n, ∀ w : List α, w.length = n →
      ∃ v, Reduces w v ∧ Terminal v ∧ v.length ≤ w.length := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw
      rcases step_or_terminal w with ⟨v, hv⟩ | ht
      · have hlen := hv.length_lt
        obtain ⟨u, hred, hu, hulen⟩ := ih v.length (by omega) v rfl
        exact ⟨u, (Relation.ReflTransGen.single hv).trans hred, hu,
          hulen.trans (Nat.le_of_lt hlen)⟩
      · exact ⟨w, Relation.ReflTransGen.refl, ht, le_rfl⟩
  exact aux w.length w rfl

theorem terminal_one_false (a : α) : ¬ Terminal [a] := by
  intro h
  have hc := h.1 a (by simp)
  simp at hc

theorem terminal_two_false (a b : α) : ¬ Terminal [a, b] := by
  intro h
  have hab : a ≠ b := List.isChain_pair.mp h.2
  have hc := h.1 a (by simp)
  simp [List.count_cons, hab, Ne.symm hab] at hc

theorem terminal_three_false (a b c : α) : ¬ Terminal [a, b, c] := by
  intro h
  have hab := (List.isChain_cons_cons.mp h.2).1
  have hbc := List.isChain_pair.mp (List.isChain_cons_cons.mp h.2).2
  have hc := h.1 b (by simp)
  simp [List.count_cons, hab, Ne.symm hab, hbc, Ne.symm hbc] at hc

theorem terminal_four (a b c d : α) (h : Terminal [a, b, c, d]) :
    c = a ∧ d = b := by
  have hab := (List.isChain_cons_cons.mp h.2).1
  have hbc := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp h.2).2).1
  by_cases hca : c = a
  · subst c
    by_cases hdb : d = b
    · exact ⟨rfl, hdb⟩
    · have hc := h.1 b (by simp)
      simp [List.count_cons, hab, Ne.symm hab, hdb, Ne.symm hdb] at hc
  · by_cases hda : d = a
    · subst d
      have hc := h.1 b (by simp)
      simp [List.count_cons, hab, Ne.symm hab, hbc, Ne.symm hbc] at hc
    · have hc := h.1 a (by simp)
      simp [List.count_cons, hab, Ne.symm hab, hca, Ne.symm hca,
        hda, Ne.symm hda] at hc

theorem terminal_five (a b c d e : α) (h : Terminal [a, b, c, d, e]) :
    c = a ∧ d = b ∧ e = a := by
  have hab := (List.isChain_cons_cons.mp h.2).1
  have hbc := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp h.2).2).1
  have hcd := (List.isChain_cons_cons.mp
    (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp h.2).2).2).1
  have hde := List.isChain_pair.mp (List.isChain_cons_cons.mp
    (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp h.2).2).2).2
  by_cases hca : c = a
  · subst c
    by_cases hdb : d = b
    · subst d
      by_cases hea : e = a
      · exact ⟨rfl, rfl, hea⟩
      · have hc := h.1 e (by simp)
        simp [List.count_cons, hea, Ne.symm hea, hde, Ne.symm hde] at hc
    · by_cases heb : e = b
      · subst e
        have hc := h.1 d (by simp)
        simp [List.count_cons, hcd, Ne.symm hcd, hdb, Ne.symm hdb] at hc
      · have hc := h.1 b (by simp)
        simp [List.count_cons, hab, Ne.symm hab, hdb, Ne.symm hdb,
          heb, Ne.symm heb] at hc
  · by_cases hda : d = a
    · subst d
      by_cases heb : e = b
      · subst e
        have hc := h.1 c (by simp)
        simp [List.count_cons, hca, Ne.symm hca, hbc, Ne.symm hbc] at hc
      · have hc := h.1 b (by simp)
        simp [List.count_cons, hab, Ne.symm hab, hbc, Ne.symm hbc,
          heb, Ne.symm heb] at hc
    · by_cases hea : e = a
      · subst e
        by_cases hdb : d = b
        · subst d
          have hc := h.1 c (by simp)
          simp [List.count_cons, hca, Ne.symm hca, hbc, Ne.symm hbc] at hc
        · have hc := h.1 b (by simp)
          simp [List.count_cons, hab, Ne.symm hab, hbc, Ne.symm hbc,
            hdb, Ne.symm hdb] at hc
      · have hc := h.1 a (by simp)
        simp [List.count_cons, hab, Ne.symm hab, hca, Ne.symm hca,
          hda, Ne.symm hda, hea, Ne.symm hea] at hc

def Core (w : List α) : Prop :=
  w = [] ∨ ∃ a b, a ≠ b ∧ (w = [a, b, a, b] ∨ w = [a, b, a, b, a])

theorem terminal_core {w : List α} (h : Terminal w) (hlen : w.length ≤ 5) : Core w := by
  rcases w with _ | ⟨a, w⟩
  · exact Or.inl rfl
  rcases w with _ | ⟨b, w⟩
  · exact False.elim (terminal_one_false a h)
  rcases w with _ | ⟨c, w⟩
  · exact False.elim (terminal_two_false a b h)
  rcases w with _ | ⟨d, w⟩
  · exact False.elim (terminal_three_false a b c h)
  rcases w with _ | ⟨e, w⟩
  · obtain ⟨hca, hdb⟩ := terminal_four a b c d h
    subst c
    subst d
    exact Or.inr ⟨a, b, (List.isChain_cons_cons.mp h.2).1, Or.inl rfl⟩
  rcases w with _ | ⟨f, w⟩
  · obtain ⟨hca, hdb, hea⟩ := terminal_five a b c d e h
    subst c
    subst d
    subst e
    exact Or.inr ⟨a, b, (List.isChain_cons_cons.mp h.2).1, Or.inr rfl⟩
  · simp only [List.length_cons] at hlen
    omega

theorem reduces_to_core {w : List α} (h : w.length ≤ 5) :
    ∃ v, Reduces w v ∧ Core v := by
  obtain ⟨v, hv, ht, hlen⟩ := exists_terminal w
  exact ⟨v, hv, terminal_core ht (hlen.trans h)⟩

theorem substitute_circuit {R X Y : Type*} [CommSemiring R]
    {p : FreeAlgebra R X} {s : ℕ} (h : HasCircuit p s)
    (c : CircuitFamily R Y X) :
    HasCircuit (FreeAlgebra.lift R c.polynomial p) (c.size + s) := by
  obtain ⟨n, d, i, hp, hs⟩ := h
  let one : CircuitFamily R X Unit := ⟨n, d, fun _ => i⟩
  refine ⟨(c.substitute one).nodeCount, (c.substitute one).circuit,
    (c.substitute one).output (), ?_, ?_⟩
  · change (c.substitute one).polynomial () = _
    rw [CircuitFamily.polynomial_substitute]
    exact congrArg (FreeAlgebra.lift R c.polynomial) hp
  · change (c.substitute one).size ≤ _
    rw [CircuitFamily.size_substitute]
    exact Nat.add_le_add_left hs c.size

def SamePattern {I X : Type*} (u v : I → X) : Prop :=
  ∀ i j, u i = u j ↔ v i = v j

theorem samePattern_iff_permutation {I X : Type*} [Finite I] (u v : I → X) :
    SamePattern u v ↔ ∃ σ : Equiv.Perm X, ∀ i, σ (u i) = v i := by
  classical
  constructor
  · intro h
    let B := Set.range u
    haveI : Finite B := Finite.of_surjective _ (Set.codRestrict_range_surjective u)
    let get : B → I := fun b => Classical.choose b.property
    have hget (b : B) : u (get b) = b.val := Classical.choose_spec b.property
    let target : B → X := fun b => v (get b)
    have hinj : Function.Injective target := by
      intro a b hab
      apply Subtype.ext
      calc
        a.val = u (get a) := (hget a).symm
        _ = u (get b) := (h (get a) (get b)).mpr hab
        _ = b.val := hget b
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
      (fun b : B => b.val) target Subtype.val_injective hinj
    refine ⟨σ, fun i => ?_⟩
    let b : B := ⟨u i, ⟨i, rfl⟩⟩
    calc
      σ (u i) = v (get b) := hσ b
      _ = v i := (h (get b) i).mp (hget b)
  · rintro ⟨σ, hσ⟩ i j
    constructor
    · intro hij
      rw [← hσ i, ← hσ j, hij]
    · intro hij
      apply σ.injective
      rw [hσ i, hσ j]
      exact hij

noncomputable instance setoidFintype (I : Type*) [Fintype I] : Fintype (Setoid I) := by
  classical
  apply Fintype.ofInjective (fun p : Setoid I => p.r)
  intro p q hpq
  apply Setoid.ext
  intro i j
  exact iff_of_eq (congrFun (congrFun hpq i) j)

end Lemmata.FockCircuits.Patterns
