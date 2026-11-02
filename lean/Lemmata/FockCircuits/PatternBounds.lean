module

public import Lemmata.FockCircuits.PatternReconstruction

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.Patterns

theorem sum_two_labels {B C A : Type*} [Fintype B] [DecidableEq B] [Fintype C]
    [AddCommMonoid A] (a b : B) (hab : a ≠ b) (f : C → C → A) :
    ∃ r : ℕ, (∑ g : B → C, f (g a) (g b)) = r • ∑ i : C, ∑ j : C, f i j := by
  classical
  let b' : {x : B // x ≠ a} := ⟨b, Ne.symm hab⟩
  let D := {x : {x : B // x ≠ a} // x ≠ b'}
  refine ⟨Fintype.card (D → C), ?_⟩
  rw [sum_split_label a]
  calc
    _ = ∑ i : C, ∑ g : {x : B // x ≠ a} → C, f i (g b') := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro g hg
      rw [split_label_same]
      exact congrArg (f i) (split_label_other a i g b')
    _ = ∑ i : C, ∑ j : C, ∑ _g : D → C, f i j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sum_split_label b']
      simp [split_label_same, D, Finset.smul_sum]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Finset.smul_sum]

variable {R P C : Type*} [CommSemiring R] [Fintype C]

noncomputable def quartic (p q r s : P) : FreeAlgebra R (P × C) :=
  ∑ i : C, ∑ j : C, FreeAlgebra.ι R (p, i) * FreeAlgebra.ι R (q, j) *
    FreeAlgebra.ι R (r, i) * FreeAlgebra.ι R (s, j)

noncomputable def quintic (p q r s t : P) : FreeAlgebra R (P × C) :=
  ∑ i : C, ∑ j : C, FreeAlgebra.ι R (p, i) * FreeAlgebra.ι R (q, j) *
    FreeAlgebra.ι R (r, i) * FreeAlgebra.ι R (s, j) * FreeAlgebra.ι R (t, i)

theorem quartic_pattern {B : Type*} [Fintype B] [DecidableEq B]
    (a b : B) (hab : a ≠ b) (p q r s : P) :
    ∃ z : ℕ, pattern (R := R) (C := C) [(a, p), (b, q), (a, r), (b, s)] =
      z • quartic p q r s := by
  obtain ⟨z, hz⟩ := sum_two_labels a b hab (fun i j : C =>
    FreeAlgebra.ι R (p, i) * FreeAlgebra.ι R (q, j) *
      FreeAlgebra.ι R (r, i) * FreeAlgebra.ι R (s, j))
  refine ⟨z, ?_⟩
  simpa only [pattern, quartic, List.map_cons, List.map_nil, word_cons, word_nil,
    mul_one, mul_assoc] using hz

theorem quintic_pattern {B : Type*} [Fintype B] [DecidableEq B]
    (a b : B) (hab : a ≠ b) (p q r s t : P) :
    ∃ z : ℕ, pattern (R := R) (C := C) [(a, p), (b, q), (a, r), (b, s), (a, t)] =
      z • quintic p q r s t := by
  obtain ⟨z, hz⟩ := sum_two_labels a b hab (fun i j : C =>
    FreeAlgebra.ι R (p, i) * FreeAlgebra.ι R (q, j) *
      FreeAlgebra.ι R (r, i) * FreeAlgebra.ι R (s, j) * FreeAlgebra.ι R (t, i))
  refine ⟨z, ?_⟩
  simpa only [pattern, quintic, List.map_cons, List.map_nil, word_cons, word_nil,
    mul_one, mul_assoc] using hz

theorem nsmul_hasCircuit {X : Type*} (m : ℕ)
    {f : FreeAlgebra R X} {s : ℕ} (h : HasCircuit f s) :
    HasCircuit (m • f) (s + 1) := by
  rw [← Nat.cast_smul_eq_nsmul R m f, Algebra.smul_def]
  simpa only [zero_add] using (HasCircuit.scalar (X := X) (m : R)).mul h

theorem terminal_hasCircuit {B : Type*} [Fintype B] [DecidableEq B]
    (w : List (B × P)) (ht : Terminal (w.map Prod.fst)) (hlen : w.length ≤ 5)
    (s : ℕ) (h₄ : ∀ p q r t : P, HasCircuit (quartic (R := R) (C := C) p q r t) s)
    (h₅ : ∀ p q r t u : P, HasCircuit (quintic (R := R) (C := C) p q r t u) s) :
    HasCircuit (pattern (R := R) (C := C) w) (s + 1) := by
  classical
  rcases w with _ | ⟨⟨a, p⟩, w⟩
  · exact pattern_nil_hasCircuit.mono (Nat.zero_le _)
  rcases w with _ | ⟨⟨b, q⟩, w⟩
  · exact False.elim (terminal_one_false a ht)
  rcases w with _ | ⟨⟨c, r⟩, w⟩
  · exact False.elim (terminal_two_false a b ht)
  rcases w with _ | ⟨⟨d, t⟩, w⟩
  · exact False.elim (terminal_three_false a b c ht)
  rcases w with _ | ⟨⟨e, u⟩, w⟩
  · change Terminal [a, b, c, d] at ht
    obtain ⟨hca, hdb⟩ := terminal_four a b c d ht
    subst c
    subst d
    have hab := (List.isChain_cons_cons.mp ht.2).1
    obtain ⟨z, hz⟩ := quartic_pattern (R := R) (C := C) a b hab p q r t
    rw [hz]
    exact nsmul_hasCircuit z (h₄ p q r t)
  rcases w with _ | ⟨⟨f, v⟩, w⟩
  · change Terminal [a, b, c, d, e] at ht
    obtain ⟨hca, hdb, hea⟩ := terminal_five a b c d e ht
    subst c
    subst d
    subst e
    have hab := (List.isChain_cons_cons.mp ht.2).1
    obtain ⟨z, hz⟩ := quintic_pattern (R := R) (C := C) a b hab p q r t u
    rw [hz]
    exact nsmul_hasCircuit z (h₅ p q r t u)
  · simp only [List.length_cons] at hlen
    omega

theorem labelled_cases {B : Type*} [DecidableEq B] (w : List (B × P)) :
    (∃ u z v, w = u ++ z :: v ∧ (w.map Prod.fst).count z.1 = 1) ∨
      (∃ u z t v, w = u ++ z :: t :: v ∧ z.1 = t.1) ∨
        Terminal (w.map Prod.fst) := by
  classical
  by_cases hc : ∀ a ∈ w.map Prod.fst, 2 ≤ (w.map Prod.fst).count a
  · by_cases ha : (w.map Prod.fst).IsChain (· ≠ ·)
    · exact Or.inr (Or.inr ⟨hc, ha⟩)
    · have hchain : ¬ w.IsChain (fun z t => z.1 ≠ t.1) := by
        intro hchain
        exact ha ((List.isChain_map Prod.fst).mpr hchain)
      rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hchain
      push Not at hchain
      obtain ⟨z, t, u, v, hw, hzt⟩ := hchain
      exact Or.inr (Or.inl ⟨u, z, t, v, hw, hzt⟩)
  · push Not at hc
    obtain ⟨a, ha, hc⟩ := hc
    have hp := List.count_pos_iff.mpr ha
    have hone : (w.map Prod.fst).count a = 1 := by omega
    obtain ⟨z, hz, hza⟩ := List.mem_map.mp ha
    obtain ⟨u, v, hw⟩ := List.mem_iff_append.mp hz
    exact Or.inl ⟨u, z, v, hw, by simpa only [hza] using hone⟩

def removeLabel {B : Type*} (a : B) (w : List (B × P))
    (h : ∀ z ∈ w, z.1 ≠ a) : List ({b : B // b ≠ a} × P) :=
  w.attach.map fun z => (⟨z.val.1, h z.val z.property⟩, z.val.2)

theorem removeLabel_forget {B : Type*} (a : B) (w : List (B × P))
    (h : ∀ z ∈ w, z.1 ≠ a) :
    (removeLabel a w h).map (fun z => (z.1.val, z.2)) = w := by
  simp [removeLabel, List.map_map, Function.comp_def, List.attach_map_subtype_val]

theorem removeLabel_rows {B : Type*} (a : B) (w : List (B × P))
    (h : ∀ z ∈ w, z.1 ≠ a) :
    (removeLabel a w h).map Prod.snd = w.map Prod.snd := by
  have hf := congrArg (List.map Prod.snd) (removeLabel_forget a w h)
  simpa only [List.map_map, Function.comp_def] using hf

theorem removeLabel_length {B : Type*} (a : B) (w : List (B × P))
    (h : ∀ z ∈ w, z.1 ≠ a) : (removeLabel a w h).length = w.length := by
  have hf := congrArg List.length (removeLabel_forget a w h)
  simpa only [List.length_map] using hf

theorem removeLabel_mem {B : Type*} (a : B) (w : List (B × P))
    (h : ∀ z ∈ w, z.1 ≠ a) (z : {b : B // b ≠ a} × P)
    (hz : z ∈ removeLabel a w h) : (z.1.val, z.2) ∈ w := by
  rw [← removeLabel_forget a w h]
  exact List.mem_map.mpr ⟨z, hz, rfl⟩

theorem singleton_avoids {B : Type*} [DecidableEq B]
    (u v : List (B × P)) (a : B) (p : P)
    (h : ((u ++ (a, p) :: v).map Prod.fst).count a = 1) :
    (∀ z ∈ u, z.1 ≠ a) ∧ (∀ z ∈ v, z.1 ≠ a) := by
  have hc : (u.map Prod.fst).count a + ((v.map Prod.fst).count a + 1) = 1 := by
    simpa only [List.map_append, List.map_cons, List.count_append, List.count_cons_self] using h
  have hu : (u.map Prod.fst).count a = 0 := by omega
  have hv : (v.map Prod.fst).count a = 0 := by omega
  constructor
  · intro z hz hza
    have hp : 0 < (u.map Prod.fst).count a :=
      List.count_pos_iff.mpr (List.mem_map.mpr ⟨z, hz, hza⟩)
    omega
  · intro z hz hza
    have hp : 0 < (v.map Prod.fst).count a :=
      List.count_pos_iff.mpr (List.mem_map.mpr ⟨z, hz, hza⟩)
    omega

theorem nodup_row_parts {B : Type*} (u v : List (B × P)) (z : B × P)
    (h : ((u ++ z :: v).map Prod.snd).Nodup) :
    (∀ x ∈ u, x.2 ≠ z.2) ∧ (∀ x ∈ v, x.2 ≠ z.2) := by
  simp only [List.map_append, List.map_cons] at h
  have hp := List.nodup_append.mp h
  constructor
  · intro x hx hxp
    exact hp.2.2 x.2 (List.mem_map.mpr ⟨x, hx, rfl⟩) z.2 (by simp) hxp
  · intro x hx hxp
    apply (List.nodup_cons.mp hp.2.1).1
    exact List.mem_map.mpr ⟨x, hx, hxp⟩

end Lemmata.FockCircuits.Patterns
