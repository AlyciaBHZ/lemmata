module

public import Lemmata.FockCircuits.PatternBounds

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Patterns

universe u

variable {R P C : Type*} [CommSemiring R] [Fintype P] [DecidableEq P] [Fintype C]

def collapseRow (p : P) : P ⊕ Unit → P := Sum.elim id (fun _ => p)

theorem nodup_rows_delete {B : Type*} (u v : List (B × P)) (z : B × P)
    (h : ((u ++ z :: v).map Prod.snd).Nodup) : ((u ++ v).map Prod.snd).Nodup := by
  simp only [List.map_append, List.map_cons] at h ⊢
  exact List.Nodup.sublist
    ((List.sublist_cons_self z.2 (v.map Prod.snd)).append_left (u.map Prod.snd)) h

theorem nodup_rows_delete_second {B : Type*} (u v : List (B × P)) (z t : B × P)
    (h : ((u ++ z :: t :: v).map Prod.snd).Nodup) :
    ((u ++ z :: v).map Prod.snd).Nodup := by
  simp only [List.map_append, List.map_cons] at h ⊢
  exact List.Nodup.sublist
    (((List.sublist_cons_self t.2 (v.map Prod.snd)).cons_cons z.2).append_left
      (u.map Prod.snd)) h

theorem pattern_hasCircuit (s : ℕ)
    (h₄ : ∀ p q r t : P, HasCircuit (quartic (R := R) (C := C) p q r t) s)
    (h₅ : ∀ p q r t u : P, HasCircuit (quintic (R := R) (C := C) p q r t u) s)
    {B : Type u} [Fintype B] [DecidableEq B] (w : List (B × P))
    (hlen : w.length ≤ 5) (hrows : (w.map Prod.snd).Nodup) :
    HasCircuit (pattern (R := R) (C := C) w)
      (s + 1 + w.length * (3 * Fintype.card C + 2)) := by
  classical
  let stepCost := 3 * Fintype.card C + 2
  have aux : ∀ k : ℕ, ∀ (B : Type u) [Fintype B] [DecidableEq B] (w : List (B × P)),
      w.length = k → w.length ≤ 5 → (w.map Prod.snd).Nodup →
        HasCircuit (pattern (R := R) (C := C) w) (s + 1 + k * stepCost) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro B _ _ w hk hlen hrows
      have hkfive : k ≤ 5 := by omega
      rcases labelled_cases w with ⟨u, ⟨a, p⟩, v, rfl, hsingle⟩ |
          ⟨u, ⟨a, p⟩, ⟨b, q⟩, v, rfl, hab⟩ | ht
      · have havoid := singleton_avoids u v a p hsingle
        rcases List.eq_nil_or_concat' u with rfl | ⟨u₀, ⟨b, q⟩, rfl⟩
        · let red := removeLabel a v havoid.2
          have hm : red.length + 1 = k := by
            simp only [List.nil_append, List.length_cons] at hk
            simpa only [red, removeLabel_length, Nat.add_comm] using hk
          have hredrows : (red.map Prod.snd).Nodup := by
            rw [show red.map Prod.snd = v.map Prod.snd from removeLabel_rows a v havoid.2]
            have hr := hrows
            simp only [List.nil_append, List.map_cons] at hr
            exact (List.nodup_cons.mp hr).2
          have hc := ih red.length (by omega) {b : B // b ≠ a} red rfl (by omega) hredrows
          have hext := singleton_first_hasCircuit (R := R) hc
          rw [← singleton_first_pattern (R := R) (P := P) (C := C) (B := B) a red] at hext
          have hback := rename_hasCircuit
            (fun z : Extended P C => (collapseRow p z.1, z.2)) hext
          rw [pattern_mapRows] at hback
          have hf : HasCircuit (pattern (R := R) (C := C) ((a, p) :: v))
              (2 * Fintype.card C + (s + 1 + red.length * stepCost) + 1) := by
            simpa only [List.map_cons, List.map_map, Function.comp_def, collapseRow,
              Sum.elim_inl, Sum.elim_inr, id_eq, red, removeLabel_forget, List.map_id] using hback
          apply hf.mono
          rw [← hm, Nat.add_mul, Nat.one_mul]
          dsimp only [stepCost]
          omega
        · have hu : ∀ z ∈ u₀, z.1 ≠ a := by
            intro z hz
            exact havoid.1 z (List.mem_append_left _ hz)
          have hb : b ≠ a := havoid.1 (b, q) (by simp)
          let b' : {b : B // b ≠ a} := ⟨b, hb⟩
          let red := removeLabel a u₀ hu ++ (b', q) :: removeLabel a v havoid.2
          have hm : red.length + 1 = k := by
            simp only [List.length_append, List.length_cons, List.length_nil] at hk
            simp only [red, List.length_append, List.length_cons, removeLabel_length]
            omega
          have hredrows : red.map Prod.snd = (u₀ ++ (b, q) :: v).map Prod.snd := by
            simp only [red, List.map_append, List.map_cons, removeLabel_rows]
          have hrednd : (red.map Prod.snd).Nodup := by
            rw [hredrows]
            apply nodup_rows_delete_second u₀ v (b, q) (a, p)
            simpa only [List.append_assoc, List.singleton_append] using hrows
          have hpart := nodup_row_parts (removeLabel a u₀ hu) (removeLabel a v havoid.2)
            (b', q) hrednd
          have hc := ih red.length (by omega) {b : B // b ≠ a} red rfl (by omega) hrednd
          have hext := singletonInsertion_hasCircuit (R := R) q hc
          have hpoly := singleton_pattern (R := R) (P := P) (C := C) (B := B) a b' q
            (removeLabel a u₀ hu) (removeLabel a v havoid.2) hpart.1 hpart.2
          rw [hpoly] at hext
          have hback := rename_hasCircuit
            (fun z : Extended P C => (collapseRow p z.1, z.2)) hext
          rw [pattern_mapRows] at hback
          have hf : HasCircuit
              (pattern (R := R) (C := C) ((u₀ ++ [(b, q)]) ++ (a, p) :: v))
              (3 * Fintype.card C + (s + 1 + red.length * stepCost)) := by
            simpa only [List.map_append, List.map_cons, List.map_map, Function.comp_def,
              collapseRow, Sum.elim_inl, Sum.elim_inr, id_eq, b', removeLabel_forget,
              List.append_assoc, List.singleton_append, List.map_id] using hback
          apply hf.mono
          rw [← hm, Nat.add_mul, Nat.one_mul]
          dsimp only [stepCost]
          omega
      · change a = b at hab
        subst b
        let red := u ++ (a, p) :: v
        have hm : red.length + 1 = k := by
          simp only [List.length_append, List.length_cons] at hk
          simp only [red, List.length_append, List.length_cons]
          omega
        have hrednd : (red.map Prod.snd).Nodup :=
          nodup_rows_delete_second u v (a, p) (a, q) hrows
        have hpart := nodup_row_parts u v (a, p) hrednd
        have hc := ih red.length (by omega) B red rfl (by omega) hrednd
        have hext := adjacentExpansion_hasCircuit (R := R) p hc
        have hpoly := adjacent_pattern (R := R) (P := P) (C := C) (B := B) a p u v hpart.1 hpart.2
        rw [hpoly] at hext
        have hback := rename_hasCircuit
          (fun z : Extended P C => (collapseRow q z.1, z.2)) hext
        rw [pattern_mapRows] at hback
        have hf : HasCircuit (pattern (R := R) (C := C) (u ++ (a, p) :: (a, q) :: v))
            (Fintype.card C + (s + 1 + red.length * stepCost)) := by
          simp only [List.map_append, List.map_cons, List.map_map, Function.comp_def,
            collapseRow, Sum.elim_inl, Sum.elim_inr, id_eq, Prod.mk.eta] at hback
          simpa only [List.map_id', Nat.add_assoc] using hback
        apply hf.mono
        rw [← hm, Nat.add_mul, Nat.one_mul]
        dsimp only [stepCost]
        omega
      · exact (terminal_hasCircuit w ht hlen s h₄ h₅).mono (by omega)
  exact aux w.length B w rfl hlen hrows

end Lemmata.FockCircuits.Patterns
