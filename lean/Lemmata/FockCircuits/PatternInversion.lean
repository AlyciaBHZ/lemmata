module

public import Lemmata.FockCircuits.PatternInduction
public import Lemmata.FockCircuits.Symmetric
public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.Data.List.FinRange

@[expose] public section

set_option autoImplicit false

open scoped BigOperators Classical

namespace Lemmata.FockCircuits.Patterns

theorem finite_mobius_inversion {A M : Type*} [Fintype A] [PartialOrder A]
    [LocallyFiniteOrder A] [DecidableEq A] [AddCommGroup M]
    (p e : A → M) (hp : ∀ a, p a = ∑ b : A, if a ≤ b then e b else 0) (a : A) :
    e a = ∑ b : A, IncidenceAlgebra.mu ℤ a b • p b := by
  classical
  symm
  calc
    _ = ∑ b : A, ∑ c : A,
        IncidenceAlgebra.mu ℤ a b • (if b ≤ c then e c else 0) := by
      simp_rw [hp, Finset.smul_sum]
    _ = ∑ c : A, ∑ b : A,
        if a ≤ b ∧ b ≤ c then IncidenceAlgebra.mu ℤ a b • e c else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hab : a ≤ b <;> by_cases hbc : b ≤ c
      · simp only [hab, hbc, and_self, ite_true]
      · simp only [hab, hbc, and_false, ite_false, smul_zero]
      · rw [IncidenceAlgebra.apply_eq_zero_of_not_le hab]
        simp only [hab, hbc, false_and, ite_false, ite_true, zero_smul]
      · simp only [hab, hbc, false_and, ite_false, smul_zero]
    _ = ∑ c : A, (∑ b ∈ Finset.Icc a c, IncidenceAlgebra.mu ℤ a b) • e c := by
      apply Finset.sum_congr rfl
      intro c hc
      have hi : Finset.Icc a c = Finset.univ.filter (fun b => a ≤ b ∧ b ≤ c) := by
        ext b
        simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hi, Finset.sum_smul, Finset.sum_filter]
    _ = e a := by
      simp only [IncidenceAlgebra.sum_Icc_mu_right, ite_smul, one_smul, zero_smul]
      simp

variable {R X : Type*} [CommRing R]

theorem zsmul_hasCircuit (m : ℤ) {f : FreeAlgebra R X} {s : ℕ} (h : HasCircuit f s) :
    HasCircuit (m • f) (s + 1) := by
  rw [← Int.cast_smul_eq_zsmul R m f, Algebra.smul_def]
  simpa only [zero_add] using (HasCircuit.scalar (X := X) (m : R)).mul h

theorem finset_sum_hasCircuit {A : Type*} [DecidableEq A] (t : Finset A)
    (p : A → FreeAlgebra R X) (s : ℕ) (hp : ∀ a ∈ t, HasCircuit (p a) s) :
    HasCircuit (∑ a ∈ t, p a) (t.card * (s + 1)) := by
  induction t using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, Finset.card_empty, Nat.zero_mul, map_zero] using
      HasCircuit.scalar (X := X) (0 : R)
  | @insert a t hat ih =>
    rw [Finset.sum_insert hat, Finset.card_insert_of_notMem hat]
    have ha := hp a (Finset.mem_insert_self a t)
    have ht := ih (fun b hb => hp b (Finset.mem_insert_of_mem hb))
    exact (ha.add ht).mono (by rw [Nat.add_mul, Nat.one_mul]; omega)

theorem unitriangular_hasCircuit {A : Type*} [Fintype A] [PartialOrder A]
    [LocallyFiniteOrder A] [DecidableEq A]
    (p e : A → FreeAlgebra R X) (s : ℕ)
    (htri : ∀ a, p a = ∑ b : A, if a ≤ b then e b else 0)
    (hp : ∀ a, HasCircuit (p a) s) (a : A) :
    HasCircuit (e a) (Fintype.card A * (s + 2)) := by
  classical
  rw [finite_mobius_inversion p e htri a]
  have h := finset_sum_hasCircuit Finset.univ
    (fun b => IncidenceAlgebra.mu ℤ a b • p b) (s + 1)
    (fun b _ => zsmul_hasCircuit _ (hp b))
  simpa only [Finset.card_univ, Nat.add_assoc] using h

noncomputable def allPattern [Fintype X] {k : ℕ} (π : Setoid (Fin k)) : FreeAlgebra R X := by
  classical
  exact ∑ f : Quotient π → X, word (List.ofFn fun i => f (Quotient.mk π i))

theorem allPattern_eq_sum [Fintype X] {k : ℕ} (π : Setoid (Fin k)) :
    allPattern (R := R) (X := X) π =
      ∑ a : Fin k → X, if π ≤ Setoid.ker a then word (List.ofFn a) else 0 := by
  classical
  unfold allPattern
  let liftTuple : (Quotient π → X) → Fin k → X := fun f i => f (Quotient.mk π i)
  have hinj : Function.Injective liftTuple := by
    intro f g hfg
    funext q
    refine Quotient.inductionOn q (fun i => ?_)
    exact congrFun hfg i
  apply Fintype.sum_of_injective liftTuple hinj
  · intro a ha
    by_cases hπ : π ≤ Setoid.ker a
    · exfalso
      apply ha
      refine ⟨Quotient.lift a (fun i j hij => hπ hij), ?_⟩
      rfl
    · exact ite_eq_right hπ
  · intro f
    have hπ : π ≤ Setoid.ker (liftTuple f) := by
      intro i j hij
      exact congrArg f (Quotient.sound hij)
    exact (ite_eq_left hπ).symm

theorem allPattern_eq_exact_sum [Fintype X] {k : ℕ} (π : Setoid (Fin k)) :
    allPattern (R := R) (X := X) π =
      ∑ τ : Setoid (Fin k), if π ≤ τ then Symmetric.exactPattern (R := R) (X := X) τ else 0 := by
  classical
  rw [allPattern_eq_sum]
  symm
  calc
    _ = ∑ τ : Setoid (Fin k), ∑ a : Fin k → X,
        if π ≤ τ ∧ Setoid.ker a = τ then word (List.ofFn a) else 0 := by
      apply Finset.sum_congr rfl
      intro τ hτ
      by_cases hπ : π ≤ τ
      · simp only [hπ, ite_true, true_and, Symmetric.exactPattern]
      · simp only [hπ, ite_false, false_and, Finset.sum_const_zero]
    _ = ∑ a : Fin k → X, if π ≤ Setoid.ker a then word (List.ofFn a) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_eq_single (Setoid.ker a)]
      · simp only [and_true]
      · intro τ hτ hne
        simp only [Ne.symm hne, and_false, ite_false]
      · simp

noncomputable def quotientWord {k : ℕ} (π : Setoid (Fin k)) : List (Quotient π × Fin k) :=
  List.ofFn fun i => (Quotient.mk π i, i)

theorem quotientWord_rows {k : ℕ} (π : Setoid (Fin k)) :
    (quotientWord π).map Prod.snd = List.finRange k := by
  simp only [quotientWord, List.map_ofFn, List.finRange, Function.comp_def]

theorem quotientWord_nodup {k : ℕ} (π : Setoid (Fin k)) :
    ((quotientWord π).map Prod.snd).Nodup := by
  rw [quotientWord_rows]
  exact List.nodup_finRange k

theorem allPattern_eq_identified [Fintype X] {k : ℕ} (π : Setoid (Fin k)) :
    allPattern (R := R) (X := X) π =
      FreeAlgebra.lift R (fun z : Fin k × X => FreeAlgebra.ι R z.2)
        (pattern (R := R) (C := X) (quotientWord π)) := by
  classical
  simp only [allPattern, pattern, map_sum]
  apply Finset.sum_congr rfl
  intro f hf
  simp only [quotientWord, word, List.map_ofFn, List.map_map, map_list_prod,
    FreeAlgebra.lift_ι_apply, Function.comp_def]

theorem quartic_hasCircuit {P C : Type*} [Fintype C] {s : ℕ}
    (h : HasCircuit (quartic (R := R) (C := C) (P := Fin 4) 0 1 2 3) s)
    (p q r t : P) : HasCircuit (quartic (R := R) (C := C) p q r t) s := by
  let rows : Fin 4 → P := ![p, q, r, t]
  have hr := rename_hasCircuit (fun z : Fin 4 × C => (rows z.1, z.2)) h
  simpa [quartic, rows] using hr

theorem quintic_hasCircuit {P C : Type*} [Fintype C] {s : ℕ}
    (h : HasCircuit (quintic (R := R) (C := C) (P := Fin 5) 0 1 2 3 4) s)
    (p q r t u : P) : HasCircuit (quintic (R := R) (C := C) p q r t u) s := by
  let rows : Fin 5 → P := ![p, q, r, t, u]
  have hr := rename_hasCircuit (fun z : Fin 5 × C => (rows z.1, z.2)) h
  simpa [quintic, rows] using hr

theorem allPattern_hasCircuit [Fintype X] {s : ℕ}
    (h₄ : HasCircuit (quartic (R := R) (C := X) (P := Fin 4) 0 1 2 3) s)
    (h₅ : HasCircuit (quintic (R := R) (C := X) (P := Fin 5) 0 1 2 3 4) s)
    {k : ℕ} (hk : k ≤ 5) (π : Setoid (Fin k)) :
    HasCircuit (allPattern (R := R) (X := X) π) (s + 15 * Fintype.card X + 11) := by
  classical
  have hlen : (quotientWord π).length ≤ 5 := by simpa only [quotientWord, List.length_ofFn] using hk
  have hp := pattern_hasCircuit s (quartic_hasCircuit h₄) (quintic_hasCircuit h₅)
    (quotientWord π) hlen (quotientWord_nodup π)
  have hr := rename_hasCircuit (fun z : Fin k × X => z.2) hp
  rw [← allPattern_eq_identified] at hr
  apply hr.mono
  simp only [quotientWord, List.length_ofFn]
  have hb := Nat.mul_le_mul_right (3 * Fintype.card X + 2) hk
  omega

theorem exactPattern_hasCircuit [Fintype X] {s : ℕ}
    (h₄ : HasCircuit (quartic (R := R) (C := X) (P := Fin 4) 0 1 2 3) s)
    (h₅ : HasCircuit (quintic (R := R) (C := X) (P := Fin 5) 0 1 2 3 4) s)
    {k : ℕ} (hk : k ≤ 5) (π : Setoid (Fin k)) :
    HasCircuit (Symmetric.exactPattern (R := R) (X := X) π)
      (Fintype.card (Setoid (Fin k)) * (s + 15 * Fintype.card X + 13)) := by
  classical
  letI : LocallyFiniteOrder (Setoid (Fin k)) := Fintype.toLocallyFiniteOrder
  have h := unitriangular_hasCircuit
    (fun τ : Setoid (Fin k) => allPattern (R := R) (X := X) τ)
    (fun τ : Setoid (Fin k) => Symmetric.exactPattern (R := R) (X := X) τ)
    (s + 15 * Fintype.card X + 11) allPattern_eq_exact_sum
    (allPattern_hasCircuit h₄ h₅ hk) π
  simpa only [Nat.add_assoc] using h

noncomputable def positionalAllPattern (C : Type*) [Fintype C]
    {k : ℕ} (π : Setoid (Fin k)) : FreeAlgebra R (Fin k × C) := by
  classical
  exact pattern (R := R) (C := C) (quotientWord π)

noncomputable def positionalExactPattern (C : Type*) [Fintype C]
    {k : ℕ} (π : Setoid (Fin k)) : FreeAlgebra R (Fin k × C) := by
  classical
  exact ∑ a : Fin k → C, if Setoid.ker a = π then
    word (List.ofFn fun i => (i, a i)) else 0

theorem positionalAllPattern_eq_sum {C : Type*} [Fintype C]
    {k : ℕ} (π : Setoid (Fin k)) :
    positionalAllPattern (R := R) C π =
      ∑ a : Fin k → C, if π ≤ Setoid.ker a then word (List.ofFn fun i => (i, a i)) else 0 := by
  classical
  unfold positionalAllPattern pattern quotientWord
  simp only [List.map_ofFn, Function.comp_def]
  let liftTuple : (Quotient π → C) → Fin k → C := fun f i => f (Quotient.mk π i)
  have hinj : Function.Injective liftTuple := by
    intro f g hfg
    funext q
    refine Quotient.inductionOn q (fun i => ?_)
    exact congrFun hfg i
  apply Fintype.sum_of_injective liftTuple hinj
  · intro a ha
    by_cases hπ : π ≤ Setoid.ker a
    · exfalso
      apply ha
      exact ⟨Quotient.lift a (fun i j hij => hπ hij), rfl⟩
    · exact ite_eq_right hπ
  · intro f
    have hπ : π ≤ Setoid.ker (liftTuple f) := by
      intro i j hij
      exact congrArg f (Quotient.sound hij)
    exact (ite_eq_left hπ).symm

theorem positionalAllPattern_eq_exact_sum {C : Type*} [Fintype C]
    {k : ℕ} (π : Setoid (Fin k)) :
    positionalAllPattern (R := R) C π =
      ∑ τ : Setoid (Fin k), if π ≤ τ then positionalExactPattern (R := R) C τ else 0 := by
  classical
  rw [positionalAllPattern_eq_sum]
  symm
  calc
    _ = ∑ τ : Setoid (Fin k), ∑ a : Fin k → C,
        if π ≤ τ ∧ Setoid.ker a = τ then word (List.ofFn fun i => (i, a i)) else 0 := by
      apply Finset.sum_congr rfl
      intro τ hτ
      by_cases hπ : π ≤ τ
      · simp only [hπ, ite_true, true_and, positionalExactPattern]
      · simp only [hπ, ite_false, false_and, Finset.sum_const_zero]
    _ = ∑ a : Fin k → C, if π ≤ Setoid.ker a then word (List.ofFn fun i => (i, a i)) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_eq_single (Setoid.ker a)]
      · simp only [and_true]
      · intro τ hτ hne
        simp only [Ne.symm hne, and_false, ite_false]
      · simp

theorem positionalAllPattern_hasCircuit {C : Type*} [Fintype C] {s : ℕ}
    (h₄ : HasCircuit (quartic (R := R) (C := C) (P := Fin 4) 0 1 2 3) s)
    (h₅ : HasCircuit (quintic (R := R) (C := C) (P := Fin 5) 0 1 2 3 4) s)
    {k : ℕ} (hk : k ≤ 5) (π : Setoid (Fin k)) :
    HasCircuit (positionalAllPattern (R := R) C π) (s + 15 * Fintype.card C + 11) := by
  classical
  have hlen : (quotientWord π).length ≤ 5 := by simpa only [quotientWord, List.length_ofFn] using hk
  have hp := pattern_hasCircuit s (quartic_hasCircuit h₄) (quintic_hasCircuit h₅)
    (quotientWord π) hlen (quotientWord_nodup π)
  change HasCircuit (pattern (R := R) (C := C) (quotientWord π)) _
  apply hp.mono
  simp only [quotientWord, List.length_ofFn]
  have hb := Nat.mul_le_mul_right (3 * Fintype.card C + 2) hk
  omega

theorem positionalExactPattern_hasCircuit {C : Type*} [Fintype C] {s : ℕ}
    (h₄ : HasCircuit (quartic (R := R) (C := C) (P := Fin 4) 0 1 2 3) s)
    (h₅ : HasCircuit (quintic (R := R) (C := C) (P := Fin 5) 0 1 2 3 4) s)
    {k : ℕ} (hk : k ≤ 5) (π : Setoid (Fin k)) :
    HasCircuit (positionalExactPattern (R := R) C π)
      (Fintype.card (Setoid (Fin k)) * (s + 15 * Fintype.card C + 13)) := by
  classical
  letI : LocallyFiniteOrder (Setoid (Fin k)) := Fintype.toLocallyFiniteOrder
  have h := unitriangular_hasCircuit
    (fun τ : Setoid (Fin k) => positionalAllPattern (R := R) C τ)
    (fun τ : Setoid (Fin k) => positionalExactPattern (R := R) C τ)
    (s + 15 * Fintype.card C + 11) positionalAllPattern_eq_exact_sum
    (positionalAllPattern_hasCircuit h₄ h₅ hk) π
  simpa only [Nat.add_assoc] using h

noncomputable def rectangularPermanent (R : Type*) [CommRing R] (k n : ℕ) :
    FreeAlgebra R (Fin k × Fin n) := by
  classical
  exact ∑ a : Fin k → Fin n, if Function.Injective a then
    word (List.ofFn fun i => (i, a i)) else 0

theorem rectangularPermanent_eq_exact (k n : ℕ) :
    rectangularPermanent R k n =
      positionalExactPattern (R := R) (Fin n) (⊥ : Setoid (Fin k)) := by
  classical
  simp only [rectangularPermanent, positionalExactPattern, Setoid.ker_eq_bot_iff]

end Lemmata.FockCircuits.Patterns
