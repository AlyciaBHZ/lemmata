module

public import Lemmata.FockCircuits.NormalSymbol

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.Matching

variable (R : Type*) [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {α : Type*}

def word (x : α → M) (A : List α) : ExteriorAlgebra R M :=
  (A.map fun a => ExteriorAlgebra.ι R (x a)).prod

@[simp] theorem word_nil (x : α → M) : word R x [] = 1 := rfl

@[simp] theorem word_cons (x : α → M) (a : α) (A : List α) :
    word R x (a :: A) = ExteriorAlgebra.ι R (x a) * word R x A := rfl

theorem word_append (x : α → M) (A B : List α) :
    word R x (A ++ B) = word R x A * word R x B := by
  simp [word]

theorem word_eq_ιMulti (x : α → M) (A : List α) :
    word R x A = ExteriorAlgebra.ιMulti R A.length (fun j => x A[j]) := by
  rw [ExteriorAlgebra.ιMulti_apply]
  unfold word
  simp only [Fin.getElem_fin]
  exact congrArg List.prod
    (List.ofFn_getElem_eq_map A (fun a => ExteriorAlgebra.ι R (x a))).symm

theorem word_block_exchange (x : α → M) (A C : List α) :
    word R x A * word R x C =
      ((-1 : ℤˣ) ^ (A.length * C.length)) • (word R x C * word R x A) := by
  simp only [word_eq_ιMulti]
  simpa only [Nat.mul_comm] using
    ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm R (fun j : Fin A.length => x A[j])
      (fun j : Fin C.length => x C[j])

theorem contract_word (x : α → M) (d : Module.Dual R M) (A : List α) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d (word R x A) =
      ∑ j : Fin A.length, ((-1 : R) ^ (j : ℕ) * d (x A[j])) •
        word R x (A.eraseIdx j) := by
  induction A with
  | nil => simp
  | cons a A ih =>
    rw [word_cons, CliffordAlgebra.contractLeft_ι_mul, ih]
    simp only [List.length_cons]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.getElem_fin, Fin.val_zero, pow_zero, one_mul, List.getElem_cons_zero,
      List.eraseIdx_cons_zero, Fin.val_succ, List.getElem_cons_succ,
      List.eraseIdx_cons_succ, word_cons, Finset.mul_sum, Finset.smul_sum,
      Algebra.mul_smul_comm, pow_succ, mul_neg, neg_mul, mul_one, neg_smul,
      Finset.sum_neg_distrib]
    module

theorem contract_word_mul_of_zero (x : α → M) (d : Module.Dual R M)
    (A : List α) (y : ExteriorAlgebra R M) (hA : ∀ a ∈ A, d (x a) = 0) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d (word R x A * y) =
      (-1 : R) ^ A.length •
        (word R x A * CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d y) := by
  induction A with
  | nil => simp
  | cons a A ih =>
    have ha : d (x a) = 0 := hA a (by simp)
    have hA' : ∀ b ∈ A, d (x b) = 0 := fun b hb => hA b (List.mem_cons_of_mem _ hb)
    simp only [word_cons, mul_assoc, CliffordAlgebra.contractLeft_ι_mul,
      ha, zero_smul, zero_sub, ih hA', List.length_cons,
      Algebra.mul_smul_comm, pow_succ, mul_neg, mul_one, neg_smul]

theorem twist_word_of_zero (B : LinearMap.BilinForm R M) (hB : B.IsAlt)
    (x : α → M) (A : List α) (hA : ∀ a ∈ A, ∀ b ∈ A, B (x a) (x b) = 0) :
    twist R B hB (word R x A) = word R x A := by
  induction A with
  | nil => simp
  | cons a A ih =>
    have hAA : ∀ b ∈ A, ∀ c ∈ A, B (x b) (x c) = 0 :=
      fun b hb c hc => hA b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc)
    have haA : ∀ b ∈ A, B (x a) (x b) = 0 :=
      fun b hb => hA a (by simp) b (List.mem_cons_of_mem _ hb)
    rw [word_cons, twist_ι_mul, ih hAA, contract_word]
    have hz : (∑ j : Fin A.length, ((-1 : R) ^ (j : ℕ) * B (x a) (x A[j])) •
        word R x (A.eraseIdx j)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [haA A[j] (List.getElem_mem j.isLt), mul_zero, zero_smul]
    rw [hz, add_zero]

def exteriorEvaluate (κ : α → α → R) (x : α → M) (T : List (Term α)) :
    ExteriorAlgebra R M :=
  (T.map fun t => coefficient R κ t • word R x t.remaining).sum

@[simp] theorem exteriorEvaluate_nil (κ : α → α → R) (x : α → M) :
    exteriorEvaluate R κ x [] = 0 := rfl

@[simp] theorem exteriorEvaluate_cons (κ : α → α → R) (x : α → M)
    (t : Term α) (T : List (Term α)) :
    exteriorEvaluate R κ x (t :: T) = coefficient R κ t • word R x t.remaining +
      exteriorEvaluate R κ x T := rfl

theorem exteriorEvaluate_append (κ : α → α → R) (x : α → M)
    (T U : List (Term α)) :
    exteriorEvaluate R κ x (T ++ U) = exteriorEvaluate R κ x T + exteriorEvaluate R κ x U := by
  simp [exteriorEvaluate]

theorem exteriorEvaluate_unmatched (κ : α → α → R) (x : α → M)
    (a : α) (T : List (Term α)) :
    exteriorEvaluate R κ x (T.map (unmatched a)) =
      ExteriorAlgebra.ι R (x a) * exteriorEvaluate R κ x T := by
  induction T with
  | nil => simp
  | cons t T ih =>
    simp only [List.map_cons, exteriorEvaluate_cons, coefficient_unmatched,
      unmatched_remaining, word_cons, ih, mul_add, Algebra.mul_smul_comm]

theorem exteriorEvaluate_paired (κ : α → α → R) (x : α → M)
    (a b : α) (s : ℕ) (T : List (Term α)) :
    exteriorEvaluate R κ x (T.map (paired a b s)) =
      ((-1 : R) ^ s * κ a b) • exteriorEvaluate R κ x T := by
  induction T with
  | nil => simp
  | cons t T ih =>
    simp only [List.map_cons, exteriorEvaluate_cons, coefficient_paired,
      paired_remaining, smul_add, smul_smul, ih]

theorem exteriorEvaluate_flatten (κ : α → α → R) (x : α → M)
    (T : List (List (Term α))) :
    exteriorEvaluate R κ x T.flatten = (T.map fun t => exteriorEvaluate R κ x t).sum := by
  induction T with
  | nil => simp
  | cons t T ih => simp [exteriorEvaluate_append, ih]

theorem exteriorEvaluate_terms_cons (κ : α → α → R) (x : α → M)
    (a : α) (A B : List α) :
    exteriorEvaluate R κ x (terms (a :: A) B) =
      ExteriorAlgebra.ι R (x a) * exteriorEvaluate R κ x (terms A B) +
        ∑ j : Fin B.length, ((-1 : R) ^ (A.length + (j : ℕ)) * κ a B[j]) •
          exteriorEvaluate R κ x (terms A (B.eraseIdx j)) := by
  rw [terms, exteriorEvaluate_append, exteriorEvaluate_unmatched, exteriorEvaluate_flatten]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, exteriorEvaluate_paired]

theorem twist_word_product (B : LinearMap.BilinForm R M) (hB : B.IsAlt)
    (x : α → M) (A C : List α)
    (hAA : ∀ a ∈ A, ∀ b ∈ A, B (x a) (x b) = 0)
    (hCC : ∀ a ∈ C, ∀ b ∈ C, B (x a) (x b) = 0) :
    twist R B hB (word R x A * word R x C) =
      exteriorEvaluate R (fun a b => B (x a) (x b)) x (terms A C) := by
  classical
  induction A generalizing C with
  | nil => simp [terms, exteriorEvaluate, coefficient, twist_word_of_zero R B hB x C hCC]
  | cons a A ih =>
    have hAA' : ∀ b ∈ A, ∀ c ∈ A, B (x b) (x c) = 0 :=
      fun b hb c hc => hAA b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc)
    have haA : ∀ b ∈ A, B (x a) (x b) = 0 :=
      fun b hb => hAA a (by simp) b (List.mem_cons_of_mem _ hb)
    have hcomm : twist R B hB
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) (B (x a))
          (word R x A * word R x C)) =
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) (B (x a))
          (twist R B hB (word R x A * word R x C)) := by
      simpa only [twist] using CliffordAlgebra.changeForm_contractLeft
        (negative_form_zero R B hB) (B (x a)) (word R x A * word R x C)
    have hd : (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) (B (x a)))
        (twist R B hB (word R x A * word R x C)) =
        ∑ j : Fin C.length, ((-1 : R) ^ (A.length + (j : ℕ)) * B (x a) (x C[j])) •
          exteriorEvaluate R (fun b c => B (x b) (x c)) x (terms A (C.eraseIdx j)) := by
      rw [← hcomm, contract_word_mul_of_zero R x (B (x a)) A _ haA, contract_word]
      simp only [Finset.mul_sum, Algebra.mul_smul_comm, map_smul, map_sum,
        Finset.smul_sum, smul_smul, pow_add, mul_assoc]
      apply Finset.sum_congr rfl
      intro j hj
      have hCC' : ∀ b ∈ C.eraseIdx j, ∀ c ∈ C.eraseIdx j, B (x b) (x c) = 0 :=
        fun b hb c hc => hCC b (List.eraseIdx_subset hb) c (List.eraseIdx_subset hc)
      rw [ih (C.eraseIdx j) hAA' hCC']
    rw [word_cons, mul_assoc, twist_ι_mul, hd, ih C hAA' hCC, exteriorEvaluate_terms_cons]

theorem normalSymbol_exteriorEvaluate (κ : α → α → R)
    (x : α → OneParticle R × OneParticle R) (T : List (Term α)) (y : Fock R) :
    Fock.normalSymbol R (exteriorEvaluate R κ x T) y =
      evaluate R κ (fun a => (x a).1) (fun a => (x a).2) T y := by
  induction T with
  | nil => simp
  | cons t T ih =>
    rw [exteriorEvaluate_cons, map_add, map_smul]
    change coefficient R κ t • Fock.normalSymbol R (word R x t.remaining) y +
      Fock.normalSymbol R (exteriorEvaluate R κ x T) y = _
    rw [ih]
    congr 1
    have hm : (t.remaining.map fun a => ExteriorAlgebra.ι R (x a)) =
        ((t.remaining.map x).map (ExteriorAlgebra.ι R)) := by simp
    unfold word
    rw [hm, Fock.normalSymbol_word]

theorem exterior_matching_exchange (B : LinearMap.BilinForm R M) (hB : B.IsAlt)
    (x : α → M) (A C : List α)
    (hAA : ∀ a ∈ A, ∀ b ∈ A, B (x a) (x b) = 0)
    (hCC : ∀ a ∈ C, ∀ b ∈ C, B (x a) (x b) = 0) :
    exteriorEvaluate R (fun a b => B (x a) (x b)) x (terms A C) =
      ((-1 : ℤˣ) ^ (A.length * C.length)) •
        exteriorEvaluate R (fun a b => B (x a) (x b)) x (terms C A) := by
  rw [← twist_word_product R B hB x A C hAA hCC,
    ← twist_word_product R B hB x C A hCC hAA, word_block_exchange]
  simp only [Units.smul_def, map_zsmul]

theorem normal_matching_exchange
    (B : LinearMap.BilinForm R (OneParticle R × OneParticle R)) (hB : B.IsAlt)
    (x : α → OneParticle R × OneParticle R) (A C : List α)
    (hAA : ∀ a ∈ A, ∀ b ∈ A, B (x a) (x b) = 0)
    (hCC : ∀ a ∈ C, ∀ b ∈ C, B (x a) (x b) = 0) (y : Fock R) :
    evaluate R (fun a b => B (x a) (x b)) (fun a => (x a).1) (fun a => (x a).2)
        (terms A C) y =
      ((-1 : ℤˣ) ^ (A.length * C.length)) •
        evaluate R (fun a b => B (x a) (x b)) (fun a => (x a).1) (fun a => (x a).2)
          (terms C A) y := by
  rw [← normalSymbol_exteriorEvaluate, ← normalSymbol_exteriorEvaluate,
    exterior_matching_exchange R B hB x A C hAA hCC]
  simp only [Units.smul_def, map_zsmul, LinearMap.smul_apply]

theorem full_matching_vacuum (u v : α → OneParticle R) (A C : List α) :
    Fock.augmentation R
        (Fock.normalList R (A.map fun a => (u a, v a))
          (Fock.normalList R (C.map fun a => (u a, v a)) 1)) =
      ((terms A C).map fun t =>
        if t.remaining = [] then
          coefficient R (fun a b => Fock.coordinateDual R (v a) (u b)) t else 0).sum := by
  rw [normalList_product]
  simp only [evaluate, map_list_sum, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  simp only [map_smul, Fock.augmentation_normalList_one, List.map_eq_nil_iff]
  by_cases h : t.remaining = [] <;> simp [h, smul_eq_mul]

end Lemmata.FockCircuits.Matching
