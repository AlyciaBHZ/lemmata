module

public import Lemmata.FockCircuits.Wick
public import Mathlib.Data.List.InsertIdx

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.Matching

structure Term (α : Type*) where
  sign : ℤ
  pairs : List (α × α)
  remaining : List α

variable {α : Type*}

def unmatched (a : α) (t : Term α) : Term α :=
  ⟨t.sign, t.pairs, a :: t.remaining⟩

@[simp] theorem unmatched_remaining (a : α) (t : Term α) :
    (unmatched a t).remaining = a :: t.remaining := rfl

def paired (a b : α) (s : ℕ) (t : Term α) : Term α :=
  ⟨(-1) ^ s * t.sign, (a, b) :: t.pairs, t.remaining⟩

@[simp] theorem paired_remaining (a b : α) (s : ℕ) (t : Term α) :
    (paired a b s t).remaining = t.remaining := rfl

def terms : List α → List α → List (Term α)
  | [], B => [⟨1, [], B⟩]
  | a :: A, B =>
    (terms A B).map (unmatched a) ++
      (List.ofFn fun j : Fin B.length =>
        (terms A (B.eraseIdx j)).map (paired a B[j] (A.length + (j : ℕ)))).flatten

theorem term_length {A B : List α} {t : Term α} (ht : t ∈ terms A B) :
    t.remaining.length + 2 * t.pairs.length = A.length + B.length := by
  induction A generalizing B t with
  | nil =>
    simp only [terms, List.mem_singleton] at ht
    subst t
    simp
  | cons a A ih =>
    simp only [terms, List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      have h := ih hs
      simp only [unmatched, List.length_cons]
      omega
    · obtain ⟨l, hl, ht⟩ := List.mem_flatten.mp ht
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      have h := ih hs
      have he := List.length_eraseIdx_add_one j.isLt
      simp only [paired, List.length_cons]
      omega

def weight (ν : α → ℕ) (A : List α) : ℕ := (A.map fun a => 2 * ν a + 1).sum

def pole (ν : α → ℕ) (t : Term α) : ℕ :=
  (t.pairs.map fun p => ν p.1 + ν p.2 + 1).sum

@[simp] theorem pole_unmatched (ν : α → ℕ) (a : α) (t : Term α) :
    pole ν (unmatched a t) = pole ν t := rfl

@[simp] theorem pole_paired (ν : α → ℕ) (a b : α) (s : ℕ) (t : Term α) :
    pole ν (paired a b s t) = ν a + ν b + 1 + pole ν t := rfl

@[simp] theorem weight_nil (ν : α → ℕ) : weight ν [] = 0 := rfl

@[simp] theorem weight_cons (ν : α → ℕ) (a : α) (A : List α) :
    weight ν (a :: A) = 2 * ν a + 1 + weight ν A := rfl

theorem weight_eraseIdx (ν : α → ℕ) (B : List α) (j : Fin B.length) :
    weight ν (B.eraseIdx j) + (2 * ν B[j] + 1) = weight ν B := by
  induction B with
  | nil => exact Fin.elim0 j
  | cons b B ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [Nat.add_comm]
    · simpa only [Fin.getElem_fin, Fin.val_succ, List.getElem_cons_succ,
        List.eraseIdx_cons_succ, weight_cons, Nat.add_assoc] using
        congrArg (fun n : ℕ => 2 * ν b + 1 + n) (ih j)

theorem term_energy (ν : α → ℕ) {A B : List α} {t : Term α}
    (ht : t ∈ terms A B) :
    2 * pole ν t + weight ν t.remaining = weight ν A + weight ν B := by
  induction A generalizing B t with
  | nil =>
    simp only [terms, List.mem_singleton] at ht
    subst t
    simp [pole]
  | cons a A ih =>
    simp only [terms, List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      have h := ih hs
      simp only [pole_unmatched, unmatched_remaining, weight_cons]
      omega
    · obtain ⟨l, hl, ht⟩ := List.mem_flatten.mp ht
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      have h := ih hs
      have he := weight_eraseIdx ν B j
      simp only [pole_paired, paired_remaining, weight_cons]
      omega

theorem sum_map_eraseIdx (w : α → ℕ) (A : List α) (j : Fin A.length) :
    ((A.eraseIdx j).map w).sum + w A[j] = (A.map w).sum := by
  induction A with
  | nil => exact Fin.elim0 j
  | cons a A ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [Nat.add_comm]
    · simpa only [Fin.getElem_fin, Fin.val_succ, List.getElem_cons_succ,
        List.eraseIdx_cons_succ, List.map_cons, List.sum_cons, Nat.add_assoc] using
        congrArg (fun n : ℕ => w a + n) (ih j)

theorem term_weight_conservation (w : α → ℕ) {A B : List α} {t : Term α}
    (ht : t ∈ terms A B) :
    (t.remaining.map w).sum + (t.pairs.map fun p => w p.1 + w p.2).sum =
      (A.map w).sum + (B.map w).sum := by
  induction A generalizing B t with
  | nil =>
    simp only [terms, List.mem_singleton] at ht
    subst t
    simp
  | cons a A ih =>
    simp only [terms, List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      have h := ih hs
      simp only [unmatched, List.map_cons, List.sum_cons]
      omega
    · obtain ⟨l, hl, ht⟩ := List.mem_flatten.mp ht
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      have h := ih hs
      have he := sum_map_eraseIdx w B j
      simp only [paired, List.map_cons, List.sum_cons]
      omega

theorem pair_mem_sources {A B : List α} {t : Term α}
    (ht : t ∈ terms A B) {p : α × α} (hp : p ∈ t.pairs) : p.1 ∈ A ∧ p.2 ∈ B := by
  induction A generalizing B t with
  | nil =>
    simp only [terms, List.mem_singleton] at ht
    subst t
    simp at hp
  | cons a A ih =>
    simp only [terms, List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      have h := ih hs hp
      exact ⟨List.mem_cons_of_mem _ h.1, h.2⟩
    · obtain ⟨l, hl, ht⟩ := List.mem_flatten.mp ht
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      change p ∈ (a, B[j]) :: s.pairs at hp
      rcases List.mem_cons.mp hp with he | hp
      · subst p
        exact ⟨by simp, List.getElem_mem j.isLt⟩
      · have h := ih hs hp
        exact ⟨List.mem_cons_of_mem _ h.1, List.eraseIdx_subset h.2⟩

theorem length_le_weight (ν : α → ℕ) (A : List α) : A.length ≤ weight ν A := by
  induction A with
  | nil => simp
  | cons a A ih => simp only [List.length_cons, weight_cons]; omega

theorem incomplete_pole_bound (ν : α → ℕ) {A B : List α} {t : Term α}
    (ht : t ∈ terms A B) (hparity : Even (A.length + B.length))
    (hne : t.remaining ≠ []) :
    pole ν t ≤ (weight ν A + weight ν B) / 2 - 1 := by
  have hc := term_length ht
  have he := term_energy ν ht
  have hw := length_le_weight ν t.remaining
  have hn := List.length_pos_iff.mpr hne
  rw [Nat.even_iff] at hparity
  omega

variable (R : Type*) [CommRing R]

theorem term_parity {A B : List α} {t : Term α} (ht : t ∈ terms A B) :
    (-1 : R) ^ t.remaining.length = (-1 : R) ^ (A.length + B.length) := by
  have h := term_length ht
  calc
    _ = (-1 : R) ^ t.remaining.length * ((-1 : R) ^ 2) ^ t.pairs.length := by simp
    _ = (-1 : R) ^ (t.remaining.length + 2 * t.pairs.length) := by
      rw [← pow_mul, ← pow_add]
    _ = _ := by rw [h]

def coefficient (κ : α → α → R) (t : Term α) : R :=
  (t.sign : R) * (t.pairs.map fun p => κ p.1 p.2).prod

@[simp] theorem coefficient_unmatched (κ : α → α → R) (a : α) (t : Term α) :
    coefficient R κ (unmatched a t) = coefficient R κ t := rfl

@[simp] theorem coefficient_paired (κ : α → α → R) (a b : α) (s : ℕ) (t : Term α) :
    coefficient R κ (paired a b s t) =
      ((-1 : R) ^ s * κ a b) * coefficient R κ t := by
  simp [coefficient, paired, mul_assoc, mul_comm, mul_left_comm]

noncomputable def evaluate (κ : α → α → R) (u v : α → OneParticle R)
    (T : List (Term α)) (x : Fock R) : Fock R :=
  (T.map fun t => coefficient R κ t •
    Fock.normalList R (t.remaining.map fun a => (u a, v a)) x).sum

@[simp] theorem evaluate_nil (κ : α → α → R) (u v : α → OneParticle R) (x : Fock R) :
    evaluate R κ u v [] x = 0 := rfl

@[simp] theorem evaluate_cons (κ : α → α → R) (u v : α → OneParticle R)
    (t : Term α) (T : List (Term α)) (x : Fock R) :
    evaluate R κ u v (t :: T) x = coefficient R κ t •
      Fock.normalList R (t.remaining.map fun a => (u a, v a)) x +
        evaluate R κ u v T x := rfl

theorem evaluate_append (κ : α → α → R) (u v : α → OneParticle R)
    (T U : List (Term α)) (x : Fock R) :
    evaluate R κ u v (T ++ U) x =
      evaluate R κ u v T x + evaluate R κ u v U x := by
  simp [evaluate]

theorem evaluate_paired (κ : α → α → R) (u v : α → OneParticle R)
    (a b : α) (s : ℕ) (T : List (Term α)) (x : Fock R) :
    evaluate R κ u v (T.map (paired a b s)) x =
      ((-1 : R) ^ s * κ a b) • evaluate R κ u v T x := by
  induction T with
  | nil => simp
  | cons t T ih =>
    simp only [List.map_cons, evaluate_cons, coefficient_paired, paired_remaining,
      smul_add, smul_smul, ih]

theorem evaluate_unmatched (κ : α → α → R) (u v : α → OneParticle R)
    (a : α) (T : List (Term α)) (s : R)
    (h : ∀ t ∈ T, (-1 : R) ^ t.remaining.length = s) (x : Fock R) :
    evaluate R κ u v (T.map (unmatched a)) x =
      Fock.createVector R (u a) (evaluate R κ u v T x) +
        s • evaluate R κ u v T (Fock.contractVector R (v a) x) := by
  induction T with
  | nil => simp
  | cons t T ih =>
    have ht := h t (by simp)
    have hT : ∀ t ∈ T, (-1 : R) ^ t.remaining.length = s :=
      fun t ht => h t (List.mem_cons_of_mem _ ht)
    simp only [List.map_cons, evaluate_cons, coefficient_unmatched, unmatched_remaining,
      Fock.normalList_cons, List.length_map, ht]
    rw [ih hT]
    simp only [map_add, map_smul, smul_add, smul_smul]
    module

theorem evaluate_flatten (κ : α → α → R) (u v : α → OneParticle R)
    (T : List (List (Term α))) (x : Fock R) :
    evaluate R κ u v T.flatten x =
      (T.map fun t => evaluate R κ u v t x).sum := by
  induction T with
  | nil => simp
  | cons t T ih => simp [evaluate_append, ih]

theorem evaluate_terms_cons (κ : α → α → R) (u v : α → OneParticle R)
    (a : α) (A B : List α) (x : Fock R) :
    evaluate R κ u v (terms (a :: A) B) x =
      Fock.createVector R (u a) (evaluate R κ u v (terms A B) x) +
        (-1 : R) ^ (A.length + B.length) •
          evaluate R κ u v (terms A B) (Fock.contractVector R (v a) x) +
      ∑ j : Fin B.length, ((-1 : R) ^ (A.length + (j : ℕ)) * κ a B[j]) •
        evaluate R κ u v (terms A (B.eraseIdx j)) x := by
  classical
  rw [terms, evaluate_append, evaluate_unmatched R κ u v a _ _
    (fun t ht => term_parity R ht), evaluate_flatten]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, evaluate_paired]

theorem contract_normalList_map (u v : α → OneParticle R) (d : OneParticle R)
    (B : List α) (x : Fock R) :
    Fock.contractVector R d (Fock.normalList R (B.map fun a => (u a, v a)) x) =
      (∑ j : Fin B.length,
        ((-1 : R) ^ (j : ℕ) * Fock.coordinateDual R d (u B[j])) •
          Fock.normalList R ((B.eraseIdx j).map fun a => (u a, v a)) x) +
      (-1 : R) ^ B.length •
        Fock.normalList R (B.map fun a => (u a, v a)) (Fock.contractVector R d x) := by
  have h := Fock.contractVector_normalList R d (B.map fun a => (u a, v a)) x
  rw [Fock.wickDerivative_eq_sum] at h
  have hs :
      (∑ j : Fin (B.map fun a => (u a, v a)).length,
        ((-1 : R) ^ (j : ℕ) *
          Fock.coordinateDual R d (B.map fun a => (u a, v a))[j].1) •
          Fock.normalList R ((B.map fun a => (u a, v a)).eraseIdx j) x) =
      ∑ j : Fin B.length,
        ((-1 : R) ^ (j : ℕ) * Fock.coordinateDual R d (u B[j])) •
          Fock.normalList R ((B.eraseIdx j).map fun a => (u a, v a)) x := by
    apply Fintype.sum_equiv (finCongr (show
      (B.map fun a => (u a, v a)).length = B.length by simp))
    intro j
    simp [Fin.getElem_fin, List.getElem_map, List.eraseIdx_map]
  rw [hs] at h
  simpa only [List.length_map] using h

theorem normalList_product (u v : α → OneParticle R) (A B : List α) (x : Fock R) :
    Fock.normalList R (A.map fun a => (u a, v a))
        (Fock.normalList R (B.map fun a => (u a, v a)) x) =
      evaluate R (fun a b => Fock.coordinateDual R (v a) (u b)) u v (terms A B) x := by
  classical
  induction A generalizing B x with
  | nil => simp [terms, evaluate, coefficient]
  | cons a A ih =>
    rw [evaluate_terms_cons]
    simp only [List.map_cons, Fock.normalList_cons, List.length_map]
    rw [contract_normalList_map]
    simp only [map_add, map_sum, map_smul, Finset.smul_sum, smul_add, smul_smul]
    simp only [ih]
    simp only [pow_add, mul_assoc]
    module

section ChangeForm

variable {M : Type*} [AddCommGroup M] [Module R M]

def alternatingPart (B : LinearMap.BilinForm R M) : LinearMap.BilinForm R M :=
  B - B.flip

@[simp] theorem alternatingPart_apply (B : LinearMap.BilinForm R M) (x y : M) :
    alternatingPart R B x y = B x y - B y x := rfl

theorem alternatingPart_isAlt (B : LinearMap.BilinForm R M) :
    (alternatingPart R B).IsAlt := by
  intro x
  exact sub_self (B x x)

variable {N : Type*} [AddCommGroup N] [Module R N]

def forwardForm (γ : M →ₗ[R] N →ₗ[R] R) : LinearMap.BilinForm R (M × N) :=
  LinearMap.mk₂ R (fun x y => γ x.1 y.2)
    (by intro x x' y; simp)
    (by intro c x y; simp)
    (by intro x y y'; simp)
    (by intro c x y; simp)

def crossForm (γ : M →ₗ[R] N →ₗ[R] R) : LinearMap.BilinForm R (M × N) :=
  alternatingPart R (forwardForm R γ)

@[simp] theorem crossForm_apply (γ : M →ₗ[R] N →ₗ[R] R) (x y : M × N) :
    crossForm R γ x y = γ x.1 y.2 - γ y.1 x.2 := rfl

theorem crossForm_isAlt (γ : M →ₗ[R] N →ₗ[R] R) : (crossForm R γ).IsAlt :=
  alternatingPart_isAlt R _

@[simp] theorem crossForm_left_right (γ : M →ₗ[R] N →ₗ[R] R) (x : M) (y : N) :
    crossForm R γ (x, 0) (0, y) = γ x y := by simp

@[simp] theorem crossForm_right_left (γ : M →ₗ[R] N →ₗ[R] R) (x : M) (y : N) :
    crossForm R γ (0, y) (x, 0) = -γ x y := by simp

@[simp] theorem crossForm_left_left (γ : M →ₗ[R] N →ₗ[R] R) (x y : M) :
    crossForm R γ (x, 0) (y, 0) = 0 := by simp

@[simp] theorem crossForm_right_right (γ : M →ₗ[R] N →ₗ[R] R) (x y : N) :
    crossForm R γ (0, x) (0, y) = 0 := by simp

theorem negative_form_zero (B : LinearMap.BilinForm R M) (hB : B.IsAlt) :
    (-B).toQuadraticMap = (0 : QuadraticForm R M) - 0 := by
  rw [sub_self]
  apply LinearMap.BilinMap.toQuadraticMap_eq_zero.mpr
  intro x
  change -(B x x) = 0
  rw [hB x, neg_zero]

noncomputable def twist (B : LinearMap.BilinForm R M) (hB : B.IsAlt) :
    ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.changeForm (negative_form_zero R B hB)

@[simp] theorem twist_one (B : LinearMap.BilinForm R M) (hB : B.IsAlt) :
    twist R B hB 1 = 1 := by
  unfold twist
  exact CliffordAlgebra.changeForm_one _

@[simp] theorem twist_ι (B : LinearMap.BilinForm R M) (hB : B.IsAlt) (m : M) :
    twist R B hB (ExteriorAlgebra.ι R m) = ExteriorAlgebra.ι R m := by
  unfold twist
  exact CliffordAlgebra.changeForm_ι _ _

theorem twist_ι_mul (B : LinearMap.BilinForm R M) (hB : B.IsAlt)
    (m : M) (x : ExteriorAlgebra R M) :
    twist R B hB (ExteriorAlgebra.ι R m * x) =
      ExteriorAlgebra.ι R m * twist R B hB x +
        CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) (B m)
          (twist R B hB x) := by
  simp only [twist, CliffordAlgebra.changeForm_ι_mul, LinearMap.neg_apply,
    map_neg, sub_neg_eq_add]

theorem twist_two (B : LinearMap.BilinForm R M) (hB : B.IsAlt) (m n : M) :
    twist R B hB (ExteriorAlgebra.ι R m * ExteriorAlgebra.ι R n) =
      ExteriorAlgebra.ι R m * ExteriorAlgebra.ι R n +
        algebraMap R (ExteriorAlgebra R M) (B m n) := by
  rw [twist_ι_mul, twist_ι, CliffordAlgebra.contractLeft_ι]

theorem twist_block_exchange (B : LinearMap.BilinForm R M) (hB : B.IsAlt)
    (m n : ℕ) (a : Fin m → M) (b : Fin n → M) :
    twist R B hB (ExteriorAlgebra.ιMulti R m a * ExteriorAlgebra.ιMulti R n b) =
      ((-1 : ℤˣ) ^ (m * n)) •
        twist R B hB (ExteriorAlgebra.ιMulti R n b * ExteriorAlgebra.ιMulti R m a) := by
  simpa only [Units.smul_def, map_zsmul, Nat.mul_comm] using
    congrArg (twist R B hB) (ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm R a b)

end ChangeForm

end Lemmata.FockCircuits.Matching
