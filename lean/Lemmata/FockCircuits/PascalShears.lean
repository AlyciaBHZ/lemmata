module

public import Lemmata.FockCircuits.Shear
public import Lemmata.FockCircuits.Pascal
public import Mathlib.Tactic.Linarith
public import Lemmata.FockCircuits.Modes

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.Fock

variable (R : Type*) [CommRing R]

noncomputable def linearShears : List (ℕ × ℕ × R) → OneParticle R →ₗ[R] OneParticle R
  | [] => LinearMap.id
  | s :: rest => (shearLinear R s.2.2 s.1 s.2.1).comp (linearShears rest)

theorem linearShears_append (A B : List (ℕ × ℕ × R)) :
    linearShears R (A ++ B) = (linearShears R A).comp (linearShears R B) := by
  induction A with
  | nil => rfl
  | cons a A ih => simp only [List.cons_append, linearShears, ih, LinearMap.comp_assoc]

theorem linearShears_same_target (t : ℕ) (S : List (ℕ × R))
    (ht : ∀ s ∈ S, s.1 ≠ t) (v : OneParticle R) :
    linearShears R (S.map fun s => (s.1, t, s.2)) v =
      v + (S.map fun s => s.2 * v s.1).sum • Finsupp.single t 1 := by
  induction S with
  | nil => simp [linearShears]
  | cons s S ih =>
    have hst : t ≠ s.1 := (ht s (by simp)).symm
    have hS : ∀ a ∈ S, a.1 ≠ t := fun a ha => ht a (by simp [ha])
    simp only [List.map_cons, linearShears, LinearMap.comp_apply, ih hS,
      shearLinear_apply, List.sum_cons, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_apply, ite_eq_right hst, smul_eq_mul, mul_zero, add_zero,
      add_smul]
    abel

noncomputable def raisingStage (L : ℕ) : List (ℕ × ℕ × R) :=
  (Finset.range L).toList.map fun i => (i, L, (L.choose i : R))

theorem raisingStage_apply (L : ℕ) (v : OneParticle R) :
    linearShears R (raisingStage R L) v =
      v + (∑ i ∈ Finset.range L, (L.choose i : R) * v i) • Finsupp.single L 1 := by
  have h := linearShears_same_target R L
    ((Finset.range L).toList.map fun i => (i, (L.choose i : R)))
    (by
      intro s hs
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs
      have hi' := Finset.mem_range.mp (Finset.mem_toList.mp hi)
      omega) v
  simpa only [raisingStage, List.map_map, Function.comp_def,
    Finset.sum_map_toList] using h

theorem raisingStage_single (L m : ℕ) :
    linearShears R (raisingStage R L) (Finsupp.single m 1) =
      Finsupp.single m 1 +
        (if m < L then (L.choose m : R) else 0) • Finsupp.single L 1 := by
  rw [raisingStage_apply]
  congr 2
  simp [Finsupp.single_apply, eq_comm]

noncomputable def finitePascal (L : ℕ) : OneParticle R →ₗ[R] OneParticle R :=
  Finsupp.linearCombination R fun m =>
    if m < L then ∑ k ∈ Finset.range L, (k.choose m : R) • Finsupp.single k 1
    else Finsupp.single m 1

theorem finitePascal_single (L m : ℕ) :
    finitePascal R L (Finsupp.single m 1) =
      if m < L then ∑ k ∈ Finset.range L, (k.choose m : R) • Finsupp.single k 1
      else Finsupp.single m 1 := by
  simp [finitePascal]

theorem finitePascal_single_apply (L m k : ℕ) :
    finitePascal R L (Finsupp.single m 1) k =
      if m < L then (if k < L then (k.choose m : R) else 0)
      else if m = k then 1 else 0 := by
  rw [finitePascal_single]
  split_ifs <;> simp_all [Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, eq_comm]

theorem finitePascal_succ (L : ℕ) :
    finitePascal R (L + 1) =
      (finitePascal R L).comp (linearShears R (raisingStage R L)) := by
  apply (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).ext
  intro m
  simp only [Finsupp.coe_basisSingleOne, LinearMap.comp_apply,
    raisingStage_single, map_add, map_smul]
  apply Finsupp.ext
  intro k
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    finitePascal_single_apply]
  by_cases hm : m < L
  · by_cases hk : k < L
    · simp [hm, hk, show m < L + 1 by omega, show L ≠ k by omega] <;> omega
    · by_cases hkl : k = L
      · subst k
        simp [hm] <;> omega
      · simp [hm, hk, hkl, show ¬ k < L + 1 by omega, Ne.symm hkl] <;> omega
  · by_cases hml : m = L
    · subst m
      by_cases hk : k < L
      · simp [hk, Nat.choose_eq_zero_of_lt hk, show L ≠ k by omega]
      · by_cases hkl : k = L
        · subst k; simp
        · simp [hk, hkl, Ne.symm hkl, show ¬ k < L + 1 by omega]
    · simp [hm, hml, show ¬ m < L + 1 by omega]

noncomputable def raisingSteps : ℕ → List (ℕ × ℕ × R)
  | 0 => []
  | L + 1 => raisingSteps L ++ raisingStage R L

theorem raisingSteps_factorization (L : ℕ) :
    linearShears R (raisingSteps R L) = finitePascal R L := by
  induction L with
  | zero =>
    apply (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).ext
    intro m
    simp [raisingSteps, linearShears, finitePascal_single]
  | succ L ih =>
    rw [raisingSteps, linearShears_append, ih, ← finitePascal_succ]

theorem length_raisingSteps (L : ℕ) :
    2 * (raisingSteps R L).length = L * (L - 1) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [raisingSteps, List.length_append, raisingStage,
      List.length_map, Finset.length_toList, Finset.card_range]
    cases L with
    | zero => simp_all
    | succ L =>
      simp only [Nat.succ_sub_one] at ih ⊢
      nlinarith

theorem raisingSteps_oriented (L : ℕ) :
    ∀ s ∈ raisingSteps R L, s.1 < s.2.1 := by
  induction L with
  | zero => simp [raisingSteps]
  | succ L ih =>
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact ih s hs
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hs
      exact Finset.mem_range.mp (Finset.mem_toList.mp hi)

theorem coordinateDual_single_right (v : OneParticle R) (i : ℕ) :
    coordinateDual R v (Finsupp.single i 1) = v i := by
  rw [coordinateDual_apply]
  by_cases hi : i ∈ v.support
  · simp [Finsupp.single_apply, hi]
  · have hvi : v i = 0 := Finsupp.notMem_support_iff.mp hi
    simp [Finsupp.single_apply, hi, hvi]

theorem shearLinear_adjoint (a : R) (i j : ℕ) (v w : OneParticle R) :
    coordinateDual R (shearLinear R a i j v) w =
      coordinateDual R v (shearLinear R a j i w) := by
  simp only [shearLinear_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, coordinateDual_single, coordinateDual_single_right,
    one_mul, smul_eq_mul]
  ring

def transposedSteps (S : List (ℕ × ℕ × R)) : List (ℕ × ℕ × R) :=
  S.reverse.map fun s => (s.2.1, s.1, s.2.2)

theorem linearShears_adjoint (S : List (ℕ × ℕ × R)) (v w : OneParticle R) :
    coordinateDual R (linearShears R S v) w =
      coordinateDual R v (linearShears R (transposedSteps R S) w) := by
  induction S generalizing w with
  | nil => rfl
  | cons s S ih =>
    rw [linearShears, LinearMap.comp_apply, shearLinear_adjoint, ih]
    simp only [transposedSteps, List.reverse_cons, List.map_append,
      List.map_singleton, linearShears_append, linearShears, LinearMap.comp_apply,
      LinearMap.id_apply]

theorem loweringSteps_pascal_single {L m : ℕ} (hm : m < L) :
    pascal R (Finsupp.single m 1) =
      (-1 : R) ^ m •
        linearShears R (transposedSteps R (raisingSteps R L)) (Finsupp.single m 1) := by
  apply Finsupp.ext
  intro k
  have h := linearShears_adjoint R (raisingSteps R L)
    (Finsupp.single k 1) (Finsupp.single m 1)
  rw [raisingSteps_factorization, coordinateDual_single_right,
    coordinateDual_single, one_mul, finitePascal_single_apply] at h
  rw [pascal_single_apply, Finsupp.smul_apply, smul_eq_mul, ← h]
  by_cases hk : k < L
  · simp [hm, hk]
  · have hmk : m < k := by omega
    simp [hk, Nat.choose_eq_zero_of_lt hmk, show k ≠ m by omega]

theorem transposed_raisingSteps_oriented (L : ℕ) :
    ∀ s ∈ transposedSteps R (raisingSteps R L), s.2.1 < s.1 := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact raisingSteps_oriented R L t (List.mem_reverse.mp ht)

noncomputable def signDiagonal : OneParticle R →ₗ[R] OneParticle R :=
  Finsupp.linearCombination R fun i : ℕ => (-1 : R) ^ i • Finsupp.single i 1

@[simp] theorem signDiagonal_single (m : ℕ) :
    signDiagonal R (Finsupp.single m 1) = (-1 : R) ^ m • Finsupp.single m 1 := by
  simp [signDiagonal]

theorem sign_word (I : List ℕ) :
    (I.map fun i => (-1 : R) ^ i • generator R i).prod =
      (I.map fun i => (-1 : R) ^ i).prod • (I.map (generator R)).prod := by
  induction I with
  | nil => simp
  | cons i I ih =>
    simp only [List.map_cons, List.prod_cons, ih, smul_mul_assoc,
      mul_smul_comm, smul_smul, mul_comm]

theorem signDiagonal_basis (I : Finset ℕ) :
    ExteriorAlgebra.map (signDiagonal R) (basis R I) =
      (I.sort.map fun i => (-1 : R) ^ i).prod • basis R I := by
  rw [basis_eq_sorted_prod, map_list_prod, List.map_map]
  have hg (i : ℕ) : ExteriorAlgebra.map (signDiagonal R) (generator R i) =
      (-1 : R) ^ i • generator R i := by
    simp only [generator, ExteriorAlgebra.map_apply_ι, signDiagonal_single, map_smul]
  simpa only [Function.comp_def, hg] using sign_word R I.sort

theorem pascalExterior_basis_factor {L : ℕ} (I : Finset ℕ)
    (hI : ∀ i ∈ I, i < L) :
    pascalExterior R (basis R I) =
      ExteriorAlgebra.map (linearShears R (transposedSteps R (raisingSteps R L)))
        (ExteriorAlgebra.map (signDiagonal R) (basis R I)) := by
  simp only [pascalExterior, basis_eq_sorted_prod, map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  have h := loweringSteps_pascal_single R (hI i (by simpa only [Finset.mem_sort] using hi))
  simpa only [Function.comp_def, generator, ExteriorAlgebra.map_apply_ι,
    signDiagonal_single, map_smul, LinearEquiv.coe_coe] using
      congrArg (ExteriorAlgebra.ι R) h

end Lemmata.FockCircuits.Fock
