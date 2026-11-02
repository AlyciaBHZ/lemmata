module

public import Lemmata.FockCircuits.PatternReconstruction
public import Mathlib.LinearAlgebra.FreeAlgebra
public import Mathlib.Data.List.OfFn

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace Lemmata.FockCircuits.Symmetric

open Patterns

noncomputable section

variable {R : Type*} {X : Type*} [CommSemiring R]

def rename (σ : Equiv.Perm X) : FreeAlgebra R X →ₐ[R] FreeAlgebra R X :=
  FreeAlgebra.lift R fun x => FreeAlgebra.ι R (σ x)

def IsSymmetric (p : FreeAlgebra R X) : Prop := ∀ σ : Equiv.Perm X, rename σ p = p

theorem rename_word (σ : Equiv.Perm X) (w : List X) :
    rename σ (word (R := R) w) = word (w.map σ) := by
  simp only [rename, word, map_list_prod, List.map_map, FreeAlgebra.lift_ι_apply,
    Function.comp_def]

theorem equiv_ι (x : X) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := R) (X := X) (FreeAlgebra.ι R x) =
      MonoidAlgebra.single (FreeMonoid.of x) 1 := by
  change FreeAlgebra.lift R (fun x => MonoidAlgebra.of R (FreeMonoid X) (FreeMonoid.of x))
    (FreeAlgebra.ι R x) = _
  rw [FreeAlgebra.lift_ι_apply]
  rfl

theorem equiv_word (w : List X) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := R) (X := X) (word (R := R) w) =
      MonoidAlgebra.single (FreeMonoid.ofList w) 1 := by
  induction w with
  | nil => simp only [word_nil, map_one, FreeMonoid.ofList_nil, MonoidAlgebra.one_def]
  | cons x w ih =>
    rw [word_cons, map_mul, equiv_ι, ih, MonoidAlgebra.single_mul_single]
    simp only [one_mul, FreeMonoid.ofList_cons]

def wordBasis (R : Type*) (X : Type*) [CommSemiring R] : Module.Basis (FreeMonoid X) R (FreeAlgebra R X) :=
  (MonoidAlgebra.basis (FreeMonoid X) R).map
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := R) (X := X)).symm.toLinearEquiv

theorem wordBasis_apply (w : FreeMonoid X) :
    wordBasis R X w = word (R := R) (FreeMonoid.toList w) := by
  apply (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := R) (X := X)).injective
  simp only [wordBasis, Module.Basis.map_apply, MonoidAlgebra.basis_apply,
    AlgEquiv.toLinearEquiv_apply, AlgEquiv.apply_symm_apply, equiv_word, FreeMonoid.ofList_toList]

def coefficient (w : List X) : FreeAlgebra R X →ₗ[R] R :=
  (Finsupp.lapply (FreeMonoid.ofList w)).comp (wordBasis R X).repr.toLinearMap

def coeff (p : FreeAlgebra R X) (w : List X) : R := coefficient w p

@[simp] theorem coeff_zero (w : List X) : coeff (0 : FreeAlgebra R X) w = 0 := map_zero _

@[simp] theorem coeff_sum {I : Type*} (s : Finset I) (f : I → FreeAlgebra R X) (w : List X) :
    coeff (∑ i ∈ s, f i) w = ∑ i ∈ s, coeff (f i) w := map_sum _ _ _

@[simp] theorem coeff_smul (c : R) (p : FreeAlgebra R X) (w : List X) :
    coeff (c • p) w = c * coeff p w := by
  exact (coefficient w).map_smul c p

theorem coeff_word (v w : List X) :
    coeff (word (R := R) v) w = if v = w then 1 else 0 := by
  classical
  have hb : wordBasis R X (FreeMonoid.ofList v) = word (R := R) v := by
    simpa only [FreeMonoid.toList_ofList] using wordBasis_apply (R := R) (FreeMonoid.ofList v)
  rw [← hb]
  change (wordBasis R X).repr (wordBasis R X (FreeMonoid.ofList v)) (FreeMonoid.ofList w) = _
  simp only [Module.Basis.repr_self, Finsupp.single_apply, FreeMonoid.ofList.injective.eq_iff]

theorem coeff_ext {p q : FreeAlgebra R X} (h : ∀ w : List X, coeff p w = coeff q w) : p = q := by
  apply (wordBasis R X).repr.injective
  ext w
  exact h (FreeMonoid.toList w)

theorem coeff_rename (σ : Equiv.Perm X) (p : FreeAlgebra R X) (w : List X) :
    coeff (rename σ p) (w.map σ) = coeff p w := by
  classical
  have hmap : Function.Injective (List.map σ) := List.map_injective_iff.mpr σ.injective
  have hlinear : (coefficient (R := R) (w.map σ)).comp (rename (R := R) σ).toLinearMap =
      coefficient (R := R) w := by
    apply (wordBasis R X).ext
    intro v
    rw [wordBasis_apply]
    change coeff (rename σ (word (R := R) (FreeMonoid.toList v))) (w.map σ) =
      coeff (word (R := R) (FreeMonoid.toList v)) w
    rw [rename_word]
    simp only [coeff_word, hmap.eq_iff]
  exact LinearMap.congr_fun hlinear p

theorem coeff_samePattern {k : ℕ} {p : FreeAlgebra R X} (hp : IsSymmetric p)
    (u v : Fin k → X) (h : SamePattern u v) :
    coeff p (List.ofFn u) = coeff p (List.ofFn v) := by
  obtain ⟨σ, hσ⟩ := (samePattern_iff_permutation u v).mp h
  have hv : List.ofFn v = (List.ofFn u).map σ := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact (hσ i).symm
  have hc := coeff_rename σ p (List.ofFn u)
  rw [hp σ] at hc
  rw [hv]
  exact hc.symm

def DegreeLE (d : ℕ) (p : FreeAlgebra R X) : Prop :=
  ∀ w : List X, d < w.length → coeff p w = 0

def homogeneousPart [Fintype X] (k : ℕ) (p : FreeAlgebra R X) : FreeAlgebra R X :=
  ∑ a : Fin k → X, coeff p (List.ofFn a) • word (List.ofFn a)

def exactPattern [Fintype X] {k : ℕ} (π : Setoid (Fin k)) : FreeAlgebra R X := by
  classical
  exact ∑ a : Fin k → X, if Setoid.ker a = π then word (List.ofFn a) else 0

def patternCoefficient [Fintype X] (p : FreeAlgebra R X) (k : ℕ) (π : Setoid (Fin k)) : R := by
  classical
  exact if h : ∃ a : Fin k → X, Setoid.ker a = π then coeff p (List.ofFn h.choose) else 0

theorem patternCoefficient_ker [Fintype X] {p : FreeAlgebra R X} (hp : IsSymmetric p)
    {k : ℕ} (a : Fin k → X) :
    patternCoefficient p k (Setoid.ker a) = coeff p (List.ofFn a) := by
  classical
  have ha : ∃ b : Fin k → X, Setoid.ker b = Setoid.ker a := ⟨a, rfl⟩
  rw [patternCoefficient, dite_eq_left ha]
  apply coeff_samePattern hp
  intro i j
  change (Setoid.ker ha.choose).r i j ↔ (Setoid.ker a).r i j
  rw [ha.choose_spec]

theorem coeff_exactPattern [Fintype X] {k : ℕ} (π : Setoid (Fin k)) (a : Fin k → X) :
    coeff (exactPattern (R := R) (X := X) π) (List.ofFn a) = if Setoid.ker a = π then 1 else 0 := by
  classical
  rw [exactPattern, coeff_sum]
  rw [Finset.sum_eq_single a]
  · split_ifs <;> simp [coeff_word]
  · intro b hb hba
    have hword : List.ofFn b ≠ List.ofFn a := fun h => hba (List.ofFn_injective h)
    split_ifs <;> simp only [coeff_zero, coeff_word, ite_eq_right hword]
  · simp

theorem coeff_homogeneousPart [Fintype X] (k : ℕ) (p : FreeAlgebra R X) (w : List X) :
    coeff (homogeneousPart k p) w = if w.length = k then coeff p w else 0 := by
  classical
  by_cases hk : w.length = k
  · rw [ite_eq_left hk]
    subst k
    rw [homogeneousPart, coeff_sum]
    simp only [coeff_smul, coeff_word]
    have hiff (a : Fin w.length → X) : List.ofFn a = w ↔ a = w.get := by
      constructor
      · intro h
        exact List.ofFn_injective (h.trans (List.ofFn_get w).symm)
      · rintro rfl
        exact List.ofFn_get w
    simp only [hiff, mul_ite, mul_one, mul_zero]
    simp
  · rw [ite_eq_right hk, homogeneousPart, coeff_sum]
    apply Finset.sum_eq_zero
    intro a ha
    have hword : List.ofFn a ≠ w := by
      intro h
      have hlength := congrArg List.length h
      simp only [List.length_ofFn] at hlength
      exact hk hlength.symm
    rw [coeff_smul, coeff_word, ite_eq_right hword, mul_zero]

theorem sum_homogeneousParts [Fintype X] (d : ℕ) (p : FreeAlgebra R X) (hp : DegreeLE d p) :
    p = ∑ k : Fin (d+1), homogeneousPart k.val p := by
  classical
  apply coeff_ext
  intro w
  rw [coeff_sum]
  simp only [coeff_homogeneousPart]
  by_cases hw : w.length ≤ d
  · let j : Fin (d+1) := ⟨w.length, by omega⟩
    have hiff (k : Fin (d+1)) : w.length = k.val ↔ k = j := by
      constructor
      · intro h
        apply Fin.ext
        exact h.symm
      · rintro rfl
        rfl
    simp only [hiff]
    simp
  · have hzero := hp w (by omega)
    rw [hzero]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hne : w.length ≠ k.val := by have := k.isLt; omega
    exact ite_eq_right hne

theorem homogeneousPart_eq_patterns [Fintype X] {p : FreeAlgebra R X}
    (hp : IsSymmetric p) (k : ℕ) :
    homogeneousPart k p = ∑ π : Setoid (Fin k), patternCoefficient p k π •
      exactPattern (R := R) (X := X) π := by
  classical
  simp only [homogeneousPart, exactPattern, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [patternCoefficient_ker hp]

theorem decomposition [Fintype X] (d : ℕ) (p : FreeAlgebra R X)
    (hsym : IsSymmetric p) (hdegree : DegreeLE d p) :
    p = ∑ k : Fin (d+1), ∑ π : Setoid (Fin k.val),
      patternCoefficient p k.val π • exactPattern (R := R) (X := X) π := by
  calc
    p = ∑ k : Fin (d+1), homogeneousPart k.val p := sum_homogeneousParts d p hdegree
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact homogeneousPart_eq_patterns hsym k.val

end

end Lemmata.FockCircuits.Symmetric
