module

public import Lemmata.FockCircuits.Matching
public import Lemmata.FockCircuits.BasisAction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Fold

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Fock

variable (R : Type*) [CommRing R]

noncomputable def creationLinear : OneParticle R →ₗ[R] Module.End R (Fock R) :=
  (Algebra.lmul R (Fock R)).toLinearMap.comp (ExteriorAlgebra.ι R)

noncomputable def contractionLinear : OneParticle R →ₗ[R] Module.End R (Fock R) :=
  (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (OneParticle R)))).comp
    (coordinateDual R)

@[simp] theorem creationLinear_apply (a : OneParticle R) :
    creationLinear R a = createVector R a := rfl

@[simp] theorem contractionLinear_apply (a : OneParticle R) :
    contractionLinear R a = contractVector R a := rfl

abbrev NormalPair := Module.End R (Fock R) × Module.End R (Fock R)

noncomputable def normalStep :
    (OneParticle R × OneParticle R) →ₗ[R] NormalPair R →ₗ[R] NormalPair R :=
  LinearMap.mk₂ R
    (fun a T => ((createVector R a.1).comp T.1 + T.2.comp (contractVector R a.2),
      -(createVector R a.1).comp T.2 - T.1.comp (contractVector R a.2)))
    (by
      intro a b T
      change ((creationLinear R (a.1 + b.1)).comp T.1 +
          T.2.comp (contractionLinear R (a.2 + b.2)),
        -(creationLinear R (a.1 + b.1)).comp T.2 -
          T.1.comp (contractionLinear R (a.2 + b.2))) = _
      simp only [map_add, LinearMap.add_comp, LinearMap.comp_add,
        creationLinear_apply, contractionLinear_apply, Prod.mk_add_mk]
      apply Prod.ext <;> module)
    (by
      intro c a T
      change ((creationLinear R (c • a.1)).comp T.1 +
          T.2.comp (contractionLinear R (c • a.2)),
        -(creationLinear R (c • a.1)).comp T.2 -
          T.1.comp (contractionLinear R (c • a.2))) = _
      simp only [map_smul, LinearMap.smul_comp, LinearMap.comp_smul,
        creationLinear_apply, contractionLinear_apply, Prod.smul_mk,
        smul_add, smul_sub, smul_neg])
    (by
      intro a T U
      apply Prod.ext <;>
        simp only [Prod.fst_add, Prod.snd_add, LinearMap.comp_add, LinearMap.add_comp] <;>
        module)
    (by
      intro c a T
      apply Prod.ext <;>
        simp only [Prod.smul_fst, Prod.smul_snd, LinearMap.comp_smul,
          LinearMap.smul_comp, smul_add, smul_sub, smul_neg])

theorem normalStep_square (a : OneParticle R × OneParticle R) (T : NormalPair R) :
    normalStep R a (normalStep R a T) = 0 := by
  apply Prod.ext
  · apply LinearMap.ext
    intro x
    change createVector R a.1
        (createVector R a.1 (T.1 x) + T.2 (contractVector R a.2 x)) +
      (-createVector R a.1 (T.2 (contractVector R a.2 x)) -
        T.1 (contractVector R a.2 (contractVector R a.2 x))) = 0
    rw [map_add, createVector_createVector_self,
      contractVector_contractVector_self, map_zero]
    module
  · apply LinearMap.ext
    intro x
    change -createVector R a.1
        (-createVector R a.1 (T.2 x) - T.1 (contractVector R a.2 x)) -
      (createVector R a.1 (T.1 (contractVector R a.2 x)) +
        T.2 (contractVector R a.2 (contractVector R a.2 x))) = 0
    rw [map_sub, map_neg, createVector_createVector_self,
      contractVector_contractVector_self, map_zero]
    module

noncomputable def normalPair :
    ExteriorAlgebra R (OneParticle R × OneParticle R) →ₗ[R] NormalPair R :=
  CliffordAlgebra.foldr (0 : QuadraticForm R (OneParticle R × OneParticle R))
    (normalStep R) (by intro a T; simpa using normalStep_square R a T)
    (LinearMap.id, LinearMap.id)

noncomputable def normalSymbol :
    ExteriorAlgebra R (OneParticle R × OneParticle R) →ₗ[R] Module.End R (Fock R) :=
  (LinearMap.fst R (Module.End R (Fock R)) (Module.End R (Fock R))).comp (normalPair R)

@[simp] theorem normalPair_one : normalPair R 1 = (LinearMap.id, LinearMap.id) := by
  unfold normalPair
  rw [CliffordAlgebra.foldr_one]

theorem normalPair_ι_mul (a : OneParticle R × OneParticle R)
    (x : ExteriorAlgebra R (OneParticle R × OneParticle R)) :
    normalPair R (ExteriorAlgebra.ι R a * x) = normalStep R a (normalPair R x) := by
  unfold normalPair
  rw [CliffordAlgebra.foldr_mul, CliffordAlgebra.foldr_ι]

theorem normalPair_word (L : List (OneParticle R × OneParticle R)) :
    normalPair R (L.map (ExteriorAlgebra.ι R)).prod =
      (normalList R L, (-1 : R) ^ L.length • normalList R L) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, normalPair_ι_mul, ih]
    apply Prod.ext
    · apply LinearMap.ext
      intro x
      change createVector R a.1 (normalList R L x) +
        (-1 : R) ^ L.length • normalList R L (contractVector R a.2 x) = _
      rfl
    · apply LinearMap.ext
      intro x
      have hs : (-1 : R) ^ L.length * (-1 : R) ^ L.length = 1 := by
        rw [← mul_pow]
        simp
      change -createVector R a.1 (((-1 : R) ^ L.length) • normalList R L x) -
        normalList R L (contractVector R a.2 x) = _
      simp only [normalList_cons, List.length_cons, LinearMap.smul_apply,
        map_smul, smul_add, smul_smul, pow_succ, mul_neg, mul_one, neg_smul,
        hs, one_smul]
      match_scalars <;>
        rcases neg_one_pow_eq_or R L.length with hsign | hsign <;>
        simp [hsign] <;> ring

theorem normalSymbol_word (L : List (OneParticle R × OneParticle R)) :
    normalSymbol R (L.map (ExteriorAlgebra.ι R)).prod = normalList R L := by
  change (normalPair R (L.map (ExteriorAlgebra.ι R)).prod).1 = _
  rw [normalPair_word]

noncomputable def augmentation : Fock R →ₐ[R] R :=
  ExteriorAlgebra.algebraMapInv

@[simp] theorem augmentation_ι (v : OneParticle R) :
    augmentation R (ExteriorAlgebra.ι R v) = 0 := by
  simp only [augmentation, ExteriorAlgebra.algebraMapInv,
    ExteriorAlgebra.lift_ι_apply, LinearMap.zero_apply]

@[simp] theorem augmentation_createVector (v : OneParticle R) (x : Fock R) :
    augmentation R (createVector R v x) = 0 := by
  rw [createVector_apply, map_mul, augmentation_ι, zero_mul]

theorem normalList_one (L : List (OneParticle R × OneParticle R)) :
    normalList R L 1 = (L.map fun a => ExteriorAlgebra.ι R a.1).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [normalList_cons, contractVector_one, map_zero, smul_zero,
      add_zero, ih, createVector_apply, List.map_cons, List.prod_cons]

theorem augmentation_normalList_one (L : List (OneParticle R × OneParticle R)) :
    augmentation R (normalList R L 1) = if L = [] then 1 else 0 := by
  rw [normalList_one]
  cases L with
  | nil => simp
  | cons a L => simp only [List.map_cons, List.prod_cons, map_mul,
      augmentation_ι, zero_mul, List.cons_ne_nil, ite_false]

theorem augmentation_normalList_creators (L : List (OneParticle R × OneParticle R))
    (x : Fock R) :
    augmentation R (normalList R L x) =
      augmentation R (normalList R (L.map fun a => (0, a.2)) x) := by
  induction L generalizing x with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, normalList_cons, map_add, map_smul,
      augmentation_createVector, zero_add, List.length_map]
    rw [ih]

theorem augmentation_basis (I : Finset ℕ) :
    augmentation R (basis R I) = if I = ∅ then 1 else 0 := by
  classical
  by_cases hI : I = ∅
  · subst I
    simp
  have hsort : I.sort ≠ [] := by
    intro hs
    have hc : I.card = 0 := by
      simpa only [Finset.length_sort, List.length_nil] using congrArg List.length hs
    exact hI (Finset.card_eq_zero.mp hc)
  obtain ⟨i, A, hA⟩ := List.exists_cons_of_ne_nil hsort
  rw [basis_eq_sorted_prod, hA, List.map_cons, List.prod_cons, map_mul]
  simp only [generator, augmentation_ι, zero_mul, hI, ite_false]

theorem augmentation_eq_basis_empty (x : Fock R) :
    augmentation R x = (basis R).repr x ∅ := by
  have he : (augmentation R).toLinearMap = (basis R).coord ∅ := by
    apply (basis R).ext
    intro I
    change augmentation R (basis R I) = (basis R).repr (basis R I) ∅
    rw [Module.Basis.repr_self_apply]
    exact augmentation_basis R I
  exact LinearMap.congr_fun he x

end Lemmata.FockCircuits.Fock
