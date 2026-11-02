module

public import Lemmata.FockCircuits.Modes
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Module

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Fock

open scoped BigOperators

variable (R : Type*) [CommRing R]

noncomputable def normalList (L : List (OneParticle R × OneParticle R)) :
    Fock R →ₗ[R] Fock R :=
  L.rec LinearMap.id fun a l n =>
    (createVector R a.1).comp n +
      (-1 : R) ^ l.length • n.comp (contractVector R a.2)

@[simp] theorem normalList_nil : normalList R [] = LinearMap.id := rfl

@[simp] theorem normalList_cons (a : OneParticle R × OneParticle R)
    (L : List (OneParticle R × OneParticle R)) (x : Fock R) :
    normalList R (a :: L) x = createVector R a.1 (normalList R L x) +
      (-1 : R) ^ L.length • normalList R L (contractVector R a.2 x) := rfl

noncomputable def wickDerivative (v : OneParticle R)
    (L : List (OneParticle R × OneParticle R)) : Fock R →ₗ[R] Fock R :=
  L.rec 0 fun a l d =>
    coordinateDual R v a.1 • normalList R l -
      (createVector R a.1).comp d +
      (-1 : R) ^ l.length • d.comp (contractVector R a.2)

@[simp] theorem wickDerivative_nil (v : OneParticle R) :
    wickDerivative R v [] = 0 := rfl

@[simp] theorem wickDerivative_cons (v : OneParticle R)
    (a : OneParticle R × OneParticle R)
    (L : List (OneParticle R × OneParticle R)) (x : Fock R) :
    wickDerivative R v (a :: L) x =
      coordinateDual R v a.1 • normalList R L x -
        createVector R a.1 (wickDerivative R v L x) +
        (-1 : R) ^ L.length • wickDerivative R v L (contractVector R a.2 x) := rfl

theorem contractVector_normalList (v : OneParticle R)
    (L : List (OneParticle R × OneParticle R)) (x : Fock R) :
    contractVector R v (normalList R L x) = wickDerivative R v L x +
      (-1 : R) ^ L.length • normalList R L (contractVector R v x) := by
  induction L generalizing x with
  | nil => simp
  | cons a L ih =>
    have hs : (-1 : R) ^ L.length * (-1 : R) ^ L.length = 1 := by
      rw [← mul_pow]
      simp
    have hdd : contractVector R v (contractVector R a.2 x) =
        -contractVector R a.2 (contractVector R v x) :=
      eq_neg_iff_add_eq_zero.mpr (contractVector_anticommute R v a.2 x)
    simp only [normalList_cons, wickDerivative_cons, List.length_cons]
    rw [map_add, map_smul, contractVector_createVector, ih, ih, hdd]
    simp only [map_add, map_smul, map_neg, smul_add,
      smul_neg, smul_smul, pow_succ, mul_neg, mul_one, neg_mul, neg_smul,
      hs, one_smul]
    module

theorem field_normalList (a : OneParticle R × OneParticle R)
    (L : List (OneParticle R × OneParticle R)) (x : Fock R) :
    field R a.1 a.2 (normalList R L x) =
      normalList R (a :: L) x + wickDerivative R a.2 L x := by
  change createVector R a.1 (normalList R L x) +
    contractVector R a.2 (normalList R L x) = _
  rw [contractVector_normalList, normalList_cons]
  abel

theorem wickDerivative_eq_sum (v : OneParticle R)
    (L : List (OneParticle R × OneParticle R)) (x : Fock R) :
    wickDerivative R v L x =
      ∑ j : Fin L.length, ((-1 : R) ^ (j : ℕ) * coordinateDual R v L[j].1) •
        normalList R (L.eraseIdx j) x := by
  classical
  induction L generalizing x with
  | nil => simp
  | cons a L ih =>
    rw [wickDerivative_cons, ih, ih]
    simp only [List.length_cons]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.getElem_fin, Fin.val_zero, pow_zero, one_mul, List.getElem_cons_zero,
      List.eraseIdx_cons_zero, Fin.val_succ, List.getElem_cons_succ,
      List.eraseIdx_cons_succ]
    calc
      _ = coordinateDual R v a.1 • normalList R L x +
          ∑ j : Fin L.length,
            (-createVector R a.1
              (((-1 : R) ^ (j : ℕ) * coordinateDual R v L[j].1) •
                normalList R (L.eraseIdx j) x) +
            (-1 : R) ^ L.length •
              (((-1 : R) ^ (j : ℕ) * coordinateDual R v L[j].1) •
                normalList R (L.eraseIdx j) (contractVector R a.2 x))) := by
        simp only [map_sum, Finset.smul_sum, Finset.sum_add_distrib,
          Finset.sum_neg_distrib]
        abel
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        have hlen := List.length_eraseIdx_add_one j.isLt
        have hs : (-1 : R) ^ L.length =
            -(-1 : R) ^ (L.eraseIdx j).length := by
          calc
            _ = (-1 : R) ^ ((L.eraseIdx j).length + 1) :=
              congrArg (fun n : ℕ => (-1 : R) ^ n) hlen.symm
            _ = _ := by rw [pow_succ]; simp
        rw [hs, normalList_cons]
        simp only [Fin.getElem_fin, Fin.val_succ, List.getElem_cons_succ,
          map_smul, smul_add, smul_smul, pow_succ]
        module

theorem field_normalList_eq_sum (a : OneParticle R × OneParticle R)
    (L : List (OneParticle R × OneParticle R)) (x : Fock R) :
    field R a.1 a.2 (normalList R L x) = normalList R (a :: L) x +
      ∑ j : Fin L.length,
        ((-1 : R) ^ (j : ℕ) * coordinateDual R a.2 L[j].1) •
          normalList R (L.eraseIdx j) x := by
  rw [field_normalList, wickDerivative_eq_sum]

theorem normalList_repeat (a : OneParticle R × OneParticle R)
    (L : List (OneParticle R × OneParticle R)) (x : Fock R) :
    normalList R (a :: a :: L) x = 0 := by
  have hs : (-1 : R) ^ L.length * (-1 : R) ^ L.length = 1 := by
    rw [← mul_pow]
    simp
  simp only [normalList_cons, List.length_cons, map_add, map_smul, smul_add,
    smul_smul, pow_succ, mul_neg, mul_one, neg_mul, neg_smul, hs, one_smul,
    createVector_createVector_self, contractVector_contractVector_self, map_zero]
  module

theorem normalList_swap (a b : OneParticle R × OneParticle R)
    (L : List (OneParticle R × OneParticle R)) (x : Fock R) :
    normalList R (a :: b :: L) x + normalList R (b :: a :: L) x = 0 := by
  have hs : (-1 : R) ^ L.length * (-1 : R) ^ L.length = 1 := by
    rw [← mul_pow]
    simp
  have hc := createVector_anticommute R a.1 b.1 (normalList R L x)
  have hd := contractVector_anticommute R b.2 a.2 x
  simp only [normalList_cons, List.length_cons, map_add, map_smul, smul_add,
    smul_smul, pow_succ, mul_neg, mul_one, neg_mul, neg_smul, hs, one_smul]
  calc
    _ = (createVector R a.1 (createVector R b.1 (normalList R L x)) +
          createVector R b.1 (createVector R a.1 (normalList R L x))) -
        normalList R L (contractVector R b.2 (contractVector R a.2 x) +
          contractVector R a.2 (contractVector R b.2 x)) := by
      simp only [map_add]
      module
    _ = 0 := by rw [hc, hd, map_zero, sub_self]

end Lemmata.FockCircuits.Fock
