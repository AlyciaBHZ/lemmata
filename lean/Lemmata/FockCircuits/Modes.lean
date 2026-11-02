module

public import Lemmata.FockCircuits.Exterior
public import Lemmata.FockCircuits.Pascal
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic.Abel

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.Fock

variable (R : Type*) [CommRing R]

noncomputable def coordinateDual :
    OneParticle R →ₗ[R] Module.Dual R (OneParticle R) :=
  Finsupp.linearCombination R fun i : ℕ => Finsupp.lapply i

theorem coordinateDual_apply (v w : OneParticle R) :
    coordinateDual R v w = ∑ i ∈ v.support, v i * w i := by
  simp only [coordinateDual, Finsupp.linearCombination_apply, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul]

@[simp] theorem coordinateDual_single (i : ℕ) (r : R) (v : OneParticle R) :
    coordinateDual R (Finsupp.single i r) v = r * v i := by
  simp [coordinateDual, Finsupp.lapply_apply, smul_eq_mul]

noncomputable def createVector (v : OneParticle R) : Fock R →ₗ[R] Fock R :=
  LinearMap.mulLeft R (ExteriorAlgebra.ι R v)

noncomputable def contractVector (v : OneParticle R) : Fock R →ₗ[R] Fock R :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (OneParticle R)))
    (coordinateDual R v)

@[simp] theorem createVector_apply (v : OneParticle R) (x : Fock R) :
    createVector R v x = ExteriorAlgebra.ι R v * x := rfl

@[simp] theorem createVector_single (i : ℕ) (x : Fock R) :
    createVector R (Finsupp.single i 1) x = create R i x := rfl

@[simp] theorem contractVector_single (i : ℕ) :
    contractVector R (Finsupp.single i 1) = contract R i := by
  simp [contractVector, coordinateDual, contract]

@[simp] theorem contractVector_one (v : OneParticle R) :
    contractVector R v 1 = 0 :=
  CliffordAlgebra.contractLeft_one _ _

@[simp] theorem createVector_createVector_self (v : OneParticle R) (x : Fock R) :
    createVector R v (createVector R v x) = 0 := by
  simp only [createVector_apply, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

@[simp] theorem contractVector_contractVector_self (v : OneParticle R) (x : Fock R) :
    contractVector R v (contractVector R v x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft _ _

theorem createVector_anticommute (v w : OneParticle R) (x : Fock R) :
    createVector R v (createVector R w x) +
      createVector R w (createVector R v x) = 0 := by
  simp only [createVector_apply, ← mul_assoc, ← add_mul,
    ExteriorAlgebra.ι_add_mul_swap, zero_mul]

theorem contractVector_anticommute (v w : OneParticle R) (x : Fock R) :
    contractVector R v (contractVector R w x) +
      contractVector R w (contractVector R v x) = 0 := by
  have h := CliffordAlgebra.contractLeft_comm
    (Q := (0 : QuadraticForm R (OneParticle R)))
    (coordinateDual R v) (coordinateDual R w) x
  exact eq_neg_iff_add_eq_zero.mp h

theorem contractVector_createVector (v w : OneParticle R) (x : Fock R) :
    contractVector R v (createVector R w x) =
      coordinateDual R v w • x -
        createVector R w (contractVector R v x) := by
  exact CliffordAlgebra.contractLeft_ι_mul
    (coordinateDual R v) w x

theorem contractVector_createVector_add (v w : OneParticle R) (x : Fock R) :
    contractVector R v (createVector R w x) +
      createVector R w (contractVector R v x) =
        (∑ i ∈ v.support, v i * w i) • x := by
  rw [contractVector_createVector, sub_add_cancel, coordinateDual_apply]

noncomputable def field (u v : OneParticle R) : Fock R →ₗ[R] Fock R :=
  createVector R u + contractVector R v

noncomputable def normalTwo (u v p q : OneParticle R) : Fock R →ₗ[R] Fock R :=
  (createVector R u).comp (createVector R p) +
    (createVector R u).comp (contractVector R q) -
    (createVector R p).comp (contractVector R v) +
    (contractVector R v).comp (contractVector R q)

theorem field_field (u v p q : OneParticle R) (x : Fock R) :
    field R u v (field R p q x) =
      normalTwo R u v p q x + coordinateDual R v p • x := by
  change
    createVector R u (createVector R p x + contractVector R q x) +
      contractVector R v (createVector R p x + contractVector R q x) =
    (createVector R u (createVector R p x) +
      createVector R u (contractVector R q x) -
      createVector R p (contractVector R v x) +
      contractVector R v (contractVector R q x)) + coordinateDual R v p • x
  rw [map_add, map_add, contractVector_createVector]
  abel

@[simp] theorem normalTwo_self (u v : OneParticle R) :
    normalTwo R u v u v = 0 := by
  apply LinearMap.ext
  intro x
  change
    createVector R u (createVector R u x) +
      createVector R u (contractVector R v x) -
      createVector R u (contractVector R v x) +
      contractVector R v (contractVector R v x) = 0
  rw [createVector_createVector_self, contractVector_contractVector_self]
  abel

theorem normalTwo_anticommute (u v p q : OneParticle R) (x : Fock R) :
    normalTwo R u v p q x + normalTwo R p q u v x = 0 := by
  have hc := createVector_anticommute R u p x
  have hd := contractVector_anticommute R v q x
  change
    (createVector R u (createVector R p x) +
      createVector R u (contractVector R q x) -
      createVector R p (contractVector R v x) +
      contractVector R v (contractVector R q x)) +
    (createVector R p (createVector R u x) +
      createVector R p (contractVector R v x) -
      createVector R u (contractVector R q x) +
      contractVector R q (contractVector R v x)) = 0
  calc
    _ = (createVector R u (createVector R p x) +
          createVector R p (createVector R u x)) +
        (contractVector R v (contractVector R q x) +
          contractVector R q (contractVector R v x)) := by abel
    _ = 0 := by rw [hc, hd, zero_add]

noncomputable def cutoffVector (N : ℕ) (a : ℕ → R) : OneParticle R :=
  ∑ k ∈ Finset.range N, Finsupp.single k (a k)

@[simp] theorem cutoffVector_apply (N : ℕ) (a : ℕ → R) (k : ℕ) :
    cutoffVector R N a k = if k < N then a k else 0 := by
  classical
  simp [cutoffVector, Finsupp.single_apply, eq_comm]

theorem coordinateDual_cutoffVector (N : ℕ) (a : ℕ → R) (v : OneParticle R) :
    coordinateDual R (cutoffVector R N a) v =
      ∑ k ∈ Finset.range N, a k * v k := by
  classical
  simp [cutoffVector, coordinateDual_single]

theorem coordinateDual_cutoffVector_cutoffVector
    (N : ℕ) (a b : ℕ → R) :
    coordinateDual R (cutoffVector R N a) (cutoffVector R N b) =
      ∑ k ∈ Finset.range N, a k * b k := by
  rw [coordinateDual_cutoffVector]
  apply Finset.sum_congr rfl
  intro k hk
  rw [cutoffVector_apply, ite_eq_left (Finset.mem_range.mp hk)]

def contractionCoefficient (m n : ℕ) : ℤ :=
  (-1 : ℤ) ^ m * ((m + n).choose m : ℤ)

theorem negative_mul_positive (m n k : ℕ) :
    negativeCoefficient m k * positiveCoefficient n k =
      contractionCoefficient m n * ((k + m).choose (m + n) : ℤ) := by
  have hc : (k + m).choose m * k.choose n =
      (m + n).choose m * (k + m).choose (m + n) := by
    simpa only [Nat.add_sub_cancel_right, Nat.add_sub_cancel_left, Nat.mul_comm] using
      (Nat.choose_mul (n := k + m) (k := m + n) (s := m) (Nat.le_add_right m n)).symm
  unfold negativeCoefficient positiveCoefficient contractionCoefficient
  simp only [mul_assoc]
  congr 1
  exact_mod_cast hc

noncomputable def positiveVector (N m : ℕ) : OneParticle R :=
  cutoffVector R N fun k => (positiveCoefficient m k : R)

noncomputable def negativeVector (N m : ℕ) : OneParticle R :=
  cutoffVector R N fun k => (negativeCoefficient m k : R)

theorem coordinateDual_negative_positive (N m n : ℕ) :
    coordinateDual R (negativeVector R N m) (positiveVector R N n) =
      (contractionCoefficient m n : R) *
        ∑ k ∈ Finset.range N, (((k + m).choose (m + n) : ℤ) : R) := by
  rw [negativeVector, positiveVector, coordinateDual_cutoffVector_cutoffVector,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [Int.coe_castRingHom, Int.cast_mul] using
    congrArg (Int.castRingHom R) (negative_mul_positive m n k)

theorem finite_contraction (N m n : ℕ) (x : Fock R) :
    contractVector R (negativeVector R N m)
        (createVector R (positiveVector R N n) x) +
      createVector R (positiveVector R N n)
        (contractVector R (negativeVector R N m) x) =
      ((contractionCoefficient m n : R) *
        ∑ k ∈ Finset.range N, (((k + m).choose (m + n) : ℤ) : R)) • x := by
  rw [contractVector_createVector, sub_add_cancel, coordinateDual_negative_positive]

end Lemmata.FockCircuits.Fock
