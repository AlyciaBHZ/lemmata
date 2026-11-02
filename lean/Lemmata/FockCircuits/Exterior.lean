module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.Algebra.Group.Nat.Even

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits

abbrev OneParticle (R : Type*) [Zero R] := ℕ →₀ R

abbrev Fock (R : Type*) [CommRing R] := ExteriorAlgebra R (OneParticle R)

def doubledEnergy (I : Finset ℕ) : ℕ := ∑ i ∈ I, (2 * i + 1)

theorem doubledEnergy_eq (I : Finset ℕ) :
    doubledEnergy I = 2 * (∑ i ∈ I, i) + I.card := by
  simp [doubledEnergy, Finset.sum_add_distrib, Finset.mul_sum]

theorem doubledEnergy_mod_two (I : Finset ℕ) :
    doubledEnergy I % 2 = I.card % 2 := by
  simp [doubledEnergy_eq, Nat.add_mod]

theorem even_doubledEnergy_iff (I : Finset ℕ) :
    Even (doubledEnergy I) ↔ Even I.card := by
  simp only [Nat.even_iff, doubledEnergy_mod_two]

theorem mem_lt_of_doubledEnergy_eq {I : Finset ℕ} {e i : ℕ}
    (hI : doubledEnergy I = 2 * e) (hi : i ∈ I) : i < e := by
  have h := Finset.single_le_sum (f := fun j : ℕ => 2 * j + 1)
    (fun j _ => Nat.zero_le _) hi
  change 2 * i + 1 ≤ doubledEnergy I at h
  omega

namespace Fock

variable (R : Type*) [CommRing R]

noncomputable def basis : Module.Basis (Finset ℕ) R (Fock R) :=
  (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).ExteriorAlgebra

noncomputable def generator (i : ℕ) : Fock R :=
  ExteriorAlgebra.ι R (Finsupp.single i 1)

noncomputable def create (i : ℕ) : Fock R →ₗ[R] Fock R :=
  LinearMap.mulLeft R (generator R i)

noncomputable def contract (i : ℕ) : Fock R →ₗ[R] Fock R :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (OneParticle R)))
    (Finsupp.lapply i)

@[simp] theorem create_apply (i : ℕ) (x : Fock R) :
    create R i x = generator R i * x := rfl

@[simp] theorem contract_one (i : ℕ) : contract R i 1 = 0 :=
  CliffordAlgebra.contractLeft_one _ _

@[simp] theorem generator_sq (i : ℕ) :
    generator R i * generator R i = 0 :=
  ExteriorAlgebra.ι_sq_zero _

theorem generator_anticommute (i j : ℕ) :
    generator R i * generator R j + generator R j * generator R i = 0 :=
  ExteriorAlgebra.ι_add_mul_swap _ _

@[simp] theorem create_create_self (i : ℕ) (x : Fock R) :
    create R i (create R i x) = 0 := by
  simp only [create_apply, ← mul_assoc, generator_sq, zero_mul]

@[simp] theorem contract_contract_self (i : ℕ) (x : Fock R) :
    contract R i (contract R i x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft _ _

theorem create_anticommute (i j : ℕ) (x : Fock R) :
    create R i (create R j x) + create R j (create R i x) = 0 := by
  simp only [create_apply, ← mul_assoc, ← add_mul, generator_anticommute, zero_mul]

theorem contract_anticommute (i j : ℕ) (x : Fock R) :
    contract R i (contract R j x) + contract R j (contract R i x) = 0 := by
  have h := CliffordAlgebra.contractLeft_comm
    (Q := (0 : QuadraticForm R (OneParticle R)))
    (Finsupp.lapply i) (Finsupp.lapply j) x
  exact eq_neg_iff_add_eq_zero.mp h

theorem contract_create (i j : ℕ) (x : Fock R) :
    contract R i (create R j x) =
      (if i = j then x else 0) - create R j (contract R i x) := by
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (OneParticle R)))
    (Finsupp.lapply i) (ExteriorAlgebra.ι R (Finsupp.single j 1) * x) = _
  rw [CliffordAlgebra.contractLeft_ι_mul]
  by_cases hij : i = j
  · subst j
    simp [Finsupp.lapply, create, generator, contract]
  · simp [Finsupp.lapply, hij, create, generator, contract]

theorem contract_create_add_create_contract (i j : ℕ) (x : Fock R) :
    contract R i (create R j x) + create R j (contract R i x) =
      if i = j then x else 0 := by
  rw [contract_create, sub_add_cancel]

@[simp] theorem contract_generator (i j : ℕ) :
    contract R i (generator R j) = if i = j then 1 else 0 := by
  simpa only [create_apply, mul_one, contract_one, mul_zero, sub_zero] using
    contract_create R i j (1 : Fock R)

end Fock

end Lemmata.FockCircuits
