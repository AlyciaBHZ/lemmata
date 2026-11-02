module

public import Lemmata.FockCircuits.FiniteIdentity

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.FiniteIdentity

variable (R : Type*) [CommRing R]

noncomputable def positiveLeft (L : ℕ) : OneParticle R →ₗ[R] OneParticle R :=
  Finsupp.linearCombination R fun m : ℕ =>
    TwoColour.leftVector R L (fun k => (positiveCoefficient m k : R))

noncomputable def positiveRight (L : ℕ) : OneParticle R →ₗ[R] OneParticle R :=
  Finsupp.linearCombination R fun m : ℕ =>
    TwoColour.rightVector R L (fun k => (positiveCoefficient m k : R))

noncomputable def negativeRight (L : ℕ) : OneParticle R →ₗ[R] OneParticle R :=
  Finsupp.linearCombination R fun m : ℕ =>
    TwoColour.rightVector R L (fun k => (negativeCoefficient m k : R))

theorem rightVector_sum {D : Type*} (S : Finset D) (c : D → R)
    (L : ℕ) (v : D → Fin L → R) :
    (∑ j ∈ S, c j • TwoColour.rightVector R L (v j)) =
      TwoColour.rightVector R L (fun k => ∑ j ∈ S, c j * v j k) := by
  simp only [TwoColour.rightVector, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_smul]

theorem positiveRight_comp_pascal (L : ℕ) :
    (positiveRight R L).comp (Fock.pascal R).toLinearMap = negativeRight R L := by
  apply (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).ext
  intro m
  simp only [Finsupp.coe_basisSingleOne, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Fock.pascal_single_sum, map_sum, map_smul]
  simp only [positiveRight, negativeRight, Finsupp.linearCombination_single,
    one_smul]
  rw [rightVector_sum]
  congr 1
  funext k
  have h := congrArg (fun z : ℤ => (z : R)) (pascal_convolution m k)
  simpa only [Int.cast_sum, Int.cast_mul] using h

theorem substitution_eq (L : ℕ) :
    substitution R L = positiveLeft R L +
      (positiveRight R L).comp (Fock.pascal R).toLinearMap := by
  rw [positiveRight_comp_pascal]
  apply (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).ext
  intro m
  simp [substitution, positiveLeft, negativeRight]

theorem kernel_oriented (L : ℕ) (v : State R L) :
    kernel R L v =
      ExteriorAlgebra.map
        ((positiveLeft R L).comp (Fock.pascal R).symm.toLinearMap + positiveRight R L)
        (Fock.pascalExterior R (realize R L v)) * TwoColour.kernel R L := by
  rw [kernel, substitution_eq, Fock.exterior_orientation]

end Lemmata.FockCircuits.FiniteIdentity
