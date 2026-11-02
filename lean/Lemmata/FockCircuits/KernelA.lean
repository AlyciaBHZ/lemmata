module

public import Lemmata.FockCircuits.KernelAlgorithm
public import Lemmata.FockCircuits.KernelOrientation

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lemmata.FockCircuits.KernelAlgorithm

open FiniteIdentity
open scoped BigOperators

variable (R : Type*) [CommRing R]

theorem particleEmbedding_finitePascal_left {L m : ℕ} (hm : m < L) :
    particleEmbedding R (fun i => 2 * i)
        (Fock.finitePascal R L (Finsupp.single m 1)) =
      positiveLeft R L (Finsupp.single m 1) := by
  simp only [Fock.finitePascal_single, ite_eq_left hm, map_sum, map_smul,
    particleEmbedding_single, positiveLeft, Finsupp.linearCombination_single,
    one_smul, TwoColour.leftVector, positiveCoefficient, Int.cast_natCast]
  symm
  exact Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (k.choose m : R) • Finsupp.single (2 * k) (1 : R)) L

theorem particleEmbedding_finitePascal_right {L m : ℕ} (hm : m < L) :
    particleEmbedding R (fun i => 2 * i + 1)
        (Fock.finitePascal R L (Finsupp.single m 1)) =
      positiveRight R L (Finsupp.single m 1) := by
  simp only [Fock.finitePascal_single, ite_eq_left hm, map_sum, map_smul,
    particleEmbedding_single, positiveRight, Finsupp.linearCombination_single,
    one_smul, TwoColour.rightVector, positiveCoefficient, Int.cast_natCast]
  symm
  exact Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (k.choose m : R) • Finsupp.single (2 * k + 1) (1 : R)) L

end Lemmata.FockCircuits.KernelAlgorithm
