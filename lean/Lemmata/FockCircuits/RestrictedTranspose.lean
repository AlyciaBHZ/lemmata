module

public import Lemmata.FockCircuits.SourceBanks

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lemmata.FockCircuits.RestrictedTranspose

open scoped BigOperators

noncomputable section

variable {R D I O : Type*} [CommRing R]
variable [Fintype D] [Fintype I] [Fintype O] [DecidableEq D]

/-- Restrict source and output coordinates and apply the output diagonal before transposing. -/
def build {a : D → D → R} (t : ScalarTransposeAlgorithm R D D a)
    (source : I ↪ D) (output : O ↪ D) (mask : D → R) :
    ScalarTransposeAlgorithm R I O (fun o i => mask (output o) * a (output o) (source i)) := by
  let ti := ScalarAdjoints.injectionTranspose (R := R) source
  let td := ScalarAdjoints.diagonalTranspose mask
  let outputTranspose := SourceBanks.selectionTranspose (R := R) output
  let result := ScalarAdjoints.compose (ScalarAdjoints.compose (ScalarAdjoints.compose ti t) td) outputTranspose
  refine ⟨result.circuit, ?_⟩
  intro i
  rw [result.correct]
  simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro o ho
  congr 1
  ring

theorem size_build {a : D → D → R} (t : ScalarTransposeAlgorithm R D D a)
    (source : I ↪ D) (output : O ↪ D) (mask : D → R) :
    (build t source output mask).size = t.size + Fintype.card D := by
  simp only [build, ScalarTransposeAlgorithm.size, ScalarAdjoints.compose,
    CircuitFamily.size_substitute]
  change (SourceBanks.selectionTranspose (R := R) output).size +
    ((ScalarAdjoints.diagonalTranspose mask).size +
      (t.size + (ScalarAdjoints.injectionTranspose (R := R) source).size)) = _
  rw [SourceBanks.size_selectionTranspose, ScalarAdjoints.size_diagonalTranspose,
    ScalarAdjoints.size_injectionTranspose]
  simp only [ScalarTransposeAlgorithm.size]
  omega

end

end Lemmata.FockCircuits.RestrictedTranspose
