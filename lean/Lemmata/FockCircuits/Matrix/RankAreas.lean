module

public import Lemmata.FockCircuits.Matrix.BilinearPower
public import Lemmata.FockCircuits.Matrix.Foundation.Flattening

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix

open Foundation

noncomputable section

variable {K A B C : Type*} [Field K]
variable [Fintype A] [Fintype B] [Fintype C]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem matrix_output_area_le_rank [Nonempty B] {r : ℕ}
    (h : Tensor.RankAtMost (Tensor.matrixCoefficients (K := K) A B C) r) :
    Fintype.card A * Fintype.card C ≤ r := by
  classical
  let middle : B := Classical.choice inferInstance
  have hi := h.card_le_of_identity
    (fun i : A × C => (i.1, middle)) (fun i : A × C => (middle, i.2))
    (fun i : A × C => (i.2, i.1)) (by
      intro i j
      have hij : (i.2 = j.2 ∧ j.1 = i.1) ↔ i = j := by
        constructor
        · rintro ⟨hc, ha⟩
          exact Prod.ext ha.symm hc
        · rintro rfl
          exact ⟨rfl, rfl⟩
      simp [Tensor.matrixCoefficients, hij])
  simpa only [Fintype.card_prod] using hi

theorem matrix_areas_le_rank [Nonempty A] [Nonempty B] [Nonempty C] {r : ℕ}
    (h : Tensor.RankAtMost (Tensor.matrixCoefficients (K := K) A B C) r) :
    Fintype.card A * Fintype.card B ≤ r ∧ Fintype.card B * Fintype.card C ≤ r ∧
      Fintype.card A * Fintype.card C ≤ r := by
  have hab := matrix_output_area_le_rank (Tensor.matrixCoefficients_cyclic_rank h)
  have hbc := matrix_output_area_le_rank
    (Tensor.matrixCoefficients_cyclic_rank (Tensor.matrixCoefficients_cyclic_rank h))
  exact ⟨by simpa only [Nat.mul_comm] using hab,
    by simpa only [Nat.mul_comm] using hbc, matrix_output_area_le_rank h⟩

namespace BilinearScheme

theorem areas_le_rank [Nonempty A] [Nonempty B] [Nonempty C]
    (s : BilinearScheme K A B C) :
    Fintype.card A * Fintype.card B ≤ s.rank ∧
      Fintype.card B * Fintype.card C ≤ s.rank ∧
      Fintype.card A * Fintype.card C ≤ s.rank :=
  matrix_areas_le_rank ⟨s.left, s.right, s.output, s.coefficient_identity⟩

theorem recursive_size_bound {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]
    (s : BilinearScheme K A B C) (n : ℕ) :
    (s.recursive n).size ≤ (6 * n * s.rank + 1) * s.rank ^ n :=
  s.size_recursive_le s.areas_le_rank.1 s.areas_le_rank.2.1 s.areas_le_rank.2.2 n

end BilinearScheme

end

end Lemmata.FockCircuits.Matrix
