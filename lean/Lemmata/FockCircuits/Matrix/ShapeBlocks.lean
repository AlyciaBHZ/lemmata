module

public import Lemmata.FockCircuits.Matrix.Profile.CharacterBound
public import Lemmata.FockCircuits.Matrix.ExactBlocks

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix

open Foundation Spectral

noncomputable section

def shapeRate (a b c : ℝ) : ℝ := (a * b + a * c + b * c) ^ 2 / (4 * a * b * c)

theorem shapeRate_cyclic (a b c : ℝ) : shapeRate c a b = shapeRate a b c := by
  unfold shapeRate
  congr 1 <;> ring

theorem value_matrix_power_shape {K : Type*} [Field K] (χ : Character K)
    {base : ℕ} (hbase : 0 < base) (a b c : ℕ) :
    χ.value (Tensor.matrixCoefficients (K := K)
      (Fin (base ^ a)) (Fin (base ^ b)) (Fin (base ^ c))) =
      (base : ℝ) ^ ((a : ℝ) * χ.pY + (b : ℝ) * χ.pZ + (c : ℝ) * χ.pX) := by
  have hpos : 0 < (base : ℝ) := Nat.cast_pos.mpr hbase
  rw [χ.value_matrixCoefficients (pow_pos hbase a) (pow_pos hbase b) (pow_pos hbase c)]
  simp only [Nat.cast_pow]
  rw [← Real.rpow_natCast_mul hpos.le b, ← Real.rpow_natCast_mul hpos.le a,
    ← Real.rpow_natCast_mul hpos.le c, ← Real.rpow_add hpos, ← Real.rpow_add hpos]
  congr 1
  ring

theorem matrix_power_shape_character_bound {K : Type*} [Field K] [Infinite K] [IsAlgClosed K]
    (χ : Character K) {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    χ.value (Tensor.matrixCoefficients (K := K)
      (Fin (2 ^ a)) (Fin (2 ^ b)) (Fin (2 ^ c))) ≤
      (2 : ℝ) ^ shapeRate a b c := by
  rw [value_matrix_power_shape χ (by norm_num)]
  have hw := Profile.weighted_character_bound χ (c : ℝ) (a : ℝ) (b : ℝ)
    (Nat.cast_pos.mpr hc) (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hb)
  change (c : ℝ) * χ.pX + (a : ℝ) * χ.pY + (b : ℝ) * χ.pZ ≤ shapeRate c a b at hw
  rw [shapeRate_cyclic] at hw
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  linarith

/-- Positive slack gives finite exact coefficient blocks over every scalar field. -/
theorem shape_blocks_over_field (F : Type*) [Field F] {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N r d : ℕ, 0 < N ∧ 0 < d ∧
      (r : ℝ) < ((2 : ℝ) ^ (shapeRate a b c + δ)) ^ N ∧
      ∀ n : ℕ, Tensor.RankAtMost
        (Tensor.power (Tensor.power (Tensor.matrixCoefficients (K := F)
          (Fin (2 ^ a)) (Fin (2 ^ b)) (Fin (2 ^ c))) N) n) (r ^ n * d * d) := by
  apply finite_blocks_over_field _
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (shapeRate a b c))
  · intro χ
    have heq : (fun x y z => algebraMap F (AlgebraicClosure F)
        (Tensor.matrixCoefficients (K := F) (Fin (2 ^ a)) (Fin (2 ^ b)) (Fin (2 ^ c)) x y z)) =
        Tensor.matrixCoefficients (K := AlgebraicClosure F)
          (Fin (2 ^ a)) (Fin (2 ^ b)) (Fin (2 ^ c)) := by
      funext x y z
      simp only [Tensor.matrixCoefficients, apply_ite, map_one, map_zero]
      split_ifs <;> rfl
    rw [heq]
    exact matrix_power_shape_character_bound χ ha hb hc
  · apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    linarith

end

end Lemmata.FockCircuits.Matrix
