module

/- Adapted coefficient-character lifting from OpenAI/selanavot under Apache-2.0.
See Matrix/NOTICE.md for provenance and scope. -/

public import Lemmata.FockCircuits.Matrix.Character.Basic
public import Lemmata.FockCircuits.Matrix.Tensor.DirectSumClass
public import Lemmata.FockCircuits.Matrix.TensorPower

public section

set_option autoImplicit false

@[expose] section

namespace Lemmata.FockCircuits.Matrix

open Foundation
open Spectral TensorSemiring
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

/-- A monotone tensor-class character acts on exact coefficient arrays. -/
def characterOfHom (φ : TensorClass K →+* ℝ) (hφ : Monotone φ) : Spectral.Character K where
  value := fun T => φ (classOf T)
  nonneg := by
    intro X Y Z hX hY hZ T
    simpa only [φ.map_zero] using hφ (TensorSemiring.zero_le (classOf T))
  map_zero := by
    intro X Y Z hX hY hZ
    rw [classOf_zero]
    exact φ.map_zero
  map_one := by
    change φ 1 = 1
    exact φ.map_one
  map_directSum := by
    intro ι X Y Z hι dι hX hY hZ T
    rw [classOf_directSum, map_sum]
  map_product := by
    intro X Y Z U V W hX hY hZ hU hV hW T S
    rw [classOf_product, map_mul]
  monotone := by
    intro X Y Z X' Y' Z' hX hY hZ hX' hY' hZ' T A B C
    apply hφ
    exact (classOf_le_iff _ _).mpr ⟨A, B, C, rfl⟩

@[simp] theorem characterOfHom_value (φ : TensorClass K →+* ℝ) (hφ : Monotone φ)
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor K X Y Z) :
    (characterOfHom φ hφ).value T = φ (classOf T) := rfl

/-- The coefficient-level spectral consequence is proved for every scalar field. -/
theorem finite_power_rank_of_characters {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) {B ρ : ℝ} (hB : 0 ≤ B)
    (h : ∀ χ : Spectral.Character K, χ.value T ≤ B) (hρ : B < ρ) :
    ∃ n r : ℕ, 0 < n ∧ Tensor.RankAtMost (Tensor.power T n) r ∧ (r : ℝ) < ρ ^ n := by
  apply exists_coefficient_power_rank T hB (fun φ hφ => ?_) hρ
  exact h (characterOfHom φ hφ)

end

end Lemmata.FockCircuits.Matrix
