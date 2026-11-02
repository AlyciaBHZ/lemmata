module

public import Lemmata.FockCircuits.Matrix.CharacterPower
public import Lemmata.FockCircuits.Matrix.Foundation.FieldDescent
public import Lemmata.FockCircuits.Matrix.BilinearCircuit

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix

open Foundation

noncomputable section

variable {F : Type*} [Field F]

/-- Spectral extraction and coefficient descent use one fixed finite algebra before powers vary. -/
theorem finite_blocks_over_field {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor F X Y Z) {B ρ : ℝ} (hB : 0 ≤ B)
    (hχ : ∀ χ : Spectral.Character (AlgebraicClosure F),
      χ.value (fun x y z => algebraMap F (AlgebraicClosure F) (T x y z)) ≤ B)
    (hρ : B < ρ) :
    ∃ N r d : ℕ, 0 < N ∧ 0 < d ∧ (r : ℝ) < ρ ^ N ∧
      ∀ n : ℕ, Tensor.RankAtMost (Tensor.power (Tensor.power T N) n) (r ^ n * d * d) := by
  obtain ⟨N, r, hN, hRank, hr⟩ := finite_power_rank_of_characters
    (fun x y z => algebraMap F (AlgebraicClosure F) (T x y z)) hB hχ hρ
  have hRank' : Tensor.RankAtMost
      (fun x y z => algebraMap F (AlgebraicClosure F) (Tensor.power T N x y z)) r := by
    have heq : (fun x y z => algebraMap F (AlgebraicClosure F) (Tensor.power T N x y z)) =
        Tensor.power (fun x y z => algebraMap F (AlgebraicClosure F) (T x y z)) N := by
      funext x y z
      simp only [Tensor.power, map_prod]
    rw [heq]
    exact hRank
  obtain ⟨d, hd, hblocks⟩ := hRank'.descend_algebraicClosure_powers
  exact ⟨N, r, d, hN, hd, hr, hblocks⟩

theorem matrix_power_rank {A B C : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq C]
    {n r : ℕ} (h : Tensor.RankAtMost
      (Tensor.power (Tensor.matrixCoefficients (K := F) A B C) n) r) :
    Tensor.RankAtMost
      (Tensor.matrixCoefficients (K := F) (Fin n → A) (Fin n → B) (Fin n → C)) r := by
  have hh := h.pullback
    (fun x : (Fin n → A) × (Fin n → B) => fun i => (x.1 i, x.2 i))
    (fun y : (Fin n → B) × (Fin n → C) => fun i => (y.1 i, y.2 i))
    (fun z : (Fin n → C) × (Fin n → A) => fun i => (z.1 i, z.2 i))
  have heq : Tensor.pullback
      (fun x : (Fin n → A) × (Fin n → B) => fun i => (x.1 i, x.2 i))
      (fun y : (Fin n → B) × (Fin n → C) => fun i => (y.1 i, y.2 i))
      (fun z : (Fin n → C) × (Fin n → A) => fun i => (z.1 i, z.2 i))
      (Tensor.power (Tensor.matrixCoefficients (K := F) A B C) n) =
        Tensor.matrixCoefficients (Fin n → A) (Fin n → B) (Fin n → C) := by
    funext x y z
    exact Tensor.matrixCoefficients_power n x y z
  rwa [heq] at hh

end

end Lemmata.FockCircuits.Matrix
