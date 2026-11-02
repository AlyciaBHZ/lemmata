module

public import Lemmata.FockCircuits.Matrix.ShapeBlocks
public import Lemmata.FockCircuits.Matrix.RankAmplification

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix

open Foundation

noncomputable section

/-- Every positive integer shape admits an exact base-field bilinear scheme with arbitrary slack. -/
theorem exists_shape_scheme (F : Type*) [Field F] {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N n : ℕ, 0 < N ∧ 0 < n ∧
      ∃ s : BilinearScheme F (Fin n → Fin N → Fin (2 ^ a))
          (Fin n → Fin N → Fin (2 ^ b)) (Fin n → Fin N → Fin (2 ^ c)),
        (s.rank : ℝ) < (2 : ℝ) ^ ((shapeRate a b c + δ) * (N * n : ℕ)) := by
  obtain ⟨N, r, d, hN, hd, hr, hblocks⟩ := shape_blocks_over_field F ha hb hc hδ
  obtain ⟨n, k, hn, hk, hlt⟩ := amplify_rank_seed _ hd hblocks hr
  have hmatrix := matrix_iterated_power_rank hk
  let s := BilinearScheme.ofRankAtMost hmatrix
  refine ⟨N, n, hN, hn, s, ?_⟩
  change (k : ℝ) < (2 : ℝ) ^ ((shapeRate a b c + δ) * (N * n : ℕ))
  rw [← pow_mul] at hlt
  rwa [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)] at hlt

end

end Lemmata.FockCircuits.Matrix
