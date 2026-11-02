module

public import Lemmata.FockCircuits.Matrix.ShapeSeed
public import Lemmata.FockCircuits.Matrix.IntegerShapes
public import Lemmata.FockCircuits.Cutoffs

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix

open BilinearScheme

noncomputable section

/-- The all-field shape bound produces finite ordered DAGs at every integer scale. -/
theorem shape_algorithms (F : Type*) [Field F] {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q r : ℕ, 1 < q ∧ (r : ℝ) < (q : ℝ) ^ (shapeRate a b c + δ) ∧
      ∀ N : ℕ,
        ∃ p : Lemmata.FockCircuits.OrderedMatrixAlgorithm F
            (Fin (N ^ a)) (Fin (N ^ b)) (Fin (N ^ c)),
          Nonempty (Construction p) ∧
            p.size ≤ (6 * (Nat.log q N + 1) * r + 1) * r ^ (Nat.log q N + 1) := by
  obtain ⟨N, n, hN, hn, s, hs⟩ := exists_shape_scheme F ha hb hc hδ
  let q := 2 ^ (N * n)
  have hq : 1 < q := Nat.one_lt_pow (Nat.mul_ne_zero hN.ne' hn.ne') (by decide)
  have hcard (d : ℕ) : Fintype.card (Fin n → Fin N → Fin (2 ^ d)) = q ^ d := by
    simp only [Fintype.card_fun, Fintype.card_fin, q, ← pow_mul]
    congr 1
    ring
  have hr : (s.rank : ℝ) < (q : ℝ) ^ (shapeRate a b c + δ) := by
    have heq : (q : ℝ) ^ (shapeRate a b c + δ) =
        (2 : ℝ) ^ ((shapeRate a b c + δ) * (N * n : ℕ)) := by
      simp only [q, Nat.cast_pow, Nat.cast_ofNat]
      rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rwa [heq]
  letI : Nonempty (Fin n → Fin N → Fin (2 ^ a)) :=
    ⟨fun _ _ => ⟨0, pow_pos (by decide) a⟩⟩
  letI : Nonempty (Fin n → Fin N → Fin (2 ^ b)) :=
    ⟨fun _ _ => ⟨0, pow_pos (by decide) b⟩⟩
  letI : Nonempty (Fin n → Fin N → Fin (2 ^ c)) :=
    ⟨fun _ _ => ⟨0, pow_pos (by decide) c⟩⟩
  refine ⟨q, s.rank, hq, hr, fun m => ?_⟩
  exact integer_shape_algorithms s hq (hcard a) (hcard b) (hcard c) m

theorem eventually_shape_algorithms (F : Type*) [Field F] {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∃ p : Lemmata.FockCircuits.OrderedMatrixAlgorithm F
          (Fin (N ^ a)) (Fin (N ^ b)) (Fin (N ^ c)),
        Nonempty (Construction p) ∧ (p.size : ℝ) ≤ (N : ℝ) ^ (shapeRate a b c + δ) := by
  obtain ⟨q, r, hq, hr, halg⟩ := shape_algorithms F ha hb hc hδ
  have hcost := eventually_recursion_cost_le_rpow q r (by omega) (shapeRate a b c + δ) hr
  filter_upwards [hcost] with N hN
  obtain ⟨p, hsyntax, hsize⟩ := halg N
  exact ⟨p, hsyntax, (Nat.cast_le.mpr hsize).trans hN⟩

end

end Lemmata.FockCircuits.Matrix
