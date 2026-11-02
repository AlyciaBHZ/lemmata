module

public import Lemmata.FockCircuits.Matrix.BilinearConstruction
public import Lemmata.FockCircuits.Matrix.RankAreas
public import Mathlib.Data.Nat.Log

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix

noncomputable section

open BilinearScheme

/-- Padding a certified power gives arbitrary integer sizes at the same arithmetic cost. -/
theorem integer_shape_algorithms {F : Type*} [Field F] {A B C : Type}
    [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty A] [Nonempty B] [Nonempty C] (s : BilinearScheme F A B C)
    {q a b c : ℕ} (hq : 1 < q)
    (hA : Fintype.card A = q ^ a) (hB : Fintype.card B = q ^ b) (hC : Fintype.card C = q ^ c)
    (N : ℕ) :
    ∃ p : Lemmata.FockCircuits.OrderedMatrixAlgorithm F (Fin (N ^ a)) (Fin (N ^ b)) (Fin (N ^ c)),
      Nonempty (Construction p) ∧
        p.size ≤ (6 * (Nat.log q N + 1) * s.rank + 1) * s.rank ^ (Nat.log q N + 1) := by
  let k := Nat.log q N + 1
  have hN : N ≤ q ^ k := (Nat.lt_pow_succ_log_self hq N).le
  have hsize (D : Type) [Fintype D] (d : ℕ) (hD : Fintype.card D = q ^ d) :
      Fintype.card (Fin (N ^ d)) ≤ Fintype.card (PowerIndex D k) := by
    rw [Fintype.card_fin, card_powerIndex, hD]
    simpa only [← pow_mul, Nat.mul_comm] using Nat.pow_le_pow_left hN d
  obtain ⟨eA⟩ := Function.Embedding.nonempty_of_card_le (hsize A a hA)
  obtain ⟨eB⟩ := Function.Embedding.nonempty_of_card_le (hsize B b hB)
  obtain ⟨eC⟩ := Function.Embedding.nonempty_of_card_le (hsize C c hC)
  let p := Lemmata.FockCircuits.Matrix.OrderedMatrixAlgorithm.pad (s.recursive k) eA eB eC
  refine ⟨p, ⟨Construction.padding eA eB eC (recursiveConstruction s k)⟩, ?_⟩
  change p.size ≤ (6 * k * s.rank + 1) * s.rank ^ k
  rw [Lemmata.FockCircuits.Matrix.OrderedMatrixAlgorithm.size_pad]
  exact s.recursive_size_bound k

end

end Lemmata.FockCircuits.Matrix
