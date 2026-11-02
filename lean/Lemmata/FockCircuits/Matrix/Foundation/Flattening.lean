module

/- Adapted namespace, imports, and selected scope from the pinned OpenAI/selanavot sources.
See Matrix/NOTICE.md and Matrix/Apache-2.0.txt. -/

public import Lemmata.FockCircuits.Matrix.Foundation.Tensor
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

set_option autoImplicit false

@[expose] section

namespace Lemmata.FockCircuits.Matrix

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

open scoped BigOperators

namespace Foundation
namespace Tensor

variable {K X Y Z : Type*} [Field K]

theorem RankAtMost.card_le_of_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Tensor K X Y Z} {r : ℕ} (hT : RankAtMost T r)
    (x : ι → X) (y : ι → Y) (z : ι → Z)
    (hidentity : ∀ i j, T (x i) (y i) (z j) = if i = j then 1 else 0) :
    Fintype.card ι ≤ r := by
  rcases hT with ⟨a, b, c, heq⟩
  let L : Matrix ι (Fin r) K := fun i q => a q (x i) * b q (y i)
  let R : Matrix (Fin r) ι K := fun q j => c q (z j)
  have hmul : L * R = (1 : Matrix ι ι K) := by
    funext i j
    change (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = if i = j then 1 else 0
    calc
      (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = T (x i) (y i) (z j) :=
        (congrFun (congrFun (congrFun heq (x i)) (y i)) (z j)).symm
      _ = _ := hidentity i j
  have hle : (1 : Matrix ι ι K).rank ≤ r := by
    rw [← hmul]
    exact (Matrix.rank_mul_le_left L R).trans (by
      simpa only [Fintype.card_fin] using Matrix.rank_le_card_width L)
  simpa only [Matrix.rank_one] using hle

end Tensor
end Foundation

end

end Lemmata.FockCircuits.Matrix
