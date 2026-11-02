module

/- Adapted namespace, imports, and selected scope from the pinned OpenAI/selanavot sources.
See Matrix/NOTICE.md and Matrix/Apache-2.0.txt. -/

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
Namespace, imports, and selected scope adapted for FockCircuits; see Matrix/NOTICE.md.
Apache-2.0 license retained in Matrix/Apache-2.0.txt.
-/

public import Lemmata.FockCircuits.Matrix.Foundation.Flattening

public section

set_option autoImplicit false

@[expose] section

namespace Lemmata.FockCircuits.Matrix

/-!
# Finite exact tensor rank

The rank is the least size of an exact decomposition into rank-one tensors.
-/

noncomputable section

open Foundation
open scoped BigOperators

namespace Spectral

variable {K : Type*} [Field K]

/-- Every finite coefficient tensor has a finite exact rank decomposition. -/
theorem exists_rankAtMost {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : ∃ r : ℕ, Tensor.RankAtMost T r := by
  classical
  let a : X × Y × Z → X → K := fun p x => if x = p.1 then T p.1 p.2.1 p.2.2 else 0
  let b : X × Y × Z → Y → K := fun p y => if y = p.2.1 then 1 else 0
  let c : X × Y × Z → Z → K := fun p z => if z = p.2.2 then 1 else 0
  refine ⟨Fintype.card (X × Y × Z), ?_⟩
  have heq : T = fun x y z => ∑ p, Tensor.rankOne (a p) (b p) (c p) x y z := by
    funext x y z
    simp [a, b, c, Tensor.rankOne, Fintype.sum_prod_type, mul_ite]
  rw [heq]
  exact Tensor.rankAtMost_sum_rankOne a b c

/-- Exact rank of a finite coefficient tensor over the scalar field. -/
def exactRank {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : ℕ := by
  classical
  exact Nat.find (exists_rankAtMost T)

/-- The least exact rank comes with an actual rank decomposition. -/
theorem exactRank_spec {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : Tensor.RankAtMost T (exactRank T) := by
  classical
  exact Nat.find_spec (exists_rankAtMost T)

/-- Every exact decomposition bounds the least rank. -/
theorem exactRank_le {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {T : Tensor K X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) : exactRank T ≤ r := by
  classical
  exact Nat.find_min' (exists_rankAtMost T) h

/-- Exact rank cannot increase under a linear restriction. -/
theorem exactRank_restrict_le {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor K X Y Z) (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) : exactRank (Tensor.restrict A B C T) ≤ exactRank T :=
  exactRank_le ((exactRank_spec T).restrict A B C)

/-- Independent bijections of the three coordinate sets preserve exact rank. -/
theorem exactRank_reindex {X Y Z X' Y' Z' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor K X Y Z) (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    exactRank (Tensor.pullback ex ey ez T) = exactRank T := by
  apply le_antisymm (exactRank_le ((exactRank_spec T).pullback ex ey ez))
  have h := exactRank_le
    ((exactRank_spec (Tensor.pullback ex ey ez T)).pullback ex.symm ey.symm ez.symm)
  have heq : Tensor.pullback ex.symm ey.symm ez.symm (Tensor.pullback ex ey ez T) = T := by
    funext x y z
    simp [Tensor.pullback]
  simpa only [heq] using h

/-- Tensor product decompositions give the usual submultiplicative rank bound. -/
theorem exactRank_product_le {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    exactRank (Tensor.product T S) ≤ exactRank T * exactRank S :=
  exactRank_le ((exactRank_spec T).product (exactRank_spec S))

end Spectral

end

end Lemmata.FockCircuits.Matrix
