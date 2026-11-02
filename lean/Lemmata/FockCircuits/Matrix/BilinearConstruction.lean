module

public import Lemmata.FockCircuits.Matrix.PrefixCircuit
public import Lemmata.FockCircuits.Matrix.AlgorithmPadding

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.BilinearScheme

noncomputable section

variable {K : Type*} [CommSemiring K]

/-- A syntactic witness records the scalar-linear stages and ordered recursive product stages. -/
inductive Construction : {L M N : Type} → [Fintype L] → [Fintype M] → [Fintype N] →
    OrderedMatrixAlgorithm K L M N → Type _
  | unit : Construction (unitAlgorithm (K := K))
  | block {A B C L M N : Type}
      [Fintype A] [Fintype B] [Fintype C] [Fintype L] [Fintype M] [Fintype N]
      [DecidableEq A] [DecidableEq B] [DecidableEq C]
      (s : BilinearScheme K A B C) {p : OrderedMatrixAlgorithm K L M N}
      (previous : Construction p) : Construction (s.blockStep p)
  | padding {L M N L' M' N' : Type}
      [Fintype L] [Fintype M] [Fintype N] [Fintype L'] [Fintype M'] [Fintype N']
      (eL : L' ↪ L) (eM : M' ↪ M) (eN : N' ↪ N)
      {p : Lemmata.FockCircuits.OrderedMatrixAlgorithm K L M N}
      (previous : Construction p) :
      Construction (Lemmata.FockCircuits.Matrix.OrderedMatrixAlgorithm.pad p eL eM eN)

def recursiveConstruction {A B C : Type} [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Fintype A] [Fintype B] [Fintype C] (s : BilinearScheme K A B C) :
    (n : ℕ) → Construction (s.recursive n)
  | 0 => .unit
  | n + 1 => .block s (recursiveConstruction s n)

theorem Construction.prefixSafe {L M N : Type} [Fintype L] [Fintype M] [Fintype N]
    {p : OrderedMatrixAlgorithm K L M N} (construction : Construction p) : PrefixSafe p := by
  induction construction with
  | unit => exact unitAlgorithm_prefixSafe
  | block s previous ih => exact blockStep_prefixSafe s _ ih
  | padding eL eM eN previous ih =>
      exact Lemmata.FockCircuits.Matrix.OrderedMatrixAlgorithm.pad_prefixSafe _ ih eL eM eN

end

end Lemmata.FockCircuits.Matrix.BilinearScheme
