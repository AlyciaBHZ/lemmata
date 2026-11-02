module

public import Lemmata.FockCircuits.Matrix.BilinearBlock

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.BilinearScheme

open scoped BigOperators

noncomputable section

def PowerIndex (A : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => A × PowerIndex A n

instance powerIndexFintype {A : Type} [Fintype A] : ∀ n, Fintype (PowerIndex A n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => letI := powerIndexFintype (A := A) n
      inferInstanceAs (Fintype (A × PowerIndex A n))

theorem card_powerIndex {A : Type} [Fintype A] (n : ℕ) :
    Fintype.card (PowerIndex A n) = Fintype.card A ^ n := by
  induction n with
  | zero =>
      calc
        Fintype.card (PowerIndex A 0) = Fintype.card Unit :=
          Fintype.card_congr (show PowerIndex A 0 ≃ Unit from Equiv.refl _)
        _ = Fintype.card A ^ 0 := by simp
  | succ n ih =>
      calc
        Fintype.card (PowerIndex A (n + 1)) = Fintype.card (A × PowerIndex A n) :=
          Fintype.card_congr (show PowerIndex A (n + 1) ≃ A × PowerIndex A n from Equiv.refl _)
        _ = Fintype.card A * Fintype.card (PowerIndex A n) := Fintype.card_prod _ _
        _ = Fintype.card A ^ (n + 1) := by rw [ih, pow_succ']

variable {K : Type*} {A B C : Type} [CommSemiring K]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]
variable [Fintype A] [Fintype B] [Fintype C]

def unitAlgorithm : OrderedMatrixAlgorithm K Unit Unit Unit where
  circuit := (CircuitBuilders.mul
    (CircuitBuilders.input (Sum.inl ((), ())))
    (CircuitBuilders.input (Sum.inr ((), ())))).reindexOutputs (fun _ => ())
  correct := by
    intro l n
    cases l
    cases n
    change _ = ∑ _m : Unit, _
    simp only [CircuitFamily.polynomial, CircuitFamily.eval_reindexOutputs,
      CircuitBuilders.eval_mul, CircuitBuilders.eval_input, Fintype.sum_unique]

@[simp] theorem size_unitAlgorithm : (unitAlgorithm (K := K)).size = 1 := by
  simp [unitAlgorithm, OrderedMatrixAlgorithm.size]

/-- Every recursive stage is an actual DAG built by the ordered bilinear block step. -/
def recursive (s : BilinearScheme K A B C) : (n : ℕ) →
    OrderedMatrixAlgorithm K (PowerIndex A n) (PowerIndex B n) (PowerIndex C n)
  | 0 => unitAlgorithm
  | n + 1 => s.blockStep (recursive s n)

def recursiveCost (r a b c : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => r * recursiveCost r a b c n +
      2 * r * (a * b * (a * b) ^ n + b * c * (b * c) ^ n + a * c * (a * c) ^ n)

theorem size_recursive (s : BilinearScheme K A B C) (n : ℕ) :
    (s.recursive n).size =
      recursiveCost s.rank (Fintype.card A) (Fintype.card B) (Fintype.card C) n := by
  induction n with
  | zero => exact size_unitAlgorithm
  | succ n ih =>
      calc
        (s.recursive (n + 1)).size = s.rank * (s.recursive n).size + 2 * s.rank *
            (Fintype.card A * Fintype.card B * Fintype.card (PowerIndex A n) *
              Fintype.card (PowerIndex B n) +
            Fintype.card B * Fintype.card C * Fintype.card (PowerIndex B n) *
              Fintype.card (PowerIndex C n) +
            Fintype.card A * Fintype.card C * Fintype.card (PowerIndex A n) *
              Fintype.card (PowerIndex C n)) := size_blockStep s (s.recursive n)
        _ = _ := by
          rw [ih]
          simp only [recursiveCost, card_powerIndex, mul_pow]
          ring

theorem recursiveCost_le {r a b c : ℕ}
    (hab : a * b ≤ r) (hbc : b * c ≤ r) (hac : a * c ≤ r) (n : ℕ) :
    recursiveCost r a b c n ≤ (6 * n * r + 1) * r ^ n := by
  induction n with
  | zero => simp [recursiveCost]
  | succ n ih =>
      have hpow (d : ℕ) (hd : d ≤ r) : d * d ^ n ≤ r ^ (n + 1) := by
        rw [pow_succ']
        exact Nat.mul_le_mul hd (Nat.pow_le_pow_left hd n)
      calc
        recursiveCost r a b c (n + 1) ≤
            r * ((6 * n * r + 1) * r ^ n) +
              2 * r * (r ^ (n + 1) + r ^ (n + 1) + r ^ (n + 1)) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ ih)
            (Nat.mul_le_mul_left _ (Nat.add_le_add
              (Nat.add_le_add (hpow (a * b) hab) (hpow (b * c) hbc)) (hpow (a * c) hac)))
        _ = (6 * (n + 1) * r + 1) * r ^ (n + 1) := by
          rw [pow_succ']
          ring

theorem size_recursive_le (s : BilinearScheme K A B C)
    (hab : Fintype.card A * Fintype.card B ≤ s.rank)
    (hbc : Fintype.card B * Fintype.card C ≤ s.rank)
    (hac : Fintype.card A * Fintype.card C ≤ s.rank) (n : ℕ) :
    (s.recursive n).size ≤ (6 * n * s.rank + 1) * s.rank ^ n := by
  rw [size_recursive]
  exact recursiveCost_le hab hbc hac n

end

end Lemmata.FockCircuits.Matrix.BilinearScheme
