module

public import Lemmata.FockCircuits.SymmetricBound
public import Lemmata.FockCircuits.PermanentBound

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.RecordBounds

theorem quartic_bound (F : Type*) [Field F] :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (Positional.quartic F n) s ∧
        (s : ℝ) ≤ C * (n : ℝ) ^ (5 / 3 : ℝ) := by
  have h := Positional.quartic_bound F (5 / 3 - Exponent.gamma)
    (sub_pos.mpr Exponent.gamma_lt_five_thirds)
  have he : Exponent.gamma + (5 / 3 - Exponent.gamma) = (5 / 3 : ℝ) := by ring
  simpa only [he] using h

theorem symmetric_five_bound (F : Type*) [Field F] :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ p : FreeAlgebra F (Fin n),
      Symmetric.IsSymmetric p → Symmetric.DegreeLE 5 p →
        ∃ s : ℕ, HasCircuit p s ∧ (s : ℝ) ≤ C * (n : ℝ) ^ (5 / 3 : ℝ) :=
  Symmetric.five_thirds_bound F

theorem permanent_five_bound (F : Type*) [Field F] :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, k ≤ 5 → ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (Patterns.rectangularPermanent F k n) s ∧
        (s : ℝ) ≤ C * (n : ℝ) ^ (5 / 3 : ℝ) :=
  Patterns.rectangularPermanent_five_thirds F

end Lemmata.FockCircuits.RecordBounds
