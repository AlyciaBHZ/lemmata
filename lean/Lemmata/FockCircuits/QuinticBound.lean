module

public import Lemmata.FockCircuits.PositionalBound

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.QuinticExistence

theorem all_fields_identity_bound (R : Type*) [Field R] (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (identityQuintic R n) s ∧
        (s : ℝ) ≤ K * (n : ℝ) ^ (Exponent.gamma + eps) := by
  apply identity_circuit_bound R 512 _ eps heps
  intro n H E W B _ hWH hBW
  obtain ⟨bank⟩ := ModeBanks.exists_modeBank R n H E W B hWH hBW
  exact ModeAdjoints.exists_quinticBank R bank hWH hBW

theorem all_fields_identity_five_thirds (R : Type*) [Field R] :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (identityQuintic R n) s ∧ (s : ℝ) ≤ K * (n : ℝ) ^ (5 / 3 : ℝ) := by
  simpa only [show Exponent.gamma + (5 / 3 - Exponent.gamma) = (5 / 3 : ℝ) by ring] using
    all_fields_identity_bound R (5 / 3 - Exponent.gamma) (sub_pos.mpr Exponent.gamma_lt_five_thirds)

end Lemmata.FockCircuits.QuinticExistence

namespace Lemmata.FockCircuits.Positional

theorem quartic_five_thirds (R : Type*) [Field R] :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (quartic R n) s ∧ (s : ℝ) ≤ K * (n : ℝ) ^ (5 / 3 : ℝ) := by
  simpa only [show Exponent.gamma + (5 / 3 - Exponent.gamma) = (5 / 3 : ℝ) by ring] using
    quartic_bound R (5 / 3 - Exponent.gamma) (sub_pos.mpr Exponent.gamma_lt_five_thirds)

theorem quintic_five_thirds (R : Type*) [Field R] :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (quintic R n) s ∧ (s : ℝ) ≤ K * (n : ℝ) ^ (5 / 3 : ℝ) := by
  simpa only [show Exponent.gamma + (5 / 3 - Exponent.gamma) = (5 / 3 : ℝ) by ring] using
    quintic_bound R (5 / 3 - Exponent.gamma) (sub_pos.mpr Exponent.gamma_lt_five_thirds)

end Lemmata.FockCircuits.Positional
