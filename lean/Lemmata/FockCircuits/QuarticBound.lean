module

public import Lemmata.FockCircuits.ModeBanks

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits

open CrossingPadding Exponent

theorem identity_quartic_bound (R : Type*) [Field R] (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (identityQuartic (R := R) n) s ∧
        (s : ℝ) ≤ K * (n : ℝ) ^ (gamma + eps) := by
  exact CrossingExistence.identity_circuit_bound R 256
    (fun n H E W B _ hWH hBW => ModeBanks.exists_modeBank R n H E W B hWH hBW) eps heps

theorem identity_quartic_five_thirds (R : Type*) [Field R] :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (identityQuartic (R := R) n) s ∧
        (s : ℝ) ≤ K * (n : ℝ) ^ (5 / 3 : ℝ) := by
  have h := identity_quartic_bound R (5 / 3 - gamma) (by linarith [gamma_lt_five_thirds])
  have he : gamma + (5 / 3 - gamma) = (5 / 3 : ℝ) := by ring
  simpa only [he] using h

end Lemmata.FockCircuits
