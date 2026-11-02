module

public import Lemmata.FockCircuits.SymmetricBound

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lemmata.FockCircuits.Patterns

open Exponent

noncomputable section

theorem rectangularPermanent_bound (R : Type*) [Field R] (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ k : ℕ, k ≤ 5 → ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (rectangularPermanent R k n) s ∧
        (s : ℝ) ≤ K * (n : ℝ)^(gamma+eps) := by
  obtain ⟨C, hC, hcore⟩ := Symmetric.core_budget R eps heps
  let M : ℝ := Symmetric.patternCount
  let K := (M+1)*(C+28)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro k hk n hn
  obtain ⟨s, h4, h5, hs⟩ := hcore n hn
  let c := Fintype.card (Setoid (Fin k))
  have hc := positionalExactPattern_hasCircuit h4 h5 hk (⊥ : Setoid (Fin k))
  refine ⟨c*(s+15*n+13), ?_, ?_⟩
  · simpa only [← rectangularPermanent_eq_exact, Fintype.card_fin] using hc
  have hcard : (c : ℝ) ≤ M := by
    change (Fintype.card (Setoid (Fin k)) : ℝ) ≤ (Symmetric.patternCount : ℝ)
    exact_mod_cast Symmetric.pattern_card_le (⟨k, by omega⟩ : Fin 6)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrate : 1 ≤ gamma+eps := by
    unfold gamma
    nlinarith [Real.sqrt_nonneg (7 : ℝ)]
  have hnpow := Real.self_le_rpow_of_one_le hnR hrate
  have hpow := Real.one_le_rpow hnR (by linarith : 0 ≤ gamma+eps)
  have hx : (s : ℝ)+15*(n : ℝ)+13 ≤ (C+28)*(n : ℝ)^(gamma+eps) := by nlinarith
  push_cast
  calc
    (c : ℝ)*((s : ℝ)+15*(n : ℝ)+13) ≤ M*((s : ℝ)+15*(n : ℝ)+13) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ M*((C+28)*(n : ℝ)^(gamma+eps)) := mul_le_mul_of_nonneg_left hx hM
    _ = (M*(C+28))*(n : ℝ)^(gamma+eps) := by ring
    _ ≤ K*(n : ℝ)^(gamma+eps) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)

theorem rectangularPermanent_five_thirds (R : Type*) [Field R] :
    ∃ K : ℝ, 0 < K ∧ ∀ k : ℕ, k ≤ 5 → ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (rectangularPermanent R k n) s ∧
        (s : ℝ) ≤ K * (n : ℝ)^(5/3 : ℝ) := by
  have h := rectangularPermanent_bound R (5/3-gamma) (sub_pos.mpr gamma_lt_five_thirds)
  simpa only [show gamma+(5/3-gamma) = (5/3 : ℝ) by ring] using h

end

end Lemmata.FockCircuits.Patterns
