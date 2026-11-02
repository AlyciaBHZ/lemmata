module

public import Lemmata.FockCircuits.PatternInversion
public import Lemmata.FockCircuits.PositionalBound

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Classical

namespace Lemmata.FockCircuits.Symmetric

open Patterns Exponent

noncomputable section

def patternCount : ℕ := ∑ k : Fin 6, Fintype.card (Setoid (Fin k.val))

theorem pattern_card_le (k : Fin 6) : Fintype.card (Setoid (Fin k.val)) ≤ patternCount := by
  change Fintype.card (Setoid (Fin k.val)) ≤ ∑ j : Fin 6, Fintype.card (Setoid (Fin j.val))
  exact Finset.single_le_sum (f := fun j : Fin 6 => Fintype.card (Setoid (Fin j.val)))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

def polynomialBudget (s n : ℕ) : ℕ :=
  6 * (patternCount * (patternCount * (s + 15*n + 13) + 2) + 1)

theorem hasCircuit_of_core_bounds {R : Type*} {X : Type*} [CommRing R] [Fintype X] {s : ℕ}
    (h4 : HasCircuit (Patterns.quartic (R := R) (C := X) (P := Fin 4) 0 1 2 3) s)
    (h5 : HasCircuit (Patterns.quintic (R := R) (C := X) (P := Fin 5) 0 1 2 3 4) s)
    (p : FreeAlgebra R X) (hsym : IsSymmetric p) (hdegree : DegreeLE 5 p) :
    HasCircuit p (polynomialBudget s (Fintype.card X)) := by
  classical
  let x := s + 15*Fintype.card X + 13
  have hinner (k : Fin 6) :
      HasCircuit (∑ π : Setoid (Fin k.val), patternCoefficient p k.val π •
        exactPattern (R := R) (X := X) π)
        (patternCount * (patternCount*x + 2)) := by
    have hcoeff (π : Setoid (Fin k.val)) :
        HasCircuit (patternCoefficient p k.val π • exactPattern (R := R) (X := X) π)
          (patternCount*x + 1) := by
      have hk : k.val ≤ 5 := by have := k.isLt; omega
      have he := exactPattern_hasCircuit h4 h5 hk π
      have he' : HasCircuit (exactPattern (R := R) (X := X) π) (patternCount*x) :=
        he.mono (Nat.mul_le_mul_right x (pattern_card_le k))
      simpa only [Algebra.smul_def, zero_add] using (HasCircuit.scalar (patternCoefficient p k.val π)).mul he'
    have hi := finset_sum_hasCircuit Finset.univ
      (fun π : Setoid (Fin k.val) => patternCoefficient p k.val π • exactPattern (R := R) (X := X) π)
      (patternCount*x + 1) (fun π _ => hcoeff π)
    have hi' : HasCircuit (∑ π : Setoid (Fin k.val), patternCoefficient p k.val π •
        exactPattern (R := R) (X := X) π)
        (Fintype.card (Setoid (Fin k.val)) * (patternCount*x + 2)) := by
      simpa only [Finset.card_univ, Nat.add_assoc] using hi
    exact hi'.mono (Nat.mul_le_mul_right _ (pattern_card_le k))
  rw [decomposition 5 p hsym hdegree]
  have hout := finset_sum_hasCircuit Finset.univ
    (fun k : Fin 6 => ∑ π : Setoid (Fin k.val), patternCoefficient p k.val π • exactPattern (R := R) (X := X) π)
    (patternCount * (patternCount*x + 2)) (fun k _ => hinner k)
  simpa only [Finset.card_univ, Fintype.card_fin, polynomialBudget] using hout

theorem core_budget (R : Type*) [Field R] (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∃ s : ℕ,
      HasCircuit (Patterns.quartic (R := R) (C := Fin n) (P := Fin 4) 0 1 2 3) s ∧
      HasCircuit (Patterns.quintic (R := R) (C := Fin n) (P := Fin 5) 0 1 2 3 4) s ∧
      (s : ℝ) ≤ C * (n : ℝ) ^ (gamma + eps) := by
  obtain ⟨K4, hK4, h4⟩ := Positional.quartic_bound R eps heps
  obtain ⟨K5, hK5, h5⟩ := Positional.quintic_bound R eps heps
  refine ⟨K4+K5, add_pos hK4 hK5, ?_⟩
  intro n hn
  obtain ⟨s4, hp4, hs4⟩ := h4 n hn
  obtain ⟨s5, hp5, hs5⟩ := h5 n hn
  refine ⟨s4+s5, ?_, ?_, ?_⟩
  · simpa only [Patterns.quartic, Positional.quartic] using hp4.mono (by omega : s4 ≤ s4+s5)
  · simpa only [Patterns.quintic, Positional.quintic] using hp5.mono (by omega : s5 ≤ s4+s5)
  · push_cast
    nlinarith

theorem circuit_bound (R : Type*) [Field R] (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → ∀ p : FreeAlgebra R (Fin n),
      IsSymmetric p → DegreeLE 5 p → ∃ s : ℕ,
        HasCircuit p s ∧ (s : ℝ) ≤ K * (n : ℝ) ^ (gamma + eps) := by
  obtain ⟨C, hC, hcore⟩ := core_budget R eps heps
  let M : ℝ := patternCount
  let K := 6*M^2*(C+28) + 12*M + 7
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro n hn p hsym hdegree
  obtain ⟨s, h4, h5, hs⟩ := hcore n hn
  have hc := hasCircuit_of_core_bounds h4 h5 p hsym hdegree
  refine ⟨polynomialBudget s n, by simpa only [Fintype.card_fin] using hc, ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrate : 1 ≤ gamma+eps := by
    unfold gamma
    nlinarith [Real.sqrt_nonneg (7 : ℝ)]
  have hnpow := Real.self_le_rpow_of_one_le hnR hrate
  have hpow := Real.one_le_rpow hnR (by linarith : 0 ≤ gamma+eps)
  have hx : (s : ℝ) + 15*(n : ℝ) + 13 ≤ (C+28)*(n : ℝ)^(gamma+eps) := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hx (by positivity : 0 ≤ 6*M^2)
  have hconstant : 12*M+6 ≤ (12*M+6)*(n : ℝ)^(gamma+eps) :=
    le_mul_of_one_le_right (by positivity) hpow
  have hid : (polynomialBudget s n : ℝ) = 6*M^2*((s : ℝ)+15*(n : ℝ)+13)+12*M+6 := by
    dsimp only [polynomialBudget, M]
    push_cast
    ring
  rw [hid]
  calc
    _ ≤ 6*M^2*((C+28)*(n : ℝ)^(gamma+eps))+(12*M+6)*(n : ℝ)^(gamma+eps) :=
      by simpa only [add_assoc] using add_le_add hmul hconstant
    _ = (6*M^2*(C+28)+12*M+6)*(n : ℝ)^(gamma+eps) := by ring
    _ ≤ K*(n : ℝ)^(gamma+eps) :=
      mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) (by positivity)

theorem five_thirds_bound (R : Type*) [Field R] :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → ∀ p : FreeAlgebra R (Fin n),
      IsSymmetric p → DegreeLE 5 p → ∃ s : ℕ,
        HasCircuit p s ∧ (s : ℝ) ≤ K * (n : ℝ) ^ (5/3 : ℝ) := by
  have h := circuit_bound R (5/3-gamma) (sub_pos.mpr gamma_lt_five_thirds)
  simpa only [show gamma+(5/3-gamma) = (5/3 : ℝ) by ring] using h

end

end Lemmata.FockCircuits.Symmetric
