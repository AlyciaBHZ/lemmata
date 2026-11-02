module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Profile

open scoped BigOperators

theorem sum_finite_increments (u : ℕ → ℝ) (a n : ℕ) :
    (∑ i : Fin n, (u (a + i.val + 1) - u (a + i.val))) = u (a + n) - u a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    simp only [Nat.add_assoc]
    ring

/-- Decreasing consecutive increments give the adjacent secant inequality at arbitrary integer endpoints. -/
theorem discrete_secant_antitone {u : ℕ → ℝ}
    (hd : Antitone (fun n => u (n + 1) - u n)) {a b c : ℕ}
    (hab : a < b) (hbc : b < c) :
    (u c - u b) / ((c : ℝ) - b) ≤ (u b - u a) / ((b : ℝ) - a) := by
  have hpair (i : Fin (b - a)) (j : Fin (c - b)) :
      u (b + j.val + 1) - u (b + j.val) ≤ u (a + i.val + 1) - u (a + i.val) := by
    apply hd
    have hi := i.isLt
    omega
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (b - a)))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (c - b)))) => hpair i j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  rw [← Finset.mul_sum] at hs
  rw [sum_finite_increments, sum_finite_increments] at hs
  have hb : a + (b - a) = b := Nat.add_sub_of_le hab.le
  have hc : b + (c - b) = c := Nat.add_sub_of_le hbc.le
  rw [hb, hc, Nat.cast_sub hab.le, Nat.cast_sub hbc.le] at hs
  apply (div_le_div_iff₀ (sub_pos.mpr (by exact_mod_cast hbc) : 0 < (c : ℝ) - b)
    (sub_pos.mpr (by exact_mod_cast hab) : 0 < (b : ℝ) - a)).mpr
  nlinarith

end Lemmata.FockCircuits.Matrix.Profile
