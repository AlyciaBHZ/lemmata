module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Profile

def PairRatio (p q a c : ℝ) : Prop :=
  ∀ R S : ℝ, 0 < R → 0 < S →
    p * S / (S + a * R) + q * R / (R + c * S) ≤ 1

theorem PairRatio.zero_left {q a c : ℝ} (hq : q ≤ 1) (hc : 0 ≤ c) :
    PairRatio 0 q a c := by
  intro R S hR hS
  simp only [zero_mul, zero_div, zero_add]
  apply (div_le_iff₀ (by positivity : 0 < R + c * S)).mpr
  have hm := mul_le_mul_of_nonneg_right hq hR.le
  have hn := mul_nonneg hc hS.le
  nlinarith

theorem PairRatio.zero_right {p a c : ℝ} (hp : p ≤ 1) (ha : 0 ≤ a) :
    PairRatio p 0 a c := by
  intro R S hR hS
  simp only [zero_mul, zero_div, add_zero]
  apply (div_le_iff₀ (by positivity : 0 < S + a * R)).mpr
  have hm := mul_le_mul_of_nonneg_right hp hS.le
  have hn := mul_nonneg ha hR.le
  nlinarith

private theorem reciprocal_sum_lower {x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x + y ≤ z) :
    4 / z ≤ 1 / x + 1 / y := by
  have hz : 0 < z := (add_pos hx hy).trans_le hxy
  have hid : 1 / x + 1 / y = (x + y) / (x * y) := by
    field_simp [hx.ne', hy.ne'] <;> ring
  rw [hid]
  apply (div_le_div_iff₀ hz (mul_pos hx hy)).mpr
  have hm := mul_le_mul_of_nonneg_right hxy (add_pos hx hy).le
  nlinarith [sq_nonneg (x - y)]

private theorem pair_weighted_le {p q a c A B : ℝ}
    (hpair : PairRatio p q a c) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hA : 0 < A) (hB : 0 < B) :
    p * A ^ 2 / (A / B + a) + q * B ^ 2 / (B / A + c) ≤ A * B := by
  have h := mul_le_mul_of_nonneg_left
    (hpair (1 / A) (1 / B) (one_div_pos.mpr hA) (one_div_pos.mpr hB))
    (mul_pos hA hB).le
  have hDa : 0 < A / B + a := add_pos_of_pos_of_nonneg (div_pos hA hB) ha
  have hDc : 0 < B / A + c := add_pos_of_pos_of_nonneg (div_pos hB hA) hc
  have hea : 1 / B + a * (1 / A) = (A / B + a) / A := by
    field_simp [hA.ne', hB.ne'] <;> ring
  have hec : 1 / A + c * (1 / B) = (B / A + c) / B := by
    field_simp [hA.ne', hB.ne'] <;> ring
  rw [hea, hec] at h
  have hid : A * B * (p * (1 / B) / ((A / B + a) / A) +
      q * (1 / A) / ((B / A + c) / B)) =
      p * A ^ 2 / (A / B + a) + q * B ^ 2 / (B / A + c) := by
    field_simp [hA.ne', hB.ne', hDa.ne', hDc.ne'] <;> ring
  rw [hid, mul_one] at h
  exact h

private theorem row_weighted_lower {p a b A B C : ℝ}
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) (hbudget : a + b ≤ 1)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    4 * (A * p) / (1 / A + 1 / B + 1 / C) ≤
      p * A ^ 2 / (A / B + a) + p * A ^ 2 / (A / C + b) := by
  let S := 1 / A + 1 / B + 1 / C
  have hS : 0 < S := by dsimp [S]; positivity
  have hx : 0 < A / B + a := add_pos_of_pos_of_nonneg (div_pos hA hB) ha
  have hy : 0 < A / C + b := add_pos_of_pos_of_nonneg (div_pos hA hC) hb
  have hAS : A * S = A / B + A / C + 1 := by
    dsimp [S]
    field_simp [hA.ne', hB.ne', hC.ne'] <;> ring
  have hz : (A / B + a) + (A / C + b) ≤ A * S := by
    rw [hAS]
    linarith
  have hm := mul_le_mul_of_nonneg_left (reciprocal_sum_lower hx hy hz)
    (mul_nonneg hp (sq_nonneg A))
  calc
    4 * (A * p) / S = (p * A ^ 2) * (4 / (A * S)) := by
      field_simp [hA.ne', hS.ne'] <;> ring
    _ ≤ (p * A ^ 2) * (1 / (A / B + a) + 1 / (A / C + b)) := hm
    _ = _ := by ring

theorem weighted_bound_of_pair_ratios
    (A B C p q r a b c d e f : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hX : a + b ≤ 1) (hY : c + d ≤ 1) (hZ : e + f ≤ 1)
    (hXY : PairRatio p q a c) (hXZ : PairRatio p r b e) (hYZ : PairRatio q r d f) :
    A * p + B * q + C * r ≤ (A * B + A * C + B * C) ^ 2 / (4 * A * B * C) := by
  let S := 1 / A + 1 / B + 1 / C
  have hS : 0 < S := by dsimp [S]; positivity
  have hAB := pair_weighted_le hXY ha hc hA hB
  have hAC := pair_weighted_le hXZ hb he hA hC
  have hBC := pair_weighted_le hYZ hd hf hB hC
  have hrowA := row_weighted_lower hp ha hb hX hA hB hC
  have hrowB := row_weighted_lower hq hc hd hY hB hA hC
  have hrowC := row_weighted_lower hr he hf hZ hC hA hB
  have hSB : 1 / B + 1 / A + 1 / C = S := by dsimp [S]; ring
  have hSC : 1 / C + 1 / A + 1 / B = S := by dsimp [S]; ring
  change 4 * (A * p) / S ≤ _ at hrowA
  rw [hSB] at hrowB
  rw [hSC] at hrowC
  have hsum : 4 * (A * p + B * q + C * r) / S ≤ A * B + A * C + B * C := by
    have hid : 4 * (A * p + B * q + C * r) / S =
        4 * (A * p) / S + 4 * (B * q) / S + 4 * (C * r) / S := by ring
    rw [hid]
    linarith
  have hnum := (div_le_iff₀ hS).mp hsum
  have hid : ((A * B + A * C + B * C) * S) / 4 =
      (A * B + A * C + B * C) ^ 2 / (4 * A * B * C) := by
    dsimp [S]
    field_simp [hA.ne', hB.ne', hC.ne'] <;> ring
  rw [← hid]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  simpa only [mul_comm] using hnum

end Lemmata.FockCircuits.Matrix.Profile
