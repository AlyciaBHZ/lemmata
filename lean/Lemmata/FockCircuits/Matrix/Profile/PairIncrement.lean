module

public import Lemmata.FockCircuits.Matrix.Profile.Weighted
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Tactic.FieldSimp

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Profile

open Filter Set
open scoped Topology

theorem derivative_nonneg_of_right_nonneg {f : ℝ → ℝ} {d : ℝ}
    (hf : HasDerivAt f d 0) (hzero : f 0 = 0)
    (hnonneg : ∀ t, 0 < t → 0 ≤ f t) : 0 ≤ d := by
  apply ge_of_tendsto hf.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  simp only [zero_add, hzero, sub_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr ht.le) (hnonneg t ht)

theorem log_one_add_ratio_derivative (r s a : ℝ) (hs : s ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log (1 + t * r / (s + a * t))) (r / s) 0 := by
  have hnum : HasDerivAt (fun t : ℝ => t * r) r 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const r
  have hden : HasDerivAt (fun t : ℝ => s + a * t) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul a).const_add s
  have h := hnum.div hden (by simpa using hs)
  have heq : (r * (s + a * 0) - (0 * r) * a) / (s + a * 0) ^ 2 = r / s := by
    simp only [mul_zero, zero_mul, add_zero, sub_zero]
    field_simp [hs]
  have hratio : HasDerivAt (fun t : ℝ => t * r / (s + a * t)) (r / s) 0 := by
    change HasDerivAt (fun t : ℝ => t * r / (s + a * t))
      ((r * (s + a * 0) - (0 * r) * a) / (s + a * 0) ^ 2) 0 at h
    rw [heq] at h
    exact h
  simpa using (hratio.const_add 1).log (by norm_num)

/-- A finite two-step increment bound gives the corresponding rational pair inequality. -/
theorem pair_ratio_at_of_product_bound {p q a c R S : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hR : 0 < R) (hS : 0 < S)
    (hbound : ∀ t : ℝ, 0 < t →
      (1 + t * R / (R + c * S)) ^ q *
        (1 + t * S / ((S + a * R) + a * R * t)) ^ p ≤ 1 + t) :
    p * S / (S + a * R) + q * R / (R + c * S) ≤ 1 := by
  have hdR : 0 < R + c * S := add_pos_of_pos_of_nonneg hR (mul_nonneg hc hS.le)
  have hdS : 0 < S + a * R := add_pos_of_pos_of_nonneg hS (mul_nonneg ha hR.le)
  let f := fun t : ℝ => Real.log (1 + t) -
    q * Real.log (1 + t * R / (R + c * S)) -
    p * Real.log (1 + t * S / ((S + a * R) + a * R * t))
  have h1 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) 1 0 := by
    simpa using log_one_add_ratio_derivative 1 1 0 one_ne_zero
  have h2 : HasDerivAt (fun t : ℝ => Real.log (1 + t * R / (R + c * S)))
      (R / (R + c * S)) 0 := by
    simpa using log_one_add_ratio_derivative R (R + c * S) 0 hdR.ne'
  have h3 := log_one_add_ratio_derivative S (S + a * R) (a * R) hdS.ne'
  have hder : HasDerivAt f
      (1 - q * (R / (R + c * S)) - p * (S / (S + a * R))) 0 := by
    have h := (h1.sub (h2.const_mul q)).sub (h3.const_mul p)
    change HasDerivAt f
      (1 - q * (R / (R + c * S)) - p * (S / (S + a * R))) 0 at h
    exact h
  have hzero : f 0 = 0 := by simp [f]
  have hnonneg (t : ℝ) (ht : 0 < t) : 0 ≤ f t := by
    have hbR : 0 < 1 + t * R / (R + c * S) := by positivity
    have hbS : 0 < 1 + t * S / ((S + a * R) + a * R * t) := by positivity
    have hlog := Real.log_le_log
      (mul_pos (Real.rpow_pos_of_pos hbR q) (Real.rpow_pos_of_pos hbS p)) (hbound t ht)
    rw [Real.log_mul (Real.rpow_pos_of_pos hbR q).ne'
      (Real.rpow_pos_of_pos hbS p).ne', Real.log_rpow hbR, Real.log_rpow hbS] at hlog
    dsimp [f]
    linarith
  have hder_nonneg := derivative_nonneg_of_right_nonneg hder hzero hnonneg
  rw [mul_div_assoc, mul_div_assoc]
  linarith

theorem pairRatio_of_product_bounds {p q a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hbound : ∀ R S : ℝ, 0 < R → 0 < S → ∀ t : ℝ, 0 < t →
      (1 + t * R / (R + c * S)) ^ q *
        (1 + t * S / ((S + a * R) + a * R * t)) ^ p ≤ 1 + t) :
    PairRatio p q a c := by
  intro R S hR hS
  exact pair_ratio_at_of_product_bound ha hc hR hS (hbound R S hR hS)

end Lemmata.FockCircuits.Matrix.Profile
