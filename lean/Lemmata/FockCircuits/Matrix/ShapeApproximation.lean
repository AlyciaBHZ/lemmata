module

public import Lemmata.FockCircuits.Exponent
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix

open Filter Exponent
open scoped Topology

noncomputable section

private def upperShapeIndex (a : ℝ) (d : ℕ) : ℕ := Nat.ceil (a * (d : ℝ)) + 1

private theorem upperShapeIndex_pos (a : ℝ) (d : ℕ) : 0 < upperShapeIndex a d := by
  dsimp [upperShapeIndex]
  omega

private theorem upperShapeIndex_scale (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun d : ℕ => (upperShapeIndex a d : ℝ) / d) atTop (𝓝 a) := by
  have hN : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h := ((tendsto_nat_ceil_mul_div_atTop ha).comp hN).add
    (tendsto_const_nhds.div_atTop hN : Tendsto (fun d : ℕ => (1 : ℝ) / d) atTop (𝓝 0))
  simpa only [upperShapeIndex, Nat.cast_add, Nat.cast_one, add_div, add_zero,
    Function.comp_apply] using h

private theorem lt_upperShapeIndex_ratio (a : ℝ) {d : ℕ} (hd : 0 < d) :
    a < (upperShapeIndex a d : ℝ) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  apply (lt_div_iff₀ hdR).mpr
  have h := Nat.le_ceil (a * (d : ℝ))
  dsimp [upperShapeIndex]
  push_cast
  linarith

theorem exists_integer_outer_shape (A B C eps : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (heps : 0 < eps) :
    ∃ d a b c : ℕ, 0 < d ∧ 0 < a ∧ 0 < b ∧ 0 < c ∧
      A < (a : ℝ) / d ∧ B < (b : ℝ) / d ∧ C < (c : ℝ) / d ∧
      realRectangularRate a b c / d < realRectangularRate A B C + eps := by
  have hα := upperShapeIndex_scale A hA.le
  have hβ := upperShapeIndex_scale B hB.le
  have hγ := upperShapeIndex_scale C hC.le
  have hnum := (((hα.mul hβ).add (hα.mul hγ)).add (hβ.mul hγ)).pow 2
  have hfour : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4) := tendsto_const_nhds
  have hden := ((hfour.mul hα).mul hβ).mul hγ
  have hden0 : 4 * A * B * C ≠ 0 := by positivity
  have hlim := hnum.div hden hden0
  change Tendsto (fun d : ℕ => realRectangularRate
    ((upperShapeIndex A d : ℝ) / d) ((upperShapeIndex B d : ℝ) / d)
    ((upperShapeIndex C d : ℝ) / d)) atTop (𝓝 (realRectangularRate A B C)) at hlim
  obtain ⟨d, hd, hrate⟩ :=
    ((eventually_gt_atTop (0 : ℕ)).and
      (hlim.eventually_lt_const (by linarith : realRectangularRate A B C <
        realRectangularRate A B C + eps))).exists
  let a := upperShapeIndex A d
  let b := upperShapeIndex B d
  let c := upperShapeIndex C d
  have ha : 0 < a := upperShapeIndex_pos A d
  have hb : 0 < b := upperShapeIndex_pos B d
  have hc : 0 < c := upperShapeIndex_pos C d
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hhomogeneous : realRectangularRate ((a : ℝ) / d) ((b : ℝ) / d) ((c : ℝ) / d) =
      realRectangularRate a b c / d := by
    dsimp [realRectangularRate]
    field_simp [hdR.ne', haR.ne', hbR.ne', hcR.ne'] <;> ring
  refine ⟨d, a, b, c, hd, ha, hb, hc,
    lt_upperShapeIndex_ratio A hd, lt_upperShapeIndex_ratio B hd, lt_upperShapeIndex_ratio C hd, ?_⟩
  rwa [hhomogeneous] at hrate

end

end Lemmata.FockCircuits.Matrix
