module

public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Exponent

def rectangularRate (a b c : ℚ) : ℚ :=
  (a * b + a * c + b * c) ^ 2 / (4 * a * b * c)

def inputExponent : ℚ := 23 / 51

def batchExponent : ℚ := 28 / 51

def rowExponent : ℚ := 56 / 51

theorem parameters :
    0 < inputExponent ∧ 0 < batchExponent ∧ 0 < rowExponent ∧
      inputExponent + batchExponent = 1 ∧ rowExponent = 2 * batchExponent := by
  norm_num [inputExponent, batchExponent, rowExponent]

theorem row_padding_gap :
    rowExponent ^ 2 - (1 + inputExponent ^ 2) = (6 : ℚ) / 2601 := by
  norm_num [inputExponent, rowExponent]

theorem row_padding :
    1 + inputExponent ^ 2 < rowExponent ^ 2 := by
  norm_num [inputExponent, rowExponent]

def energySlack : ℚ := 1 / 10000

theorem energySlack_pos : 0 < energySlack := by
  norm_num [energySlack]

theorem padded_row_padding :
    (1 + energySlack) ^ 2 + inputExponent ^ 2 < rowExponent ^ 2 := by
  norm_num [energySlack, inputExponent, rowExponent]

theorem matrix_rate :
    rectangularRate rowExponent inputExponent batchExponent = (15625 : ℚ) / 9384 := by
  norm_num [rectangularRate, inputExponent, batchExponent, rowExponent]

theorem matrix_rate_gap :
    5 / 3 - rectangularRate rowExponent inputExponent batchExponent = (5 : ℚ) / 3128 := by
  norm_num [rectangularRate, inputExponent, batchExponent, rowExponent]

theorem matrix_rate_lt_five_thirds :
    rectangularRate rowExponent inputExponent batchExponent < 5 / 3 := by
  norm_num [rectangularRate, inputExponent, batchExponent, rowExponent]

noncomputable def realRectangularRate (a b c : ℝ) : ℝ :=
  (a * b + a * c + b * c) ^ 2 / (4 * a * b * c)

theorem realRectangularRate_slot_gap (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    realRectangularRate A B C - (A + B) =
      (A * B - C * (A + B)) ^ 2 / (4 * A * B * C) := by
  dsimp [realRectangularRate]
  field_simp [hA.ne', hB.ne', hC.ne']; ring

theorem realRectangularRate_slot_bounds (A B C : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    A + B ≤ realRectangularRate A B C ∧ A + C ≤ realRectangularRate A B C ∧
      B + C ≤ realRectangularRate A B C := by
  have hbase (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
      a + b ≤ realRectangularRate a b c := by
    apply sub_nonneg.mp
    rw [realRectangularRate_slot_gap a b c ha hb hc]
    positivity
  have hAC : realRectangularRate A C B = realRectangularRate A B C := by
    dsimp [realRectangularRate]
    congr 1 <;> ring
  have hBC : realRectangularRate B C A = realRectangularRate A B C := by
    dsimp [realRectangularRate]
    congr 1 <;> ring
  exact ⟨hbase A B C hA hB hC, hAC ▸ hbase A C B hA hC hB,
    hBC ▸ hbase B C A hB hC hA⟩

noncomputable def optimalInput : ℝ := (4 - Real.sqrt 7) / 3

noncomputable def optimalBatch : ℝ := 1 - optimalInput

noncomputable def optimalRow : ℝ := 2 * optimalBatch

noncomputable def gamma : ℝ := 4 / 3 + Real.sqrt 7 / 8

theorem sqrt_seven_bounds : 2 < Real.sqrt 7 ∧ Real.sqrt 7 < 8 / 3 := by
  have hs : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hnonneg := Real.sqrt_nonneg (7 : ℝ)
  constructor <;> nlinarith

theorem optimal_parameters :
    0 < optimalInput ∧ optimalInput < 1 ∧ 0 < optimalBatch ∧ 0 < optimalRow ∧
      optimalInput + optimalBatch = 1 ∧ optimalRow ^ 2 = 1 + optimalInput ^ 2 := by
  obtain ⟨hlow, hhigh⟩ := sqrt_seven_bounds
  have hs : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp [optimalInput, optimalBatch, optimalRow] <;> nlinarith

theorem optimal_input_inverse : 1 / optimalInput = (4 + Real.sqrt 7) / 3 := by
  have hprod : optimalInput * ((4 + Real.sqrt 7) / 3) = 1 := by
    have hs : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
    dsimp [optimalInput]
    nlinarith
  apply (div_eq_iff optimal_parameters.1.ne').mpr
  nlinarith

theorem optimal_row_sqrt : Real.sqrt (1 + optimalInput ^ 2) = optimalRow := by
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + optimalInput ^ 2 by positivity)
  have hnonneg := Real.sqrt_nonneg (1 + optimalInput ^ 2)
  have hrow := optimal_parameters.2.2.2.1
  have heq := optimal_parameters.2.2.2.2.2
  nlinarith

theorem optimal_rate : realRectangularRate optimalRow optimalInput optimalBatch = gamma := by
  have ha := optimal_parameters.1
  have hb := optimal_parameters.2.2.1
  have hab := optimal_parameters.2.2.2.2.1
  have hsum : 3 * optimalInput + 2 * optimalBatch = optimalInput + 2 := by linarith
  calc
    realRectangularRate optimalRow optimalInput optimalBatch =
        (3 * optimalInput + 2 * optimalBatch) ^ 2 / (8 * optimalInput) := by
      dsimp [realRectangularRate, optimalRow]
      field_simp [ha.ne', hb.ne']; ring
    _ = (optimalInput + 2) ^ 2 / (8 * optimalInput) := by rw [hsum]
    _ = (optimalInput + 4 + 4 * (1 / optimalInput)) / 8 := by
      field_simp [ha.ne']; ring
    _ = gamma := by
      rw [optimal_input_inverse]
      dsimp [optimalInput, gamma]
      ring

theorem gamma_lt_five_thirds : gamma < 5 / 3 := by
  have h := sqrt_seven_bounds.2
  dsimp [gamma]
  linarith

open Filter
open scoped Topology

theorem padded_rate_tendsto :
    Tendsto (fun d : ℝ =>
      realRectangularRate (Real.sqrt ((1 + d) ^ 2 + optimalInput ^ 2)) optimalInput optimalBatch)
      (𝓝 0) (𝓝 gamma) := by
  have hid : Tendsto (fun d : ℝ => d) (𝓝 0) (𝓝 0) := tendsto_id
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝 0) (𝓝 1) := tendsto_const_nhds
  have hrow : Tendsto (fun d : ℝ => Real.sqrt ((1 + d) ^ 2 + optimalInput ^ 2))
      (𝓝 0) (𝓝 optimalRow) := by
    have h := (((hone.add hid).pow 2).add_const (optimalInput ^ 2)).sqrt
    simpa only [add_zero, one_pow, optimal_row_sqrt] using h
  have hnum := (((hrow.mul_const optimalInput).add (hrow.mul_const optimalBatch)).add
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => optimalInput * optimalBatch)
      (𝓝 0) (𝓝 (optimalInput * optimalBatch)))).pow 2
  have hden := ((hrow.const_mul 4).mul_const optimalInput).mul_const optimalBatch
  have hden0 : 4 * optimalRow * optimalInput * optimalBatch ≠ 0 := by
    have ha := optimal_parameters.1
    have hb := optimal_parameters.2.2.1
    have hr := optimal_parameters.2.2.2.1
    positivity
  have h := hnum.div hden hden0
  change Tendsto _ (𝓝 0) (𝓝 (realRectangularRate optimalRow optimalInput optimalBatch)) at h
  rwa [optimal_rate] at h

theorem exists_padded_rate_lt (eps : ℝ) (heps : 0 < eps) :
    ∃ d : ℝ, 0 < d ∧
      realRectangularRate (Real.sqrt ((1 + d) ^ 2 + optimalInput ^ 2)) optimalInput optimalBatch <
        gamma + eps := by
  have hlim := padded_rate_tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hpos : ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d := self_mem_nhdsWithin
  obtain ⟨d, hd, hrate⟩ :=
    (hpos.and (hlim.eventually_lt_const (by linarith : gamma < gamma + eps))).exists
  exact ⟨d, hd, hrate⟩

end Lemmata.FockCircuits.Exponent
