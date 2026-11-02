module

public import Lemmata.FockCircuits.Matrix.ShapeApproximation
public import Lemmata.FockCircuits.Cutoffs
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix

open Filter Exponent
open scoped Topology

noncomputable section

def rootScale (d n : ℕ) : ℕ := Nat.ceil ((n : ℝ) ^ (1 / (d : ℝ)))

theorem rootScale_tendsto (d : ℕ) (hd : 0 < d) : Tendsto (rootScale d) atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (d : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop (one_div_pos.mpr (by exact_mod_cast hd))).comp tendsto_natCast_atTop_atTop
  exact tendsto_nat_ceil_atTop.comp hpow

theorem rootScale_log_exponent (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => Real.log (rootScale d n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (1 / (d : ℝ))) := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / (d : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop (one_div_pos.mpr (by exact_mod_cast hd))).comp tendsto_natCast_atTop_atTop
  apply ceil_log_exponent _ _ hpow
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  rw [Real.log_rpow hnpos]
  field_simp [hlog]

theorem rpow_le_rootScale_power (d a n : ℕ) :
    (n : ℝ) ^ ((a : ℝ) / d) ≤ ((rootScale d n ^ a : ℕ) : ℝ) := by
  have hceil := Nat.le_ceil ((n : ℝ) ^ (1 / (d : ℝ)))
  have h := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg n) _) hceil a
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n), show (1 / (d : ℝ)) * a = (a : ℝ) / d by ring] at h
  simpa only [rootScale, Nat.cast_pow] using h

theorem eventually_le_rootScale_power (f : ℕ → ℕ) (L : ℝ) (d a : ℕ)
    (hf : ∀ᶠ n : ℕ in atTop, f n ≠ 0)
    (hlim : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 L))
    (hfit : L < (a : ℝ) / d) :
    ∀ᶠ n : ℕ in atTop, f n ≤ rootScale d n ^ a := by
  have h := eventually_le_rpow_of_log_limit f L hf hlim ((a : ℝ) / d - L) (sub_pos.mpr hfit)
  have hid : L + ((a : ℝ) / d - L) = (a : ℝ) / d := by ring
  rw [hid] at h
  filter_upwards [h] with n hn
  exact_mod_cast hn.trans (rpow_le_rootScale_power d a n)

theorem eventually_rootScale_rpow_le (d : ℕ) (hd : 0 < d) (M L : ℝ)
    (hrate : M / d < L) :
    ∀ᶠ n : ℕ in atTop, (rootScale d n : ℝ) ^ M ≤ (n : ℝ) ^ L := by
  have hlim := (rootScale_log_exponent d hd).const_mul M
  have hnorm : Tendsto (fun n : ℕ => M * (Real.log (rootScale d n : ℝ) / Real.log (n : ℝ)))
      atTop (𝓝 (M / d)) := by simpa only [mul_one_div] using hlim
  filter_upwards [hnorm.eventually_lt_const hrate, eventually_gt_atTop (1 : ℕ)] with n hbound hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hscale : (0 : ℝ) < rootScale d n := by
    exact_mod_cast Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hnpos (1 / (d : ℝ)))
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hscale M) (Real.rpow_pos_of_pos hnpos L)).mp
  rw [Real.log_rpow hscale, Real.log_rpow hnpos]
  have hdiv : M * Real.log (rootScale d n : ℝ) / Real.log (n : ℝ) < L := by
    simpa only [mul_div_assoc] using hbound
  exact ((div_lt_iff₀ hlog).mp hdiv).le

theorem stacked_stateCount_exponent (b a : ℝ) (hb : 0 < b) (ha : 0 < a) :
    Tendsto (fun n : ℕ => Real.log
      (((2 * ceilLogEnergy countingConstant b n) *
        stateCount (ceilLogEnergy countingConstant b n + floorLogEnergy countingConstant a n) : ℕ) : ℝ) /
        Real.log (n : ℝ)) atTop (𝓝 (Real.sqrt (b ^ 2 + a ^ 2))) := by
  let H := ceilLogEnergy countingConstant b
  let E := floorLogEnergy countingConstant a
  obtain ⟨hHtop, hHscale, _⟩ := ceilLogEnergy_scale countingConstant b countingConstant_pos hb
  have hHnz : ∀ᶠ n : ℕ in atTop, H n ≠ 0 :=
    (hHtop.eventually_gt_atTop 0).mono fun _ h => Nat.ne_of_gt h
  have hHlog := log_energy_ratio_tendsto_zero H _
    (sq_pos_of_pos (div_pos hb countingConstant_pos)) hHtop hHscale
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htwo : Tendsto (fun n : ℕ => Real.log ((2 : ℕ) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  have h2Hnz : ∀ᶠ n : ℕ in atTop, 2 * H n ≠ 0 :=
    hHnz.mono fun _ hn => Nat.mul_ne_zero (by norm_num) hn
  have h2Hlog := log_nat_product_limit (fun _ : ℕ => 2) H 0 0
    (Eventually.of_forall fun _ => by norm_num) hHnz htwo hHlog
  simp only [zero_add] at h2Hlog
  have hrows := sumLogEnergy_stateCount_exponent b a hb ha
  have hrowsnz : ∀ᶠ n : ℕ in atTop, stateCount (H n + E n) ≠ 0 :=
    Eventually.of_forall fun _ => (stateCount_pos _).ne'
  simpa only [zero_add] using log_nat_product_limit (fun n => 2 * H n)
    (fun n => stateCount (H n + E n)) 0 (Real.sqrt (b ^ 2 + a ^ 2)) h2Hnz hrowsnz h2Hlog hrows

theorem exists_exterior_shape_parameters (eps : ℝ) (heps : 0 < eps) :
    ∃ padding : ℝ, ∃ d a b c : ℕ, ∃ eta : ℝ,
      let H := ceilLogEnergy countingConstant (1 + padding)
      let E := floorLogEnergy countingConstant optimalInput
      0 < padding ∧ 0 < d ∧ 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < eta ∧
        (∀ᶠ n : ℕ in atTop, 0 < H n ∧ 2 * H n * n ≤ stateCount (H n) - 1 ∧
          stateCount (H n + E n) ≤ rootScale d n ^ a ∧
          (2 * H n) * stateCount (H n + E n) ≤ rootScale d n ^ a ∧
          stateCount (E n) ≤ rootScale d n ^ b ∧
          batchCount n (stateCount (E n)) ≤ rootScale d n ^ c ∧
          (rootScale d n : ℝ) ^ (realRectangularRate a b c + eta) ≤ (n : ℝ) ^ (gamma + eps)) ∧
        Tendsto (fun n : ℕ => Real.log (((H n + E n + 1 : ℕ) : ℝ) ^ 3) / Real.log (n : ℝ))
          atTop (𝓝 0) := by
  obtain ⟨padding, hpadding, hrate⟩ := exists_padded_rate_lt (eps / 3) (by linarith)
  let row := Real.sqrt ((1 + padding) ^ 2 + optimalInput ^ 2)
  have hrow : 0 < row := Real.sqrt_pos.mpr (by positivity)
  have hinput := optimal_parameters.1
  have hbatch := optimal_parameters.2.2.1
  obtain ⟨d, a, b, c, hd, ha, hb, hc, hfitA, hfitB, hfitC, houter⟩ :=
    exists_integer_outer_shape row optimalInput optimalBatch (eps / 3) hrow hinput hbatch (by linarith)
  let eta : ℝ := (d : ℝ) * (eps / 3)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heta : 0 < eta := mul_pos hdR (by linarith)
  have hetadiv : eta / (d : ℝ) = eps / 3 := by
    dsimp [eta]
    exact mul_div_cancel_left₀ _ hdR.ne'
  have htotal : (realRectangularRate a b c + eta) / d < gamma + eps := by
    rw [add_div, hetadiv]
    dsimp only [row] at houter
    linarith
  let H := ceilLogEnergy countingConstant (1 + padding)
  let E := floorLogEnergy countingConstant optimalInput
  have hHtop := (ceilLogEnergy_scale countingConstant (1 + padding) countingConstant_pos (by linarith)).1
  have hrows := eventually_le_rootScale_power (fun n => stateCount (H n + E n)) row d a
    (Eventually.of_forall fun n => (stateCount_pos _).ne')
    (sumLogEnergy_stateCount_exponent (1 + padding) optimalInput (by linarith) hinput) hfitA
  have hmiddle := eventually_le_rootScale_power (fun n => stateCount (E n)) optimalInput d b
    (Eventually.of_forall fun n => (stateCount_pos _).ne')
    (floorLogEnergy_stateCount_exponent optimalInput hinput) hfitB
  have hstackednz : ∀ᶠ n : ℕ in atTop, (2 * H n) * stateCount (H n + E n) ≠ 0 :=
    (hHtop.eventually_gt_atTop 0).mono fun _ hn =>
      Nat.mul_ne_zero (Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt hn)) (stateCount_pos _).ne'
  have hstacked := eventually_le_rootScale_power (fun n => (2 * H n) * stateCount (H n + E n))
    row d a hstackednz
    (stacked_stateCount_exponent (1 + padding) optimalInput (by linarith) hinput) hfitA
  have hcolumnsPos : ∀ᶠ n : ℕ in atTop, batchCount n (stateCount (E n)) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    apply Nat.ne_of_gt
    apply Nat.ceil_pos.mpr
    exact div_pos (by exact_mod_cast hn) (by exact_mod_cast stateCount_pos (E n))
  have hcolumns := eventually_le_rootScale_power (fun n => batchCount n (stateCount (E n)))
    optimalBatch d c hcolumnsPos
    (floorLogEnergy_batch_exponent optimalInput hinput optimal_parameters.2.1) hfitC
  refine ⟨padding, d, a, b, c, eta, hpadding, hd, ha, hb, hc, heta, ?_, ?_⟩
  · filter_upwards [hHtop.eventually_gt_atTop 0,
      ceilLogEnergy_capacity (1 + padding) (by linarith), hrows, hstacked, hmiddle, hcolumns,
      eventually_rootScale_rpow_le d hd (realRectangularRate a b c + eta) (gamma + eps) htotal]
      with n hH hcapacity hrows hstacked hmiddle hcolumns hcost
    exact ⟨hH, hcapacity, hrows, hstacked, hmiddle, hcolumns, hcost⟩
  · exact sumLogEnergy_overhead_exponent (1 + padding) optimalInput (by linarith) hinput

end

end Lemmata.FockCircuits.Matrix
