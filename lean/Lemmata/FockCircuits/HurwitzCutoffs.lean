module

public import Lemmata.FockCircuits.Cutoffs

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits

open Filter
open scoped Topology

theorem doubled_energy_stateCount_exponent (b : ℝ) (hb : 0 < b) :
    Tendsto (fun n : ℕ =>
      Real.log (stateCount (2 * ceilLogEnergy countingConstant b n) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (Real.sqrt 2 * b)) := by
  obtain ⟨hHtop, hHscale, _⟩ := ceilLogEnergy_scale countingConstant b countingConstant_pos hb
  have htop : Tendsto (fun n => 2 * ceilLogEnergy countingConstant b n) atTop atTop :=
    tendsto_atTop_mono (fun n => by omega) hHtop
  have hscale : Tendsto (fun n : ℕ =>
      ((2 * ceilLogEnergy countingConstant b n : ℕ) : ℝ) / Real.log (n : ℝ) ^ 2)
      atTop (𝓝 (2 * (b / countingConstant) ^ 2)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc] using hHscale.const_mul 2
  have hroot := energy_sqrt_ratio_tendsto _ _ hscale
  have h := stateCount_log_exponent _ _ htop hroot
  have hid : countingConstant * Real.sqrt (2 * (b / countingConstant) ^ 2) = Real.sqrt 2 * b := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_sq (div_pos hb countingConstant_pos).le]
    field_simp [countingConstant_pos.ne'] <;> ring
  rwa [hid] at h

theorem exists_hurwitz_energy_parameters (eps : ℝ) (heps : 0 < eps) :
    ∃ padding : ℝ, let H := ceilLogEnergy countingConstant (1 + padding)
      0 < padding ∧ (∀ᶠ n : ℕ in atTop,
        0 < H n ∧ 2 * H n * n ≤ stateCount (H n) - 1 ∧
          ((4 * stateCount (2 * H n) : ℕ) : ℝ) ≤ (n : ℝ) ^ (Real.sqrt 2 + eps)) := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  let padding : ℝ := eps / (2 * Real.sqrt 2)
  have hpadding : 0 < padding := div_pos heps (mul_pos (by norm_num) hsqrt)
  have hb : 0 < 1 + padding := by linarith
  let H := ceilLogEnergy countingConstant (1 + padding)
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hfour : Tendsto (fun n : ℕ => Real.log ((4 : ℕ) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  have hnonzero : ∀ᶠ n : ℕ in atTop, stateCount (2 * H n) ≠ 0 :=
    Eventually.of_forall fun n => (stateCount_pos _).ne'
  have hlim := log_nat_product_limit (fun _ : ℕ => 4) (fun n => stateCount (2 * H n))
    0 (Real.sqrt 2 * (1 + padding)) (Eventually.of_forall fun _ => by norm_num) hnonzero hfour
    (doubled_energy_stateCount_exponent (1 + padding) hb)
  simp only [zero_add] at hlim
  have hbound := eventually_le_rpow_of_log_limit (fun n => 4 * stateCount (2 * H n))
    (Real.sqrt 2 * (1 + padding))
    (hnonzero.mono fun _ hn => Nat.mul_ne_zero (by norm_num) hn) hlim (eps / 2) (by linarith)
  have hid : Real.sqrt 2 * (1 + padding) + eps / 2 = Real.sqrt 2 + eps := by
    dsimp [padding]
    field_simp [hsqrt.ne'] <;> ring
  rw [hid] at hbound
  have hHtop := (ceilLogEnergy_scale countingConstant (1 + padding) countingConstant_pos hb).1
  refine ⟨padding, hpadding, ?_⟩
  filter_upwards [hHtop.eventually_gt_atTop 0,
    ceilLogEnergy_capacity (1 + padding) (by linarith), hbound] with n hH hcapacity hbound
  exact ⟨hH, hcapacity, hbound⟩

end Lemmata.FockCircuits
