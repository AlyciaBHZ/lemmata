module

public import Lemmata.FockCircuits.PartitionAnalysis
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits

open Filter
open scoped Topology

noncomputable def countingConstant : ℝ := 2 * Real.sqrt fermionIntegral

theorem countingConstant_pos : 0 < countingConstant := by
  exact mul_pos (by norm_num) (Real.sqrt_pos.mpr fermionIntegral_pos)

theorem stateCount_pos (H : ℕ) : 0 < stateCount H := by
  apply Finset.card_pos.mpr
  exact ⟨∅, by simp [doubledEnergy]⟩

theorem stateCount_log_exponent (energy : ℕ → ℕ) (b : ℝ)
    (htop : Tendsto energy atTop atTop)
    (hscale : Tendsto (fun n : ℕ => Real.sqrt (energy n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 b)) :
    Tendsto (fun n : ℕ => Real.log (stateCount (energy n) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (countingConstant * b)) := by
  have h := (fullCutoff_log_tendsto.comp htop).mul hscale
  refine h.congr' ?_
  filter_upwards [htop.eventually_gt_atTop 0] with n hn
  have hroot : Real.sqrt (energy n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  simp only [Function.comp_apply, stateCount]
  field_simp [hroot]

theorem ceilLogEnergy_stateCount_exponent (b : ℝ) (hb : 0 < b) :
    Tendsto (fun n : ℕ =>
      Real.log (stateCount (ceilLogEnergy countingConstant b n) : ℝ) /
        Real.log (n : ℝ)) atTop (𝓝 b) := by
  obtain ⟨htop, _, hroot⟩ := ceilLogEnergy_scale countingConstant b countingConstant_pos hb
  have h := stateCount_log_exponent _ _ htop hroot
  simpa only [mul_div_cancel₀ _ countingConstant_pos.ne'] using h

theorem floorLogEnergy_stateCount_exponent (b : ℝ) (hb : 0 < b) :
    Tendsto (fun n : ℕ =>
      Real.log (stateCount (floorLogEnergy countingConstant b n) : ℝ) /
        Real.log (n : ℝ)) atTop (𝓝 b) := by
  obtain ⟨htop, _, hroot⟩ := floorLogEnergy_scale countingConstant b countingConstant_pos hb
  have h := stateCount_log_exponent _ _ htop hroot
  simpa only [mul_div_cancel₀ _ countingConstant_pos.ne'] using h

theorem log_energy_ratio_tendsto_zero (energy : ℕ → ℕ) (K : ℝ) (hK : 0 < K)
    (htop : Tendsto energy atTop atTop)
    (hscale : Tendsto (fun n : ℕ => (energy n : ℝ) / Real.log (n : ℝ) ^ 2)
      atTop (𝓝 K)) :
    Tendsto (fun n : ℕ => Real.log (energy n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnorm := (hscale.log hK.ne').div_atTop hlog
  have hloglog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have h := hnorm.add (hloglog.const_mul 2)
  simp only [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [htop.eventually_gt_atTop 0, hlog.eventually_gt_atTop 0]
    with n hE hn
  simp only [Function.comp_apply, id_eq]
  have hE' : (energy n : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
  rw [Real.log_div hE' (pow_ne_zero _ hn.ne'), Real.log_pow]
  ring

theorem eventually_stateCount_capacity (energy : ℕ → ℕ) (b : ℝ) (hb : 1 < b)
    (htop : Tendsto energy atTop atTop)
    (hcount : Tendsto (fun n : ℕ =>
      Real.log (stateCount (energy n) : ℝ) / Real.log (n : ℝ)) atTop (𝓝 b))
    (henergy : Tendsto (fun n : ℕ => Real.log (energy n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, 2 * energy n * n ≤ stateCount (energy n) - 1 := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun n : ℕ => Real.log 3 / Real.log (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  have hbound : Tendsto (fun n : ℕ =>
      1 + (Real.log 3 / Real.log (n : ℝ) +
        Real.log (energy n : ℝ) / Real.log (n : ℝ))) atTop (𝓝 1) := by
    simpa only [add_zero, zero_add] using
      tendsto_const_nhds.add (hconst.add henergy)
  have hmiddle : 1 < (1 + b) / 2 ∧ (1 + b) / 2 < b := by constructor <;> linarith
  filter_upwards [hcount.eventually_const_lt hmiddle.2,
    hbound.eventually_lt_const hmiddle.1, htop.eventually_gt_atTop 0,
    eventually_gt_atTop (1 : ℕ), hlog.eventually_gt_atTop 0]
    with n hcount hbound hE hn hln
  have hEpos : (0 : ℝ) < energy n := by exact_mod_cast hE
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hQpos : (0 : ℝ) < stateCount (energy n) := by
    exact_mod_cast stateCount_pos (energy n)
  have hprod : (0 : ℝ) < 3 * energy n * n := by positivity
  have hid : Real.log (3 * (energy n : ℝ) * n) / Real.log (n : ℝ) =
      1 + (Real.log 3 / Real.log (n : ℝ) +
        Real.log (energy n : ℝ) / Real.log (n : ℝ)) := by
    rw [Real.log_mul (by positivity : (3 : ℝ) * energy n ≠ 0) hnpos.ne',
      Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hEpos.ne']
    field_simp [hln.ne']; ring
  have hlt : Real.log (3 * (energy n : ℝ) * n) <
      Real.log (stateCount (energy n) : ℝ) := by
    exact (div_lt_div_iff_of_pos_right hln).mp (by rw [hid]; exact hbound.trans hcount)
  have hnat : 3 * energy n * n < stateCount (energy n) := by
    exact_mod_cast (Real.log_lt_log_iff hprod hQpos).mp hlt
  have hcapacity : 2 * energy n * n < stateCount (energy n) :=
    (Nat.mul_le_mul_right n (Nat.mul_le_mul_right (energy n) (by omega : 2 ≤ 3))).trans_lt hnat
  omega

theorem ceilLogEnergy_capacity (b : ℝ) (hb : 1 < b) :
    ∀ᶠ n : ℕ in atTop,
      2 * ceilLogEnergy countingConstant b n * n ≤
        stateCount (ceilLogEnergy countingConstant b n) - 1 := by
  obtain ⟨htop, hscale, _⟩ :=
    ceilLogEnergy_scale countingConstant b countingConstant_pos (by linarith)
  apply eventually_stateCount_capacity _ b hb htop (ceilLogEnergy_stateCount_exponent b (by linarith))
  exact log_energy_ratio_tendsto_zero _ _ (sq_pos_of_pos (div_pos (by linarith) countingConstant_pos))
    htop hscale

theorem sumLogEnergy_scale (b a : ℝ) (hb : 0 < b) (ha : 0 < a) :
    Tendsto (fun n : ℕ =>
      ceilLogEnergy countingConstant b n + floorLogEnergy countingConstant a n)
      atTop atTop ∧
    Tendsto (fun n : ℕ =>
      ((ceilLogEnergy countingConstant b n + floorLogEnergy countingConstant a n : ℕ) : ℝ) /
        Real.log (n : ℝ) ^ 2) atTop
      (𝓝 ((b / countingConstant) ^ 2 + (a / countingConstant) ^ 2)) := by
  obtain ⟨htop, hH, _⟩ := ceilLogEnergy_scale countingConstant b countingConstant_pos hb
  obtain ⟨_, hE, _⟩ := floorLogEnergy_scale countingConstant a countingConstant_pos ha
  constructor
  · exact tendsto_atTop_mono (fun n => Nat.le_add_right _ _) htop
  · simpa only [Nat.cast_add, add_div] using hH.add hE

theorem sumLogEnergy_stateCount_exponent (b a : ℝ) (hb : 0 < b) (ha : 0 < a) :
    Tendsto (fun n : ℕ =>
      Real.log (stateCount
        (ceilLogEnergy countingConstant b n + floorLogEnergy countingConstant a n) : ℝ) /
        Real.log (n : ℝ)) atTop (𝓝 (Real.sqrt (b ^ 2 + a ^ 2))) := by
  obtain ⟨htop, hscale⟩ := sumLogEnergy_scale b a hb ha
  have hroot := energy_sqrt_ratio_tendsto _ _ hscale
  have h := stateCount_log_exponent _ _ htop hroot
  have hid : (b / countingConstant) ^ 2 + (a / countingConstant) ^ 2 =
      (b ^ 2 + a ^ 2) / countingConstant ^ 2 := by
    field_simp [countingConstant_pos.ne']
  have hconstant : countingConstant *
      Real.sqrt ((b / countingConstant) ^ 2 + (a / countingConstant) ^ 2) =
      Real.sqrt (b ^ 2 + a ^ 2) := by
    rw [hid, Real.sqrt_div (by positivity), Real.sqrt_sq countingConstant_pos.le,
      mul_div_cancel₀ _ countingConstant_pos.ne']
  rwa [hconstant] at h

theorem eventually_homogeneous_family (b : ℝ) (hb : 1 < b) :
    ∀ᶠ n : ℕ in atTop,
      ∃ (W : ℕ) (S : Finset (Finset ℕ)),
        0 < W ∧ W ≤ 2 * ceilLogEnergy countingConstant b n ∧
          S.card = n ∧ ∀ I ∈ S, doubledEnergy I = W := by
  have htop := (ceilLogEnergy_scale countingConstant b countingConstant_pos (by linarith)).1
  filter_upwards [ceilLogEnergy_capacity b hb, htop.eventually_gt_atTop 0]
    with n hcapacity hpos
  exact exists_homogeneous_family _ _ hpos hcapacity

theorem tendsto_atTop_of_log_exponent (f : ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hpos : ∀ᶠ n : ℕ in atTop, 0 < f n)
    (hscale : Tendsto (fun n : ℕ => Real.log (f n) / Real.log (n : ℝ))
      atTop (𝓝 a)) : Tendsto f atTop atTop := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hln : Tendsto (fun n : ℕ => Real.log (f n)) atTop atTop := by
    have h := hscale.pos_mul_atTop ha hlog
    refine h.congr' ?_
    filter_upwards [hlog.eventually_gt_atTop 0] with n hn
    exact div_mul_cancel₀ _ hn.ne'
  refine (Real.tendsto_exp_atTop.comp hln).congr' ?_
  filter_upwards [hpos] with n hn
  exact Real.exp_log hn

theorem ceil_log_exponent (f : ℕ → ℝ) (a : ℝ)
    (htop : Tendsto f atTop atTop)
    (hscale : Tendsto (fun n : ℕ => Real.log (f n) / Real.log (n : ℝ))
      atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => Real.log (Nat.ceil (f n) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 a) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio := (tendsto_nat_ceil_div_atTop.comp htop).log (by norm_num : (1 : ℝ) ≠ 0)
  rw [Real.log_one] at hratio
  have h := (hratio.div_atTop hlog).add hscale
  simp only [zero_add] at h
  refine h.congr' ?_
  filter_upwards [htop.eventually_gt_atTop 0] with n hn
  have hceil : (0 : ℝ) < Nat.ceil (f n) := by
    exact_mod_cast Nat.ceil_pos.mpr hn
  simp only [Function.comp_apply]
  rw [Real.log_div hceil.ne' hn.ne']
  ring

noncomputable def batchCount (n m : ℕ) : ℕ := Nat.ceil ((n : ℝ) / m)

theorem floorLogEnergy_batch_exponent (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun n : ℕ =>
      Real.log (batchCount n (stateCount (floorLogEnergy countingConstant a n)) : ℝ) /
        Real.log (n : ℝ)) atTop (𝓝 (1 - a)) := by
  let f : ℕ → ℝ := fun n => (n : ℝ) / stateCount (floorLogEnergy countingConstant a n)
  have hscale : Tendsto (fun n : ℕ => Real.log (f n) / Real.log (n : ℝ))
      atTop (𝓝 (1 - a)) := by
    have h : Tendsto (fun n : ℕ => 1 -
        Real.log (stateCount (floorLogEnergy countingConstant a n) : ℝ) /
          Real.log (n : ℝ)) atTop (𝓝 (1 - a)) :=
      tendsto_const_nhds.sub (floorLogEnergy_stateCount_exponent a ha)
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hln : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hn)).ne'
    have hcount : (0 : ℝ) < stateCount (floorLogEnergy countingConstant a n) := by
      exact_mod_cast stateCount_pos (floorLogEnergy countingConstant a n)
    dsimp only [f]
    rw [Real.log_div hnpos.ne' hcount.ne']
    field_simp [hln]
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < f n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact div_pos (by exact_mod_cast hn)
      (by exact_mod_cast stateCount_pos (floorLogEnergy countingConstant a n))
  exact ceil_log_exponent f (1 - a)
    (tendsto_atTop_of_log_exponent f (1 - a) (by linarith) hpos hscale) hscale

theorem log_energy_overhead_exponent (energy : ℕ → ℕ) (K : ℝ) (hK : 0 < K)
    (htop : Tendsto energy atTop atTop)
    (hscale : Tendsto (fun n : ℕ => (energy n : ℝ) / Real.log (n : ℝ) ^ 2)
      atTop (𝓝 K)) :
    Tendsto (fun n : ℕ => Real.log (((energy n + 1 : ℕ) : ℝ) ^ 3) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ 2) atTop atTop := by
    simpa only [pow_two] using hlog.atTop_mul_atTop₀ hlog
  have hone : Tendsto (fun n : ℕ => 1 / Real.log (n : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsq
  have hscale' : Tendsto (fun n : ℕ =>
      ((energy n + 1 : ℕ) : ℝ) / Real.log (n : ℝ) ^ 2) atTop (𝓝 K) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_div, add_zero] using hscale.add hone
  have htop' : Tendsto (fun n : ℕ => energy n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ _) htop
  have h := (log_energy_ratio_tendsto_zero _ K hK htop' hscale').const_mul 3
  simpa only [Real.log_pow, Nat.cast_ofNat, mul_div_assoc, mul_zero] using h

theorem sumLogEnergy_overhead_exponent (b a : ℝ) (hb : 0 < b) (ha : 0 < a) :
    Tendsto (fun n : ℕ => Real.log
      (((ceilLogEnergy countingConstant b n + floorLogEnergy countingConstant a n + 1 : ℕ) : ℝ) ^ 3) /
        Real.log (n : ℝ)) atTop (𝓝 0) := by
  obtain ⟨htop, hscale⟩ := sumLogEnergy_scale b a hb ha
  exact log_energy_overhead_exponent _ _
    (add_pos (sq_pos_of_pos (div_pos hb countingConstant_pos))
      (sq_pos_of_pos (div_pos ha countingConstant_pos))) htop hscale

theorem eventually_le_rpow_of_log_limit (f : ℕ → ℕ) (L : ℝ)
    (hf : ∀ᶠ n : ℕ in atTop, f n ≠ 0)
    (hlim : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 L))
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (n : ℝ) ^ (L + eps) := by
  filter_upwards [hf, hlim.eventually_lt_const (by linarith : L < L + eps),
    eventually_gt_atTop (1 : ℕ)] with n hfn hlt hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hfpos : (0 : ℝ) < f n := by exact_mod_cast Nat.pos_of_ne_zero hfn
  apply (Real.log_le_log_iff hfpos (Real.rpow_pos_of_pos hnpos (L + eps))).mp
  rw [Real.log_rpow hnpos]
  exact ((div_lt_iff₀ hlog).mp hlt).le

theorem log_nat_product_limit (f g : ℕ → ℕ) (L M : ℝ)
    (hf : ∀ᶠ n : ℕ in atTop, f n ≠ 0) (hg : ∀ᶠ n : ℕ in atTop, g n ≠ 0)
    (hL : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 L))
    (hM : Tendsto (fun n : ℕ => Real.log (g n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 M)) :
    Tendsto (fun n : ℕ => Real.log ((f n * g n : ℕ) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (L + M)) := by
  refine (hL.add hM).congr' ?_
  filter_upwards [hf, hg] with n hfn hgn
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hfn) (by exact_mod_cast hgn), add_div]

theorem eventually_product_le_rpow_of_log_limits (f g : ℕ → ℕ) (L M : ℝ)
    (hf : ∀ᶠ n : ℕ in atTop, f n ≠ 0) (hg : ∀ᶠ n : ℕ in atTop, g n ≠ 0)
    (hL : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 L))
    (hM : Tendsto (fun n : ℕ => Real.log (g n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 M))
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ((f n * g n : ℕ) : ℝ) ≤ (n : ℝ) ^ (L + M + eps) := by
  apply eventually_le_rpow_of_log_limit (fun n => f n * g n) (L + M) _
    (log_nat_product_limit f g L M hf hg hL hM) eps heps
  exact hf.and hg |>.mono fun _ h => Nat.mul_ne_zero h.1 h.2

theorem eventually_absorb_log_overhead (overhead cost : ℕ → ℕ) (L : ℝ)
    (hoverhead : Tendsto (fun n : ℕ => Real.log (overhead n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 0))
    (hpos : ∀ᶠ n : ℕ in atTop, overhead n ≠ 0)
    (hcost : ∀ eps : ℝ, 0 < eps →
      ∀ᶠ n : ℕ in atTop, (cost n : ℝ) ≤ (n : ℝ) ^ (L + eps))
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ((overhead n * cost n : ℕ) : ℝ) ≤ (n : ℝ) ^ (L + eps) := by
  filter_upwards [eventually_le_rpow_of_log_limit overhead 0 hpos hoverhead (eps / 2) (by linarith),
    hcost (eps / 2) (by linarith), eventually_gt_atTop (0 : ℕ)] with n hO hC hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Nat.cast_mul]
  calc
    (overhead n : ℝ) * cost n ≤ (n : ℝ) ^ (0 + eps / 2) * (n : ℝ) ^ (L + eps / 2) :=
      mul_le_mul hO hC (Nat.cast_nonneg _) (Real.rpow_pos_of_pos hnpos _).le
    _ = (n : ℝ) ^ (L + eps) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring

theorem natLog_add_one_scale (q : ℕ) (hq : 2 ≤ q) :
    Tendsto (fun n : ℕ => ((Nat.log q n + 1 : ℕ) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (1 / Real.log (q : ℝ))) := by
  have hqreal : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqreal
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun n : ℕ => Real.logb (q : ℝ) n) atTop atTop :=
    (Real.tendsto_logb_atTop hqreal).comp tendsto_natCast_atTop_atTop
  have hfloor := (tendsto_nat_floor_div_atTop.comp hbase).mul_const (1 / Real.log (q : ℝ))
  simp only [one_mul] at hfloor
  have hratio : Tendsto (fun n : ℕ => (Nat.log q n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (1 / Real.log (q : ℝ))) := by
    refine hfloor.congr' ?_
    filter_upwards [hlog.eventually_gt_atTop 0] with n hn
    simp only [Function.comp_apply]
    rw [Real.natFloor_logb_natCast]
    simp only [Real.logb]
    field_simp [hlogq.ne', hn.ne']
  have hone : Tendsto (fun n : ℕ => 1 / Real.log (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  simpa only [Nat.cast_add, Nat.cast_one, add_div, add_zero] using hratio.add hone

theorem natLog_overhead_exponent (q : ℕ) (hq : 2 ≤ q) :
    Tendsto (fun n : ℕ => Real.log ((Nat.log q n + 1 : ℕ) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogq : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hK : 0 < 1 / Real.log (q : ℝ) := one_div_pos.mpr hlogq
  have hnorm := ((natLog_add_one_scale q hq).log hK.ne').div_atTop hlog
  have hloglog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have h := hnorm.add hloglog
  simp only [zero_add] at h
  refine h.congr' ?_
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  have hpositive : (0 : ℝ) < (Nat.log q n + 1 : ℕ) := by positivity
  simp only [Function.comp_apply, id_eq]
  rw [Real.log_div hpositive.ne' hn.ne']
  ring

theorem natLog_linear_overhead_exponent (q K : ℕ) (hq : 2 ≤ q) :
    Tendsto (fun n : ℕ => Real.log ((K * (Nat.log q n + 1) + 1 : ℕ) : ℝ) /
      Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun n : ℕ => Real.log ((K + 1 : ℕ) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  have hupper := hconst.add (natLog_overhead_exponent q hq)
  simp only [zero_add] at hupper
  apply squeeze_zero'
    (Eventually.of_forall fun n => div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))
    _ hupper
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  have hnat : K * (Nat.log q n + 1) + 1 ≤ (K + 1) * (Nat.log q n + 1) := by
    calc
      K * (Nat.log q n + 1) + 1 ≤ K * (Nat.log q n + 1) + (Nat.log q n + 1) := by omega
      _ = (K + 1) * (Nat.log q n + 1) := by ring
  have hcast : ((K * (Nat.log q n + 1) + 1 : ℕ) : ℝ) ≤
      (((K + 1) * (Nat.log q n + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hle := Real.log_le_log (by positivity : (0 : ℝ) < (K * (Nat.log q n + 1) + 1 : ℕ)) hcast
  have hdiv := div_le_div_of_nonneg_right hle hn.le
  rw [Nat.cast_mul, Real.log_mul (by positivity : ((K + 1 : ℕ) : ℝ) ≠ 0)
    (by positivity : ((Nat.log q n + 1 : ℕ) : ℝ) ≠ 0), add_div] at hdiv
  exact hdiv

theorem eventually_recursion_cost_le_rpow (q r : ℕ) (hq : 2 ≤ q) (L : ℝ)
    (hr : (r : ℝ) < (q : ℝ) ^ L) :
    ∀ᶠ n : ℕ in atTop,
      (((6 * (Nat.log q n + 1) * r + 1) * r ^ (Nat.log q n + 1) : ℕ) : ℝ) ≤
        (n : ℝ) ^ L := by
  by_cases hrzero : r = 0
  · exact Eventually.of_forall fun n => by
      simpa only [hrzero, zero_pow (by omega : Nat.log q n + 1 ≠ 0), mul_zero, Nat.cast_zero]
        using Real.rpow_nonneg (Nat.cast_nonneg n) L
  have hrpos : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hrzero
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlogq : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  let power : ℕ → ℕ := fun n => r ^ (Nat.log q n + 1)
  let overhead : ℕ → ℕ := fun n => 6 * (Nat.log q n + 1) * r + 1
  have hpower : Tendsto (fun n : ℕ => Real.log (power n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (Real.log (r : ℝ) / Real.log (q : ℝ))) := by
    have h := (natLog_add_one_scale q hq).mul_const (Real.log (r : ℝ))
    simpa only [power, Nat.cast_pow, Real.log_pow, div_mul_eq_mul_div, one_mul] using h
  have hoverhead : Tendsto (fun n : ℕ => Real.log (overhead n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [overhead, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      natLog_linear_overhead_exponent q (6 * r) hq
  have hnonzeroPower : ∀ᶠ n : ℕ in atTop, power n ≠ 0 :=
    Eventually.of_forall fun _ => pow_ne_zero _ hrzero
  have hnonzeroOverhead : ∀ᶠ n : ℕ in atTop, overhead n ≠ 0 :=
    Eventually.of_forall fun n => by dsimp [overhead]; omega
  have hlim := log_nat_product_limit overhead power 0
    (Real.log (r : ℝ) / Real.log (q : ℝ)) hnonzeroOverhead hnonzeroPower hoverhead hpower
  simp only [zero_add] at hlim
  have hstrict : Real.log (r : ℝ) / Real.log (q : ℝ) < L := by
    have h := Real.log_lt_log hrpos hr
    rw [Real.log_rpow hqpos] at h
    exact (div_lt_iff₀ hlogq).mpr h
  have hbound := eventually_le_rpow_of_log_limit (fun n => overhead n * power n)
    (Real.log (r : ℝ) / Real.log (q : ℝ))
    (hnonzeroOverhead.and hnonzeroPower |>.mono fun _ h => Nat.mul_ne_zero h.1 h.2)
    hlim (L - Real.log (r : ℝ) / Real.log (q : ℝ)) (sub_pos.mpr hstrict)
  have hid : Real.log (r : ℝ) / Real.log (q : ℝ) +
      (L - Real.log (r : ℝ) / Real.log (q : ℝ)) = L := by ring
  simpa only [hid] using hbound

end Lemmata.FockCircuits
