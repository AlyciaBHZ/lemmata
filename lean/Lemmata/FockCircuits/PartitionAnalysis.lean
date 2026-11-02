module

public import Lemmata.FockCircuits.Partition
public import Lemmata.FockCircuits.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SumIntegralComparisons

@[expose] public section

set_option autoImplicit false

open scoped BigOperators Topology

namespace Lemmata.FockCircuits

open Filter MeasureTheory Set

noncomputable def fermionLog (x : ℝ) : ℝ := Real.log (1 + Real.exp (-x))

theorem fermionLog_pos (x : ℝ) : 0 < fermionLog x := by
  apply Real.log_pos
  linarith [Real.exp_pos (-x)]

theorem fermionLog_nonneg (x : ℝ) : 0 ≤ fermionLog x := (fermionLog_pos x).le

theorem fermionLog_le_exp (x : ℝ) : fermionLog x ≤ Real.exp (-x) := by
  have h := Real.log_le_sub_one_of_pos
    (by linarith [Real.exp_pos (-x)] : 0 < 1 + Real.exp (-x))
  dsimp [fermionLog]
  linarith

theorem fermionLog_antitone : Antitone fermionLog := by
  intro x y hxy
  apply Real.log_le_log (by linarith [Real.exp_pos (-y)])
  linarith [Real.exp_le_exp.mpr (neg_le_neg hxy)]

theorem continuous_fermionLog : Continuous fermionLog := by
  unfold fermionLog
  exact (continuous_const.add (Real.continuous_exp.comp continuous_neg)).log
    (fun x => by
      simp only [Pi.add_apply, Function.comp_apply]
      linarith [Real.exp_pos (-x)])

private theorem summable_odd_exp (t : ℝ) (ht : 0 < t) :
    Summable fun i : ℕ => Real.exp (-t * (2 * i + 1 : ℕ)) := by
  have hg := summable_geometric_of_lt_one (Real.exp_nonneg (-2 * t))
    (Real.exp_lt_one_iff.mpr (by linarith : -2 * t < 0))
  apply (hg.mul_left (Real.exp (-t))).congr
  intro i
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

private theorem finite_exp_product (t : ℝ) (I : Finset ℕ) :
    (∏ i ∈ I, Real.exp (-t * (2 * i + 1 : ℕ))) =
      Real.exp (-t * doubledEnergy I) := by
  rw [← Real.exp_sum]
  congr 1
  simp [doubledEnergy, Finset.mul_sum]

theorem summable_partition_states (t : ℝ) (ht : 0 < t) :
    Summable fun I : Finset ℕ => Real.exp (-t * doubledEnergy I) := by
  apply (summable_finsetProd_of_summable_nonneg
    (fun i : ℕ => Real.exp_nonneg (-t * (2 * i + 1 : ℕ)))
    (summable_odd_exp t ht)).congr
  exact finite_exp_product t

private theorem partition_energy_fiber_sum (k : ℕ) (t : ℝ) :
    (∑' I : doubledEnergy ⁻¹' {k}, Real.exp (-t * doubledEnergy I.val)) =
      (partitionDimension k : ℝ) * Real.exp (-t * (k : ℝ)) := by
  have hset : doubledEnergy ⁻¹' {k} = (partitionSlice k : Set (Finset ℕ)) := by
    ext I
    simp only [mem_preimage, mem_singleton_iff, Finset.mem_coe, mem_partitionSlice]
  rw [hset]
  calc
    (∑' I : (partitionSlice k : Set (Finset ℕ)), Real.exp (-t * doubledEnergy I.val)) =
        ∑ I ∈ partitionSlice k, Real.exp (-t * doubledEnergy I) :=
      Finset.tsum_subtype' (partitionSlice k)
        (fun I : Finset ℕ => Real.exp (-t * doubledEnergy I))
    _ = ∑ _I ∈ partitionSlice k, Real.exp (-t * (k : ℝ)) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [mem_partitionSlice.mp hI]
    _ = (partitionDimension k : ℝ) * Real.exp (-t * (k : ℝ)) := by
      simp only [Finset.sum_const, nsmul_eq_mul, partitionDimension]

theorem summable_partition_laplace (t : ℝ) (ht : 0 < t) :
    Summable fun k : ℕ => (partitionDimension k : ℝ) * Real.exp (-t * (k : ℝ)) := by
  have h := (summable_partition_states t ht).hasSum.tsum_fiberwise doubledEnergy
  exact (h.congr_fun (fun k => (partition_energy_fiber_sum k t).symm)).summable

theorem log_partition_laplace (t : ℝ) (ht : 0 < t) :
    Real.log (laplaceSeries (fun k => (partitionDimension k : ℝ)) t) =
      ∑' i : ℕ, fermionLog (t * (2 * i + 1 : ℕ)) := by
  have hprod := summable_finsetProd_of_summable_nonneg
    (fun i : ℕ => Real.exp_nonneg (-t * (2 * i + 1 : ℕ))) (summable_odd_exp t ht)
  have hgroup := (summable_partition_states t ht).hasSum.tsum_fiberwise doubledEnergy
  have hgroup' := hgroup.congr_fun (fun k => (partition_energy_fiber_sum k t).symm)
  have heuler : (∏' i : ℕ, (1 + Real.exp (-t * (2 * i + 1 : ℕ)))) =
      ∑' I : Finset ℕ, Real.exp (-t * doubledEnergy I) := by
    rw [tprod_one_add hprod]
    exact tsum_congr (finite_exp_product t)
  have hlogs := Real.summable_log_one_add_of_summable (summable_odd_exp t ht)
  have hlogproduct := Real.rexp_tsum_eq_tprod
    (fun i : ℕ => by linarith [Real.exp_pos (-t * (2 * i + 1 : ℕ))]) hlogs
  have hseries : laplaceSeries (fun k => (partitionDimension k : ℝ)) t =
      Real.exp (∑' i : ℕ, Real.log (1 + Real.exp (-t * (2 * i + 1 : ℕ)))) := by
    exact hgroup'.tsum_eq.trans (heuler.symm.trans hlogproduct.symm)
  rw [hseries, Real.log_exp]
  apply tsum_congr
  intro i
  simp only [fermionLog, neg_mul]

theorem integrableOn_fermionLog : IntegrableOn fermionLog (Ioi 0) := by
  apply (integrableOn_exp_neg_Ioi 0).mono'
    continuous_fermionLog.aestronglyMeasurable.restrict
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (fermionLog_nonneg x)]
    exact fermionLog_le_exp x

noncomputable def fermionIntegral : ℝ := ∫ x in Ioi (0 : ℝ), fermionLog x

theorem fermionIntegral_pos : 0 < fermionIntegral := by
  apply (integral_pos_iff_support_of_nonneg fermionLog_nonneg integrableOn_fermionLog).mpr
  have hs : Function.support fermionLog = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    change fermionLog x ≠ 0
    exact (fermionLog_pos x).ne'
  rw [hs]
  simp

theorem fermionLog_sum_bounds (t : ℝ) (ht : 0 < t) :
    fermionIntegral / (2 * t) - fermionLog 0 ≤
        ∑' i : ℕ, fermionLog (t * (2 * i + 1 : ℕ)) ∧
      (∑' i : ℕ, fermionLog (t * (2 * i + 1 : ℕ))) ≤
        fermionIntegral / (2 * t) + fermionLog 0 := by
  let f : ℝ → ℝ := fun x => fermionLog ((2 * t) * x)
  have h2t : 0 < 2 * t := by positivity
  have hanti : AntitoneOn f (Ici 0) := by
    intro x hx y hy hxy
    exact fermionLog_antitone (mul_le_mul_of_nonneg_left hxy h2t.le)
  have hint : IntegrableOn f (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff fermionLog 0 h2t).mpr
    simpa only [mul_zero] using integrableOn_fermionLog
  have hnonneg : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ f x := fun x _ => fermionLog_nonneg _
  have hsum : Summable fun i : ℕ => f (i : ℝ) :=
    hanti.summable_of_integrableOn_Ioi_zero hint hnonneg
  have hsum_shift : Summable fun i : ℕ => f ((i + 1 : ℕ) : ℝ) :=
    (summable_nat_add_iff 1).mpr hsum
  have hsum_odd : Summable fun i : ℕ => fermionLog (t * (2 * i + 1 : ℕ)) := by
    simpa only [fermionLog, neg_mul] using
      Real.summable_log_one_add_of_summable (summable_odd_exp t ht)
  have hInt : (∫ x in Ioi (0 : ℝ), f x) = fermionIntegral / (2 * t) := by
    simpa only [f, mul_zero, zero_mul, smul_eq_mul, fermionIntegral, div_eq_mul_inv, mul_comm]
      using integral_comp_mul_left_Ioi fermionLog 0 h2t
  have hupper := hanti.tsum_le_integral hint hnonneg
  have hlower := hanti.integral_le_tsum hsum hnonneg
  rw [hInt] at hupper hlower
  have hOddUpper : (∑' i : ℕ, fermionLog (t * (2 * i + 1 : ℕ))) ≤
      ∑' i : ℕ, f (i : ℝ) := by
    apply hsum_odd.tsum_le_tsum _ hsum
    intro i
    apply fermionLog_antitone
    push_cast
    nlinarith
  have hOddLower : (∑' i : ℕ, f ((i + 1 : ℕ) : ℝ)) ≤
      ∑' i : ℕ, fermionLog (t * (2 * i + 1 : ℕ)) := by
    apply hsum_shift.tsum_le_tsum _ hsum_odd
    intro i
    apply fermionLog_antitone
    push_cast
    nlinarith
  have hshift := hsum.tsum_eq_zero_add
  have hf0 : f 0 = fermionLog 0 := by simp only [f, mul_zero]
  rw [hf0] at hupper
  simp only [Nat.cast_zero, hf0] at hshift
  constructor <;> linarith

theorem partition_laplace_log_error (t : ℝ) (ht : 0 < t) :
    |t * Real.log (laplaceSeries (fun k => (partitionDimension k : ℝ)) t) -
      fermionIntegral / 2| ≤ t * Real.log 2 := by
  obtain ⟨hlower, hupper⟩ := fermionLog_sum_bounds t ht
  have hlog : fermionLog 0 = Real.log 2 := by norm_num [fermionLog]
  rw [hlog] at hlower hupper
  have hlo := mul_le_mul_of_nonneg_left hlower ht.le
  have hhi := mul_le_mul_of_nonneg_left hupper ht.le
  have hInt : t * (fermionIntegral / (2 * t)) = fermionIntegral / 2 := by
    field_simp [ht.ne']
  rw [mul_sub, hInt] at hlo
  rw [mul_add, hInt] at hhi
  rw [log_partition_laplace t ht]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem partition_laplace_log_tendsto :
    Tendsto (fun t : ℝ =>
      t * Real.log (laplaceSeries (fun k => (partitionDimension k : ℝ)) t))
      (𝓝[>] 0) (𝓝 (fermionIntegral / 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hzero : Tendsto (fun t : ℝ => t * Real.log 2) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul] using
      (show Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) from
        nhdsWithin_le_nhds).mul_const (Real.log 2)
  apply squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) _ hzero
  filter_upwards [self_mem_nhdsWithin] with t ht
  simpa only [Real.norm_eq_abs] using partition_laplace_log_error t ht

theorem partition_cumulative_log_tendsto :
    Tendsto (fun H : ℕ =>
      Real.log (cumulativeWeight (fun k => (partitionDimension k : ℝ)) H) /
        Real.sqrt (H : ℝ)) atTop (𝓝 (2 * Real.sqrt (fermionIntegral / 2))) := by
  have hI : 0 < fermionIntegral / 2 := div_pos fermionIntegral_pos (by norm_num)
  apply log_cumulativeWeight_tendsto (fun k => (partitionDimension k : ℝ))
    (Real.sqrt (fermionIntegral / 2)) (fun k => Nat.cast_nonneg _) (by simp)
    (Real.sqrt_pos.mpr hI) summable_partition_laplace
  simpa only [Real.sq_sqrt hI.le] using partition_laplace_log_tendsto

theorem partition_cumulativeWeight_fullCutoff (H : ℕ) :
    cumulativeWeight (fun k => (partitionDimension k : ℝ)) (2 * H) =
      ((fullCutoff H).card : ℝ) := by
  simp only [cumulativeWeight, card_fullCutoff_eq_sum, Nat.cast_sum]

theorem fullCutoff_log_tendsto :
    Tendsto (fun H : ℕ =>
      Real.log ((fullCutoff H).card : ℝ) / Real.sqrt (H : ℝ))
      atTop (𝓝 (2 * Real.sqrt fermionIntegral)) := by
  have h2 : Tendsto (fun H : ℕ => 2 * H) atTop atTop :=
    tendsto_atTop_mono (fun H : ℕ => by simp only [id_eq]; omega) tendsto_id
  have h := (partition_cumulative_log_tendsto.comp h2).mul_const (Real.sqrt 2)
  have hI2 : 0 ≤ fermionIntegral / 2 :=
    div_nonneg fermionIntegral_pos.le (by norm_num)
  have hconstant : (2 * Real.sqrt (fermionIntegral / 2)) * Real.sqrt 2 =
      2 * Real.sqrt fermionIntegral := by
    rw [mul_assoc, ← Real.sqrt_mul hI2]
    congr 1
    congr 1
    ring
  rw [hconstant] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with H hH
  have hroot : Real.sqrt (H : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hH)).ne'
  have hroot2 : Real.sqrt (2 : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by norm_num)).ne'
  simp only [Function.comp_apply]
  rw [partition_cumulativeWeight_fullCutoff]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [hroot, hroot2]

end Lemmata.FockCircuits
