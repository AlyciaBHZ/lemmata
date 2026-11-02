module

public import Lemmata.FockCircuits.Laplace
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic.FieldSimp

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits

open Filter
open scoped Topology

theorem cumulativeWeight_pos (q : ℕ → ℝ) (H : ℕ)
    (hq : ∀ e, 0 ≤ q e) (hq0 : 0 < q 0) :
    0 < cumulativeWeight q H := by
  apply hq0.trans_le
  exact Finset.single_le_sum (fun e _ => hq e) (by simp)

theorem laplaceSeries_pos (q : ℕ → ℝ) (t : ℝ)
    (hq : ∀ e, 0 ≤ q e) (hq0 : 0 < q 0)
    (hsum : Summable fun e : ℕ => q e * Real.exp (-t * (e : ℝ))) :
    0 < laplaceSeries q t := by
  have h := hsum.le_tsum 0 fun e _ =>
    mul_nonneg (hq e) (Real.exp_nonneg _)
  apply hq0.trans_le
  simpa only [laplaceSeries, Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
    using h

theorem cumulativeWeight_le_exp_mul_laplaceSeries
    (q : ℕ → ℝ) (H : ℕ) (t : ℝ)
    (hq : ∀ e, 0 ≤ q e) (ht : 0 ≤ t)
    (hsum : Summable fun e : ℕ => q e * Real.exp (-t * (e : ℝ))) :
    cumulativeWeight q H ≤ Real.exp (t * (H : ℝ)) * laplaceSeries q t := by
  have hpoint (e : ℕ) (he : e ∈ Finset.range (H + 1)) :
      q e ≤ Real.exp (t * (H : ℝ)) * (q e * Real.exp (-t * (e : ℝ))) := by
    have heH : (e : ℝ) ≤ H := by
      exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp he)
    have heq : Real.exp (t * (H : ℝ)) * (q e * Real.exp (-t * (e : ℝ))) =
        q e * Real.exp (t * ((H : ℝ) - e)) := by
      rw [show t * ((H : ℝ) - e) = t * (H : ℝ) + -t * (e : ℝ) by ring,
        Real.exp_add]
      ring
    rw [heq]
    have hexp : 1 ≤ Real.exp (t * ((H : ℝ) - e)) :=
      Real.one_le_exp_iff.mpr (mul_nonneg ht (sub_nonneg.mpr heH))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp (hq e)
  calc
    cumulativeWeight q H ≤ (Finset.range (H + 1)).sum
        (fun e => Real.exp (t * (H : ℝ)) * (q e * Real.exp (-t * (e : ℝ)))) :=
      Finset.sum_le_sum hpoint
    _ = Real.exp (t * (H : ℝ)) * (Finset.range (H + 1)).sum
        (fun e => q e * Real.exp (-t * (e : ℝ))) := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.exp (t * (H : ℝ)) * laplaceSeries q t := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact hsum.sum_le_tsum _ fun e _ => mul_nonneg (hq e) (Real.exp_nonneg _)

theorem log_cumulativeWeight_le (q : ℕ → ℝ) (H : ℕ) (t : ℝ)
    (hq : ∀ e, 0 ≤ q e) (hq0 : 0 < q 0) (ht : 0 ≤ t)
    (hsum : Summable fun e : ℕ => q e * Real.exp (-t * (e : ℝ))) :
    Real.log (cumulativeWeight q H) ≤ t * (H : ℝ) + Real.log (laplaceSeries q t) := by
  have h := Real.log_le_log (cumulativeWeight_pos q H hq hq0)
    (cumulativeWeight_le_exp_mul_laplaceSeries q H t hq ht hsum)
  rwa [Real.log_mul (Real.exp_ne_zero _) (laplaceSeries_pos q t hq hq0 hsum).ne',
    Real.log_exp] at h

theorem exp_difference_tendsto_zero {α : Type*} {l : Filter α}
    {scale f g : α → ℝ} {A B : ℝ}
    (hscale : Tendsto scale l atTop)
    (hf : Tendsto (fun n => f n / scale n) l (𝓝 A))
    (hg : Tendsto (fun n => g n / scale n) l (𝓝 B)) (hBA : B < A) :
    Tendsto (fun n => Real.exp (g n - f n)) l (𝓝 0) := by
  have hdiff := (hg.sub hf).neg_mul_atTop (sub_neg.mpr hBA) hscale
  have hd : Tendsto (fun n => g n - f n) l atBot := by
    refine hdiff.congr' ?_
    filter_upwards [hscale.eventually_gt_atTop 0] with n hn
    field_simp [hn.ne']
  exact Real.tendsto_exp_atBot.comp hd

theorem eventually_half_exp_le_of_three_evaluations
    {α : Type*} {l : Filter α} {scale f g h D : α → ℝ} {A B C : ℝ}
    (hscale : Tendsto scale l atTop)
    (hf : Tendsto (fun n => f n / scale n) l (𝓝 A))
    (hg : Tendsto (fun n => g n / scale n) l (𝓝 B))
    (hh : Tendsto (fun n => h n / scale n) l (𝓝 C))
    (hBA : B < A) (hCA : C < A)
    (hD : ∀ᶠ n in l, Real.exp (f n) - Real.exp (g n) - Real.exp (h n) ≤ D n) :
    ∀ᶠ n in l, Real.exp (f n) / 2 ≤ D n := by
  have hg0 := exp_difference_tendsto_zero hscale hf hg hBA
  have hh0 := exp_difference_tendsto_zero hscale hf hh hCA
  have hsmall : ∀ᶠ n in l,
      Real.exp (g n - f n) + Real.exp (h n - f n) < 1 / 2 := by
    exact (hg0.add hh0).eventually_lt_const (by norm_num)
  filter_upwards [hD, hsmall] with n hn hsmall
  have hprod (x : ℝ) : Real.exp x = Real.exp (f n) * Real.exp (x - f n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmul := mul_lt_mul_of_pos_left hsmall (Real.exp_pos (f n))
  rw [mul_add, ← hprod (g n), ← hprod (h n)] at hmul
  linarith

theorem eventually_log_lower_of_three_evaluations
    {α : Type*} {l : Filter α} {scale f g h D : α → ℝ} {A B C : ℝ}
    (hscale : Tendsto scale l atTop)
    (hf : Tendsto (fun n => f n / scale n) l (𝓝 A))
    (hg : Tendsto (fun n => g n / scale n) l (𝓝 B))
    (hh : Tendsto (fun n => h n / scale n) l (𝓝 C))
    (hBA : B < A) (hCA : C < A)
    (hD : ∀ᶠ n in l, Real.exp (f n) - Real.exp (g n) - Real.exp (h n) ≤ D n)
    {a : ℝ} (ha : a < A) :
    ∀ᶠ n in l, a < Real.log (D n) / scale n := by
  have hhalf := eventually_half_exp_le_of_three_evaluations hscale hf hg hh hBA hCA hD
  have hlogscale : Tendsto (fun n => Real.log 2 / scale n) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop hscale
  have hnorm : Tendsto (fun n => (f n - Real.log 2) / scale n) l (𝓝 A) := by
    simpa only [sub_div, sub_zero] using hf.sub hlogscale
  filter_upwards [hhalf, hnorm.eventually_const_lt ha, hscale.eventually_gt_atTop 0]
    with n hn hnorm hnpos
  have hp : 0 < Real.exp (f n) / 2 := div_pos (Real.exp_pos _) (by norm_num)
  have hlog := Real.log_le_log hp hn
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hlog
  exact hnorm.trans_le (div_le_div_of_nonneg_right hlog hnpos.le)

theorem scaled_laplace_log_tendsto {α : Type*} {l : Filter α}
    (q : ℕ → ℝ) {scale : α → ℝ} {I c : ℝ}
    (hscale : Tendsto scale l atTop) (hc : 0 < c)
    (hZ : Tendsto (fun t : ℝ => t * Real.log (laplaceSeries q t))
      (𝓝[>] 0) (𝓝 I)) :
    Tendsto (fun n => Real.log (laplaceSeries q (c / scale n)) / scale n)
      l (𝓝 (I / c)) := by
  have ht : Tendsto (fun n => c / scale n) l (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_nhds.div_atTop hscale, ?_⟩
    filter_upwards [hscale.eventually_gt_atTop 0] with n hn
    exact div_pos hc hn
  have h := (hZ.comp ht).div_const c
  refine h.congr' ?_
  filter_upwards [hscale.eventually_gt_atTop 0] with n hn
  simp only [Function.comp_apply]
  field_simp [hc.ne', hn.ne']

theorem exp_laplaceSeries_three_evaluations
    (q : ℕ → ℝ) (H : ℕ) (s t u L : ℝ)
    (hq : ∀ e, 0 ≤ q e) (hq0 : 0 < q 0) (ht : 0 ≤ t)
    (hst : s ≤ t) (htu : t ≤ u)
    (hsum_s : Summable fun e : ℕ => q e * Real.exp (-s * (e : ℝ)))
    (hsum_t : Summable fun e : ℕ => q e * Real.exp (-t * (e : ℝ)))
    (hsum_u : Summable fun e : ℕ => q e * Real.exp (-u * (e : ℝ))) :
    Real.exp (t * L + Real.log (laplaceSeries q t)) -
        Real.exp (u * L + Real.log (laplaceSeries q u)) -
        Real.exp (t * L - (t - s) * (H : ℝ) + Real.log (laplaceSeries q s)) ≤
      cumulativeWeight q H := by
  have h := laplaceSeries_three_evaluations q H s t u L hq ht hst htu
    hsum_s hsum_t hsum_u
  have hs := laplaceSeries_pos q s hq hq0 hsum_s
  have htpos := laplaceSeries_pos q t hq hq0 hsum_t
  have hu := laplaceSeries_pos q u hq hq0 hsum_u
  calc
    _ = Real.exp (t * L) *
        (laplaceSeries q t - Real.exp ((u - t) * L) * laplaceSeries q u -
          Real.exp (-(t - s) * (H : ℝ)) * laplaceSeries q s) := by
      rw [Real.exp_add, Real.exp_log htpos,
        Real.exp_add, Real.exp_log hu,
        Real.exp_add, Real.exp_log hs]
      rw [show u * L = t * L + (u - t) * L by ring,
        show t * L - (t - s) * (H : ℝ) = t * L + -(t - s) * (H : ℝ) by ring,
        Real.exp_add, Real.exp_add]
      ring
    _ ≤ Real.exp (t * L) * (Real.exp (-t * L) * cumulativeWeight q H) :=
      mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
    _ = cumulativeWeight q H := by
      rw [← mul_assoc, ← Real.exp_add]
      simp only [show t * L + -t * L = 0 by ring, Real.exp_zero, one_mul]

private theorem normalized_energy_term (H : ℕ) (hH : 0 < H) (a : ℝ) :
    ((a / Real.sqrt (H : ℝ)) * (H : ℝ)) / Real.sqrt (H : ℝ) = a := by
  have hHR : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  calc
    _ = a * (H : ℝ) /
        (Real.sqrt (H : ℝ) * Real.sqrt (H : ℝ)) := by ring
    _ = a := by rw [Real.mul_self_sqrt (Nat.cast_nonneg H)]; field_simp [hHR]

private theorem energy_laplace_log_tendsto
    (q : ℕ → ℝ) (a b I : ℝ) (hb : 0 < b)
    (hZ : Tendsto (fun t : ℝ => t * Real.log (laplaceSeries q t))
      (𝓝[>] 0) (𝓝 I)) :
    Tendsto (fun H : ℕ =>
      ((a / Real.sqrt (H : ℝ)) * (H : ℝ) +
        Real.log (laplaceSeries q (b / Real.sqrt (H : ℝ)))) / Real.sqrt (H : ℝ))
      atTop (𝓝 (a + I / b)) := by
  have hscale : Tendsto (fun H : ℕ => Real.sqrt (H : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hterm : Tendsto (fun H : ℕ =>
      ((a / Real.sqrt (H : ℝ)) * (H : ℝ)) / Real.sqrt (H : ℝ)) atTop (𝓝 a) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with H hH
    exact (normalized_energy_term H hH a).symm
  simpa only [add_div] using hterm.add (scaled_laplace_log_tendsto q hscale hb hZ)

theorem eventually_log_cumulativeWeight_lower
    (q : ℕ → ℝ) (c r : ℝ)
    (hq : ∀ e, 0 ≤ q e) (hq0 : 0 < q 0) (hc : 0 < c) (hr : 1 < r)
    (hsum : ∀ t : ℝ, 0 < t →
      Summable fun e : ℕ => q e * Real.exp (-t * (e : ℝ)))
    (hZ : Tendsto (fun t : ℝ => t * Real.log (laplaceSeries q t))
      (𝓝[>] 0) (𝓝 (c ^ 2)))
    {a : ℝ} (ha : a < c / r ^ 3 + c / r) :
    ∀ᶠ H : ℕ in atTop,
      a < Real.log (cumulativeWeight q H) / Real.sqrt (H : ℝ) := by
  let f : ℕ → ℝ := fun H =>
    ((c / r ^ 3) / Real.sqrt (H : ℝ)) * (H : ℝ) +
      Real.log (laplaceSeries q ((r * c) / Real.sqrt (H : ℝ)))
  let g : ℕ → ℝ := fun H =>
    ((c / r ^ 2) / Real.sqrt (H : ℝ)) * (H : ℝ) +
      Real.log (laplaceSeries q ((r ^ 2 * c) / Real.sqrt (H : ℝ)))
  let h : ℕ → ℝ := fun H =>
    ((c / r ^ 3 - r * c + c) / Real.sqrt (H : ℝ)) * (H : ℝ) +
      Real.log (laplaceSeries q (c / Real.sqrt (H : ℝ)))
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hrc : 0 < r * c := mul_pos hrpos hc
  have hr2c : 0 < r ^ 2 * c := mul_pos (pow_pos hrpos 2) hc
  have hf : Tendsto (fun H => f H / Real.sqrt (H : ℝ))
      atTop (𝓝 (c / r ^ 3 + c / r)) := by
    have hi : c ^ 2 / (r * c) = c / r := by field_simp [hrpos.ne', hc.ne']
    simpa only [f, hi] using energy_laplace_log_tendsto q (c / r ^ 3) (r * c)
      (c ^ 2) hrc hZ
  have hg : Tendsto (fun H => g H / Real.sqrt (H : ℝ))
      atTop (𝓝 (2 * c / r ^ 2)) := by
    have hi : c / r ^ 2 + c ^ 2 / (r ^ 2 * c) = 2 * c / r ^ 2 := by
      field_simp [hrpos.ne', hc.ne']
      ring
    rw [← hi]
    exact energy_laplace_log_tendsto q (c / r ^ 2) (r ^ 2 * c) (c ^ 2) hr2c hZ
  have hh : Tendsto (fun H => h H / Real.sqrt (H : ℝ))
      atTop (𝓝 (c / r ^ 3 + 2 * c - r * c)) := by
    have hi : c / r ^ 3 - r * c + c + c ^ 2 / c =
        c / r ^ 3 + 2 * c - r * c := by
      field_simp [hrpos.ne', hc.ne']
      ring
    rw [← hi]
    exact energy_laplace_log_tendsto q (c / r ^ 3 - r * c + c) c (c ^ 2) hc hZ
  have hgap1 : 2 * c / r ^ 2 < c / r ^ 3 + c / r := by
    have hid : c / r ^ 3 + c / r - 2 * c / r ^ 2 = c * (r - 1) ^ 2 / r ^ 3 := by
      field_simp [hrpos.ne']
      ring
    have hpos : 0 < c * (r - 1) ^ 2 / r ^ 3 :=
      div_pos (mul_pos hc (pow_pos (sub_pos.mpr hr) 2)) (pow_pos hrpos 3)
    linarith
  have hgap2 : c / r ^ 3 + 2 * c - r * c < c / r ^ 3 + c / r := by
    have hid : c / r ^ 3 + c / r - (c / r ^ 3 + 2 * c - r * c) =
        c * (r - 1) ^ 2 / r := by
      field_simp [hrpos.ne']
      ring
    have hpos : 0 < c * (r - 1) ^ 2 / r :=
      div_pos (mul_pos hc (pow_pos (sub_pos.mpr hr) 2)) hrpos
    linarith
  have hD : ∀ᶠ H : ℕ in atTop,
      Real.exp (f H) - Real.exp (g H) - Real.exp (h H) ≤ cumulativeWeight q H := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with H hH
    have hroot : 0 < Real.sqrt (H : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hH)
    let s := c / Real.sqrt (H : ℝ)
    let t := (r * c) / Real.sqrt (H : ℝ)
    let u := (r ^ 2 * c) / Real.sqrt (H : ℝ)
    let L := (H : ℝ) / r ^ 4
    have hspos : 0 < s := div_pos hc hroot
    have htpos : 0 < t := div_pos hrc hroot
    have hupos : 0 < u := div_pos hr2c hroot
    have hst : s ≤ t := div_le_div_of_nonneg_right (by nlinarith) hroot.le
    have htu : t ≤ u := div_le_div_of_nonneg_right (by nlinarith) hroot.le
    have hfEq : f H = t * L + Real.log (laplaceSeries q t) := by
      dsimp [f, t, L]
      congr 1
      field_simp [hrpos.ne', hroot.ne']
    have hgEq : g H = u * L + Real.log (laplaceSeries q u) := by
      dsimp [g, u, L]
      congr 1
      field_simp [hrpos.ne', hroot.ne']
    have hhEq : h H = t * L - (t - s) * (H : ℝ) + Real.log (laplaceSeries q s) := by
      dsimp [h, t, s, L]
      congr 1
      field_simp [hrpos.ne', hroot.ne']
      ring
    rw [hfEq, hgEq, hhEq]
    exact exp_laplaceSeries_three_evaluations q H s t u L hq hq0 htpos.le hst htu
      (hsum s hspos) (hsum t htpos) (hsum u hupos)
  exact eventually_log_lower_of_three_evaluations
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    hf hg hh hgap1 hgap2 hD ha

theorem log_cumulativeWeight_tendsto
    (q : ℕ → ℝ) (c : ℝ)
    (hq : ∀ e, 0 ≤ q e) (hq0 : 0 < q 0) (hc : 0 < c)
    (hsum : ∀ t : ℝ, 0 < t →
      Summable fun e : ℕ => q e * Real.exp (-t * (e : ℝ)))
    (hZ : Tendsto (fun t : ℝ => t * Real.log (laplaceSeries q t))
      (𝓝[>] 0) (𝓝 (c ^ 2))) :
    Tendsto (fun H : ℕ =>
      Real.log (cumulativeWeight q H) / Real.sqrt (H : ℝ)) atTop (𝓝 (2 * c)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hid : Tendsto (fun r : ℝ => r) (𝓝[>] (1 : ℝ)) (𝓝 1) :=
      nhdsWithin_le_nhds
    have hlim : Tendsto (fun r : ℝ => c / r ^ 3 + c / r)
        (𝓝[>] (1 : ℝ)) (𝓝 (2 * c)) := by
      simpa only [Pi.add_apply, Pi.div_apply, Pi.pow_apply, Function.comp_apply,
        one_pow, div_one, two_mul] using
        (tendsto_const_nhds.div (hid.pow 3) (by norm_num)).add
          (tendsto_const_nhds.div hid (by norm_num))
    have hrpos : ∀ᶠ r : ℝ in 𝓝[>] (1 : ℝ), 1 < r := self_mem_nhdsWithin
    obtain ⟨r, hr, har⟩ := (hrpos.and (hlim.eventually_const_lt ha)).exists
    exact eventually_log_cumulativeWeight_lower q c r hq hq0 hc hr hsum hZ har
  · intro b hb
    have hi : c + c ^ 2 / c = 2 * c := by field_simp [hc.ne']; ring
    have hlim := energy_laplace_log_tendsto q c c (c ^ 2) hc hZ
    rw [hi] at hlim
    filter_upwards [hlim.eventually_lt_const hb, eventually_gt_atTop (0 : ℕ)]
      with H hlim hH
    have hroot : 0 < Real.sqrt (H : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hH)
    have ht : 0 < c / Real.sqrt (H : ℝ) := div_pos hc hroot
    have hle := log_cumulativeWeight_le q H (c / Real.sqrt (H : ℝ)) hq hq0 ht.le
      (hsum _ ht)
    exact (div_le_div_of_nonneg_right hle hroot.le).trans_lt hlim

noncomputable def ceilLogEnergy (c b : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (((b / c) * Real.log (n : ℝ)) ^ 2)

noncomputable def floorLogEnergy (c b : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (((b / c) * Real.log (n : ℝ)) ^ 2)

theorem energy_sqrt_ratio_tendsto (energy : ℕ → ℕ) (K : ℝ)
    (h : Tendsto (fun n : ℕ => (energy n : ℝ) / Real.log (n : ℝ) ^ 2)
      atTop (𝓝 K)) :
    Tendsto (fun n : ℕ => Real.sqrt (energy n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (Real.sqrt K)) := by
  have hs := h.sqrt
  refine hs.congr' ?_
  filter_upwards [(Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).eventually_gt_atTop 0]
    with n hn
  simp only [Function.comp_apply] at hn
  rw [Real.sqrt_div (Nat.cast_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos hn]

private theorem rounded_log_energy_scale
    (rounding : ℝ → ℕ)
    (hrtop : Tendsto rounding atTop atTop)
    (hrratio : Tendsto (fun x : ℝ => (rounding x : ℝ) / x) atTop (𝓝 1))
    (c b : ℝ) (hc : 0 < c) (hb : 0 < b) :
    Tendsto (fun n : ℕ => rounding (((b / c) * Real.log (n : ℝ)) ^ 2)) atTop atTop ∧
      Tendsto (fun n : ℕ =>
        (rounding (((b / c) * Real.log (n : ℝ)) ^ 2) : ℝ) / Real.log (n : ℝ) ^ 2)
        atTop (𝓝 ((b / c) ^ 2)) ∧
      Tendsto (fun n : ℕ =>
        Real.sqrt (rounding (((b / c) * Real.log (n : ℝ)) ^ 2) : ℝ) /
          Real.log (n : ℝ)) atTop (𝓝 (b / c)) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbc : 0 < b / c := div_pos hb hc
  have hx : Tendsto (fun n : ℕ => (b / c) * Real.log (n : ℝ)) atTop atTop :=
    hlog.const_mul_atTop hbc
  have harg : Tendsto (fun n : ℕ => ((b / c) * Real.log (n : ℝ)) ^ 2)
      atTop atTop := by
    simpa only [pow_two] using hx.atTop_mul_atTop₀ hx
  have hnorm : Tendsto (fun n : ℕ =>
      (rounding (((b / c) * Real.log (n : ℝ)) ^ 2) : ℝ) / Real.log (n : ℝ) ^ 2)
        atTop (𝓝 ((b / c) ^ 2)) := by
    have hlim := (hrratio.comp harg).mul_const ((b / c) ^ 2)
    simp only [one_mul] at hlim
    refine hlim.congr' ?_
    filter_upwards [hlog.eventually_gt_atTop 0] with n hn
    simp only [Function.comp_apply]
    field_simp [hc.ne', hb.ne', hn.ne']
  refine ⟨hrtop.comp harg, hnorm, ?_⟩
  have hs := energy_sqrt_ratio_tendsto
    (fun n : ℕ => rounding (((b / c) * Real.log (n : ℝ)) ^ 2)) ((b / c) ^ 2) hnorm
  rwa [Real.sqrt_sq hbc.le] at hs

theorem ceilLogEnergy_scale (c b : ℝ) (hc : 0 < c) (hb : 0 < b) :
    Tendsto (ceilLogEnergy c b) atTop atTop ∧
      Tendsto (fun n : ℕ => (ceilLogEnergy c b n : ℝ) / Real.log (n : ℝ) ^ 2)
        atTop (𝓝 ((b / c) ^ 2)) ∧
      Tendsto (fun n : ℕ => Real.sqrt (ceilLogEnergy c b n : ℝ) / Real.log (n : ℝ))
        atTop (𝓝 (b / c)) := by
  exact rounded_log_energy_scale Nat.ceil tendsto_nat_ceil_atTop tendsto_nat_ceil_div_atTop c b hc hb

theorem floorLogEnergy_scale (c b : ℝ) (hc : 0 < c) (hb : 0 < b) :
    Tendsto (floorLogEnergy c b) atTop atTop ∧
      Tendsto (fun n : ℕ => (floorLogEnergy c b n : ℝ) / Real.log (n : ℝ) ^ 2)
        atTop (𝓝 ((b / c) ^ 2)) ∧
      Tendsto (fun n : ℕ => Real.sqrt (floorLogEnergy c b n : ℝ) / Real.log (n : ℝ))
        atTop (𝓝 (b / c)) := by
  exact rounded_log_energy_scale Nat.floor tendsto_nat_floor_atTop tendsto_nat_floor_div_atTop c b hc hb

end Lemmata.FockCircuits
