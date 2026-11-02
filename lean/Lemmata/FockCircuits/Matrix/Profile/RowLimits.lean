module

public import Lemmata.FockCircuits.Matrix.Profile.EnvelopeLimits
public import Lemmata.FockCircuits.Matrix.Profile.Discrete
public import Lemmata.FockCircuits.Matrix.Profile.DiscreteSecants
public import Lemmata.FockCircuits.Matrix.Profile.RowLink

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Profile

open Filter Set Foundation Spectral
open scoped Topology

noncomputable section

variable {K : Type*} [Field K] [Infinite K] [IsAlgClosed K]

def poweredRow (χ : Character K) (s : ℝ) : ℝ := envelope χ 1 s ^ χ.pX⁻¹

theorem envelope_swap23_swap23 (χ : Character K) (r s : ℝ) :
    envelope χ.swap23Character.swap23Character r s = envelope χ r s := by
  rfl

theorem poweredRow_swap23_swap23 (χ : Character K) (s : ℝ) :
    poweredRow χ.swap23Character.swap23Character s = poweredRow χ s := by
  simp only [poweredRow, envelope_swap23_swap23, Character.swap23Character_pX]

theorem poweredRow_pos (χ : Character K) {s : ℝ} (hs : 0 < s) : 0 < poweredRow χ s :=
  Real.rpow_pos_of_pos (envelope_positive χ (by norm_num) hs) _

private def positiveIndex (r : ℝ) (n : ℕ) : ℕ := Nat.floor (r * (n : ℝ)) + 1

private theorem positiveIndex_pos (r : ℝ) (n : ℕ) : 0 < positiveIndex r n := by
  dsimp [positiveIndex]
  omega

private theorem positiveIndex_scale {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun n : ℕ => (positiveIndex r n : ℝ) / n) atTop (𝓝 r) := by
  have hN : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h := ((tendsto_nat_floor_mul_div_atTop hr).comp hN).add
    (tendsto_const_nhds.div_atTop hN : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0))
  simpa only [positiveIndex, Nat.cast_add, Nat.cast_one, add_div, add_zero,
    Function.comp_apply] using h

theorem poweredConvolution_secant_cross (χ : Character K) (hp : 0 < χ.pX)
    {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hbc : b < c) (hcd : c < d) :
    (poweredConvolution χ a d - poweredConvolution χ a c) * ((c : ℝ) - b) ≤
      (poweredConvolution χ a c - poweredConvolution χ a b) * ((d : ℝ) - c) := by
  let u : ℕ → ℝ := fun n => poweredConvolution χ a (n + 1)
  have hanti : Antitone (fun n => u (n + 1) - u n) := by
    apply antitone_nat_of_succ_le
    intro n
    have h := poweredConvolution_concavity_dims χ hp (a - 1) (n + 1) (by omega)
    rw [show a - 1 + 1 = a by omega] at h
    dsimp only [u]
    linarith
  have h := discrete_secant_antitone hanti
    (a := b - 1) (b := c - 1) (c := d - 1) (by omega) (by omega)
  have hden1 : (0 : ℝ) < (d - 1 : ℕ) - (c - 1 : ℕ) :=
    sub_pos.mpr (by exact_mod_cast (show c - 1 < d - 1 by omega))
  have hden2 : (0 : ℝ) < (c - 1 : ℕ) - (b - 1 : ℕ) :=
    sub_pos.mpr (by exact_mod_cast (show b - 1 < c - 1 by omega))
  have hcross := (div_le_div_iff₀ hden1 hden2).mp h
  simp only [u, Nat.sub_add_cancel (show 1 ≤ b by omega),
    Nat.sub_add_cancel (show 1 ≤ c by omega), Nat.sub_add_cancel (show 1 ≤ d by omega),
    Nat.cast_sub (show 1 ≤ b by omega), Nat.cast_sub (show 1 ≤ c by omega),
    Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_one] at hcross
  nlinarith only [hcross]

private theorem normalized_cross {x y z A B C N D : ℝ} (hN : 0 < N) (hD : 0 < D)
    (h : (z - y) * (B - A) ≤ (y - x) * (C - B)) :
    (z / D - y / D) * (B / N - A / N) ≤
      (y / D - x / D) * (C / N - B / N) := by
  have hm := mul_le_mul_of_nonneg_right h (one_div_nonneg.mpr (mul_nonneg hD.le hN.le))
  convert hm using 1 <;> field_simp [hN.ne', hD.ne']

theorem poweredRow_secant_cross (χ : Character K) (hp : 0 < χ.pX)
    {u v w : ℝ} (hu : 0 < u) (huv : u < v) (hvw : v < w) :
    (poweredRow χ w - poweredRow χ v) * (v - u) ≤
      (poweredRow χ v - poweredRow χ u) * (w - v) := by
  have hv : 0 < v := hu.trans huv
  have hw : 0 < w := hv.trans hvw
  let A := positiveIndex (1 : ℝ)
  let B := positiveIndex u
  let C := positiveIndex v
  let D := positiveIndex w
  have hA := positiveIndex_scale (by norm_num : (0 : ℝ) ≤ 1)
  have hB := positiveIndex_scale hu.le
  have hC := positiveIndex_scale hv.le
  have hD := positiveIndex_scale hw.le
  have hX := convolution_normalized_rpow_tendsto χ χ.pX⁻¹ A B (by norm_num) hu hA hB
  have hY := convolution_normalized_rpow_tendsto χ χ.pX⁻¹ A C (by norm_num) hv hA hC
  have hZ := convolution_normalized_rpow_tendsto χ χ.pX⁻¹ A D (by norm_num) hw hA hD
  have hleft := (hZ.sub hY).mul (hC.sub hB)
  have hright := (hY.sub hX).mul (hD.sub hC)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [hB.eventually_lt hC huv, hC.eventually_lt hD hvw,
    eventually_gt_atTop (0 : ℕ)] with n hBC hCD hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hbc : B n < C n := by
    exact_mod_cast (div_lt_div_iff_of_pos_right hnpos).mp hBC
  have hcd : C n < D n := by
    exact_mod_cast (div_lt_div_iff_of_pos_right hnpos).mp hCD
  exact normalized_cross hnpos (Real.rpow_pos_of_pos hnpos _) <|
    poweredConvolution_secant_cross χ hp (positiveIndex_pos 1 n) (positiveIndex_pos u n) hbc hcd

theorem poweredRow_concave (χ : Character K) (hp : 0 < χ.pX) :
    ConcaveOn ℝ (Ioi 0) (poweredRow χ) := by
  apply concaveOn_of_slope_anti_adjacent (convex_Ioi 0)
  intro u v w hu hw huv hvw
  exact (div_le_div_iff₀ (sub_pos.mpr hvw) (sub_pos.mpr huv)).mpr
    (poweredRow_secant_cross χ hp hu huv hvw)

theorem poweredRow_tripling (χ : Character K) (hp : 0 < χ.pX)
    {s : ℝ} (hs : 0 < s) :
    2 * poweredRow χ s + poweredRow χ.swap23Character s ≤ poweredRow χ (3 * s + 1) := by
  let A := positiveIndex (1 : ℝ)
  let B := positiveIndex s
  let C := fun n => 3 * B n + A n - 1
  have hA := positiveIndex_scale (by norm_num : (0 : ℝ) ≤ 1)
  have hB := positiveIndex_scale hs.le
  have hN : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hN
  have hC : Tendsto (fun n : ℕ => (C n : ℝ) / n) atTop (𝓝 (3 * s + 1)) := by
    have h := ((hB.const_mul 3).add hA).sub hone
    simp only [sub_zero] at h
    refine h.congr fun n => ?_
    dsimp only [C]
    rw [Nat.cast_sub (by have hpos := positiveIndex_pos 1 n; change 0 < A n at hpos; omega),
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  have hX := convolution_normalized_rpow_tendsto χ χ.pX⁻¹ A B (by norm_num) hs hA hB
  have hY := convolution_normalized_rpow_tendsto χ.swap23Character χ.pX⁻¹ A B
    (by norm_num) hs hA hB
  have hZ := convolution_normalized_rpow_tendsto χ χ.pX⁻¹ A C (by norm_num)
    (by linarith : 0 < 3 * s + 1) hA hC
  have hlim := (hX.const_mul 2).add hY
  have hle : 2 * poweredRow χ s + envelope χ.swap23Character 1 s ^ χ.pX⁻¹ ≤
      poweredRow χ (3 * s + 1) := by
    apply le_of_tendsto_of_tendsto hlim hZ
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have h := poweredConvolution_tripling χ hp (positiveIndex_pos 1 n) (positiveIndex_pos s n)
    have hdiv := div_le_div_of_nonneg_right h (Real.rpow_nonneg (Nat.cast_nonneg n) χ.pX⁻¹)
    simpa only [poweredConvolution, Character.swap23Character_pX, add_div, mul_div_assoc] using hdiv
  simpa only [poweredRow, Character.swap23Character_pX] using hle

theorem exists_powered_affineRowPair (χ : Character K) (hp : 0 < χ.pX) :
    Nonempty (AffineRowPair (poweredRow χ) (poweredRow χ.swap23Character)) := by
  apply exists_affineRowPair _ _ (fun _ => poweredRow_pos χ) (fun _ => poweredRow_pos χ.swap23Character)
    (poweredRow_concave χ hp)
    (poweredRow_concave χ.swap23Character (by simpa only [Character.swap23Character_pX] using hp))
  · exact fun _ => poweredRow_tripling χ hp
  · intro s hs
    simpa only [poweredRow_swap23_swap23] using poweredRow_tripling χ.swap23Character
      (by simpa only [Character.swap23Character_pX] using hp) hs

end

end Lemmata.FockCircuits.Matrix.Profile
