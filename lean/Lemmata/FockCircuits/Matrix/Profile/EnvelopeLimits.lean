module

public import Lemmata.FockCircuits.Matrix.Profile.Envelope
public import Lemmata.FockCircuits.Matrix.Profile.ReplicationDegeneration
public import Lemmata.FockCircuits.Matrix.Convolution.Monotone
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Profile

open Filter Set Foundation Spectral
open scoped Topology

noncomputable section

variable {K : Type*} [Field K] [Infinite K]

theorem convolution_normalized_tendsto_envelope (χ : Character K)
    (A B : ℕ → ℕ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hA : Tendsto (fun n : ℕ => (A n : ℝ) / n) atTop (𝓝 r))
    (hB : Tendsto (fun n : ℕ => (B n : ℝ) / n) atTop (𝓝 s)) :
    Tendsto (fun n : ℕ => χ.value (convolution (A n) (B n)) / n)
      atTop (𝓝 (envelope χ r s)) := by
  have hN : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have henv : 0 < envelope χ r s := envelope_positive χ hr hs
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro l hl
    by_cases hlneg : l < 0
    · exact Eventually.of_forall fun n => hlneg.trans_le
        (div_nonneg (χ.nonneg _) (Nat.cast_nonneg _))
    have hl0 : 0 ≤ l := le_of_not_gt hlneg
    obtain ⟨v, hv, hlv⟩ := (lt_csSup_iff (profileValues_bddAbove χ r s)
      (profileValues_nonempty χ hr hs)).mp hl
    obtain ⟨a, b, ha, hb, t, ht, htr, hts, rfl⟩ := hv
    have hf : 0 < χ.value (convolution a b) := χ.value_pos (convolution_nonzero ha hb)
    have hvpos : 0 < t * χ.value (convolution a b) := mul_pos ht hf
    let lam : ℝ := (t * χ.value (convolution a b) + l) /
      (2 * (t * χ.value (convolution a b)))
    have hlam : 0 < lam := div_pos (by linarith) (by positivity)
    have hlam1 : lam < 1 := by
      apply (div_lt_iff₀ (by positivity : 0 < 2 * (t * χ.value (convolution a b)))).mpr
      linarith
    have hlamv : l < (lam * t) * χ.value (convolution a b) := by
      have hid : (lam * t) * χ.value (convolution a b) =
          (t * χ.value (convolution a b) + l) / 2 := by
        dsimp [lam]
        field_simp [ht.ne', hf.ne'] <;> ring
      rw [hid]
      linarith
    let q : ℕ → ℕ := fun n => Nat.floor ((lam * t) * (n : ℝ))
    have hq : Tendsto (fun n : ℕ => (q n : ℝ) / n) atTop (𝓝 (lam * t)) := by
      exact (tendsto_nat_floor_mul_div_atTop (mul_pos hlam ht).le).comp hN
    have hqa : (lam * t) * a < r := by
      have hta : 0 < t * (a : ℝ) := mul_pos ht (by exact_mod_cast ha)
      calc
        (lam * t) * a = lam * (t * a) := by ring
        _ < t * a := by simpa only [one_mul] using mul_lt_mul_of_pos_right hlam1 hta
        _ ≤ r := htr
    have hqb : (lam * t) * b < s := by
      have htb : 0 < t * (b : ℝ) := mul_pos ht (by exact_mod_cast hb)
      calc
        (lam * t) * b = lam * (t * b) := by ring
        _ < t * b := by simpa only [one_mul] using mul_lt_mul_of_pos_right hlam1 htb
        _ ≤ s := hts
    filter_upwards [(hq.mul_const (a : ℝ)).eventually_lt hA hqa,
      (hq.mul_const (b : ℝ)).eventually_lt hB hqb,
      (hq.mul_const (χ.value (convolution a b))).eventually_const_lt hlamv,
      eventually_gt_atTop (0 : ℕ)] with n hqa hqb hlow hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hqa' : q n * a ≤ A n := by
      have h : (q n : ℝ) * a < A n :=
        (div_lt_div_iff_of_pos_right hnpos).mp (by
          simpa only [div_mul_eq_mul_div] using hqa)
      exact_mod_cast h.le
    have hqb' : q n * b ≤ B n := by
      have h : (q n : ℝ) * b < B n :=
        (div_lt_div_iff_of_pos_right hnpos).mp (by
          simpa only [div_mul_eq_mul_div] using hqb)
      exact_mod_cast h.le
    have hvalue := (Replication.value_convolution_replicate χ (q n) a b).trans
      (χ.value_convolution_mono hqa' hqb')
    have hdiv := div_le_div_of_nonneg_right hvalue hnpos.le
    have hlower : l < (q n : ℝ) * χ.value (convolution a b) / n := by
      simpa only [div_mul_eq_mul_div] using hlow
    exact hlower.trans_le hdiv
  · intro u hu
    let lam : ℝ := (1 + u / envelope χ r s) / 2
    have hlam1 : 1 < lam := by
      have hdiv : 1 < u / envelope χ r s := (lt_div_iff₀ henv).mpr (by simpa using hu)
      dsimp [lam]
      linarith
    have hlam : 0 < lam := by linarith
    have hlamu : lam * envelope χ r s < u := by
      have hid : lam * envelope χ r s = (envelope χ r s + u) / 2 := by
        dsimp [lam]
        field_simp [henv.ne'] <;> ring
      rw [hid]
      linarith
    have hr' : r < lam * r := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hlam1 hr
    have hs' : s < lam * s := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hlam1 hs
    filter_upwards [hA.eventually_lt_const hr', hB.eventually_lt_const hs',
      hA.eventually_const_lt hr, hB.eventually_const_lt hs,
      eventually_gt_atTop (0 : ℕ)] with n hAr hBs hApos hBpos hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hAn : 0 < A n := by
      have h : (0 : ℝ) < A n := by simpa only [zero_mul] using (lt_div_iff₀ hnpos).mp hApos
      exact_mod_cast h
    have hBn : 0 < B n := by
      have h : (0 : ℝ) < B n := by simpa only [zero_mul] using (lt_div_iff₀ hnpos).mp hBpos
      exact_mod_cast h
    have hmem : χ.value (convolution (A n) (B n)) / n ∈
        profileValues χ (lam * r) (lam * s) := by
      refine ⟨A n, B n, hAn, hBn, 1 / n, one_div_pos.mpr hnpos, ?_, ?_, ?_⟩
      · calc
          (1 / (n : ℝ)) * A n = (A n : ℝ) / n := by ring
          _ ≤ lam * r := hAr.le
      · calc
          (1 / (n : ℝ)) * B n = (B n : ℝ) / n := by ring
          _ ≤ lam * s := hBs.le
      · ring
    have hle := le_csSup (profileValues_bddAbove χ (lam * r) (lam * s)) hmem
    change χ.value (convolution (A n) (B n)) / n ≤ envelope χ (lam * r) (lam * s) at hle
    rw [envelope_homogeneous χ hr hs hlam] at hle
    exact hle.trans_lt hlamu

theorem convolution_floor_tendsto_envelope (χ : Character K)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Tendsto (fun n : ℕ => χ.value (convolution
      (Nat.floor (r * (n : ℝ))) (Nat.floor (s * (n : ℝ)))) / n)
      atTop (𝓝 (envelope χ r s)) := by
  apply convolution_normalized_tendsto_envelope χ _ _ hr hs
  · exact (tendsto_nat_floor_mul_div_atTop hr.le).comp tendsto_natCast_atTop_atTop
  · exact (tendsto_nat_floor_mul_div_atTop hs.le).comp tendsto_natCast_atTop_atTop

theorem convolution_normalized_rpow_tendsto (χ : Character K) (z : ℝ)
    (A B : ℕ → ℕ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hA : Tendsto (fun n : ℕ => (A n : ℝ) / n) atTop (𝓝 r))
    (hB : Tendsto (fun n : ℕ => (B n : ℝ) / n) atTop (𝓝 s)) :
    Tendsto (fun n : ℕ => χ.value (convolution (A n) (B n)) ^ z / (n : ℝ) ^ z)
      atTop (𝓝 (envelope χ r s ^ z)) := by
  have h := (convolution_normalized_tendsto_envelope χ A B hr hs hA hB).rpow_const (p := z)
    (Or.inl (envelope_positive χ hr hs).ne')
  exact h.congr fun n => Real.div_rpow (χ.nonneg _) (Nat.cast_nonneg _) z

end

end Lemmata.FockCircuits.Matrix.Profile
