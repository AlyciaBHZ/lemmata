module

public import Lemmata.FockCircuits.Matrix.Character.Dot
public import Lemmata.FockCircuits.Matrix.Convolution.Rank
public import Mathlib.Tactic.FieldSimp

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Profile

open Set Foundation Spectral

noncomputable section

variable {K : Type*} [Field K] [Infinite K]

def profileValues (χ : Character K) (r s : ℝ) : Set ℝ :=
  {v | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ∃ t : ℝ,
    0 < t ∧ t * a ≤ r ∧ t * b ≤ s ∧ v = t * χ.value (convolution a b)}

def envelope (χ : Character K) (r s : ℝ) : ℝ := sSup (profileValues χ r s)

theorem profileValues_nonempty (χ : Character K) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (profileValues χ r s).Nonempty := by
  refine ⟨min r s * χ.value (convolution 1 1), 1, 1, by norm_num, by norm_num,
    min r s, lt_min hr hs, ?_, ?_, rfl⟩
  · simpa only [Nat.cast_one, mul_one] using min_le_left r s
  · simpa only [Nat.cast_one, mul_one] using min_le_right r s

theorem profileValues_le (χ : Character K) {r s v : ℝ} (hv : v ∈ profileValues χ r s) :
    v ≤ r + s := by
  obtain ⟨a, b, ha, hb, t, ht, htr, hts, rfl⟩ := hv
  have hv := χ.value_le_rank (convolution_rankAtMost (K := K) a b)
  have hdim : ((a + b - 1 : ℕ) : ℝ) ≤ (a : ℝ) + b := by
    exact_mod_cast Nat.sub_le (a + b) 1
  have hmul := mul_le_mul_of_nonneg_left (hv.trans hdim) ht.le
  nlinarith

theorem profileValues_bddAbove (χ : Character K) (r s : ℝ) :
    BddAbove (profileValues χ r s) := ⟨r + s, fun _ hv => profileValues_le χ hv⟩

theorem envelope_upper (χ : Character K) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    envelope χ r s ≤ r + s :=
  csSup_le (profileValues_nonempty χ hr hs) (fun _ hv => profileValues_le χ hv)

theorem envelope_positive (χ : Character K) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    0 < envelope χ r s := by
  have hχ : 0 < χ.value (convolution (K := K) 1 1) :=
    χ.value_pos (convolution_nonzero (by norm_num) (by norm_num))
  apply (mul_pos (lt_min hr hs) hχ).trans_le
  exact le_csSup (profileValues_bddAbove χ r s)
    ⟨1, 1, by norm_num, by norm_num, min r s, lt_min hr hs,
      by simpa only [Nat.cast_one, mul_one] using min_le_left r s,
      by simpa only [Nat.cast_one, mul_one] using min_le_right r s, rfl⟩

theorem envelope_mono (χ : Character K) {r s r' s' : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrr : r ≤ r') (hss : s ≤ s') :
    envelope χ r s ≤ envelope χ r' s' := by
  apply csSup_le (profileValues_nonempty χ hr hs)
  rintro v ⟨a, b, ha, hb, t, ht, htr, hts, rfl⟩
  exact le_csSup (profileValues_bddAbove χ r' s')
    ⟨a, b, ha, hb, t, ht, htr.trans hrr, hts.trans hss, rfl⟩

/-- The continuous size envelope is exactly homogeneous before any limiting argument. -/
theorem envelope_homogeneous (χ : Character K) {r s lam : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hlam : 0 < lam) :
    envelope χ (lam * r) (lam * s) = lam * envelope χ r s := by
  apply le_antisymm
  · apply csSup_le (profileValues_nonempty χ (mul_pos hlam hr) (mul_pos hlam hs))
    rintro v ⟨a, b, ha, hb, t, ht, htr, hts, rfl⟩
    have htr' : t / lam * a ≤ r := by
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hlam).mpr (by simpa only [mul_comm r lam] using htr)
    have hts' : t / lam * b ≤ s := by
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hlam).mpr (by simpa only [mul_comm s lam] using hts)
    have hv := le_csSup (profileValues_bddAbove χ r s)
      (show (t / lam) * χ.value (convolution a b) ∈ profileValues χ r s from
        ⟨a, b, ha, hb, t / lam, div_pos ht hlam, htr', hts', rfl⟩)
    have hh := mul_le_mul_of_nonneg_left hv hlam.le
    have heq : lam * (t / lam * χ.value (convolution a b)) =
        t * χ.value (convolution a b) := by field_simp [ne_of_gt hlam]
    change t * χ.value (convolution a b) ≤ lam * sSup (profileValues χ r s)
    simpa only [heq] using hh
  · rw [mul_comm lam]
    apply (le_div_iff₀ hlam).mp
    apply csSup_le (profileValues_nonempty χ hr hs)
    rintro v ⟨a, b, ha, hb, t, ht, htr, hts, rfl⟩
    apply (le_div_iff₀ hlam).mpr
    have hv := le_csSup (profileValues_bddAbove χ (lam * r) (lam * s))
      (show (lam * t) * χ.value (convolution a b) ∈ profileValues χ (lam * r) (lam * s) from
        ⟨a, b, ha, hb, lam * t, mul_pos hlam ht,
          by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left htr hlam.le,
          by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hts hlam.le, rfl⟩)
    change (t * χ.value (convolution a b)) * lam ≤
      sSup (profileValues χ (lam * r) (lam * s))
    simpa only [mul_assoc, mul_comm lam, mul_left_comm lam] using hv

theorem convolution_le_envelope (χ : Character K) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    χ.value (convolution a b) ≤ envelope χ a b := by
  change χ.value (convolution a b) ≤ sSup (profileValues χ a b)
  have h := le_csSup (profileValues_bddAbove χ a b)
    (show 1 * χ.value (convolution a b) ∈ profileValues χ a b from
      ⟨a, b, ha, hb, 1, by norm_num, by simp, by simp, rfl⟩)
  simpa only [one_mul] using h

end

end Lemmata.FockCircuits.Matrix.Profile
