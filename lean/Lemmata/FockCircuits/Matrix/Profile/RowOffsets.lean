module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Profile

open Set

noncomputable section

def rowRatio (P Q : ℝ → ℝ) (s : ℝ) : ℝ := (P s + Q s) / (2 * s + 1)

theorem rowRatio_le_adjacent {P Q : ℝ → ℝ}
    (hP : ConcaveOn ℝ (Ioi 0) P)
    (htrip : ∀ s, 0 < s → 2 * P s + Q s ≤ P (3 * s + 1))
    {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    rowRatio P Q v ≤ (P v - P u) / (v - u) := by
  have hv : 0 < v := hu.trans huv
  have hc := hP.slope_anti_adjacent hu (show 0 < 3 * v + 1 by linarith)
    huv (show v < 3 * v + 1 by linarith)
  calc
    rowRatio P Q v ≤ (P (3 * v + 1) - P v) / (2 * v + 1) := by
      exact div_le_div_of_nonneg_right (by linarith [htrip v hv]) (by linarith)
    _ = (P (3 * v + 1) - P v) / (3 * v + 1 - v) := by congr 1; ring
    _ ≤ (P v - P u) / (v - u) := hc

theorem rowRatio_mono {P Q : ℝ → ℝ}
    (hP : ConcaveOn ℝ (Ioi 0) P) (hQ : ConcaveOn ℝ (Ioi 0) Q)
    (htripP : ∀ s, 0 < s → 2 * P s + Q s ≤ P (3 * s + 1))
    (htripQ : ∀ s, 0 < s → 2 * Q s + P s ≤ Q (3 * s + 1)) :
    MonotoneOn (rowRatio P Q) (Ioi 0) := by
  intro u hu v hv huv
  change 0 < u at hu
  change 0 < v at hv
  rcases lt_or_eq_of_le huv with huv | rfl
  · have hp := (le_div_iff₀ (sub_pos.mpr huv)).mp
      (rowRatio_le_adjacent hP htripP hu huv)
    have hq := (le_div_iff₀ (sub_pos.mpr huv)).mp
      (rowRatio_le_adjacent hQ htripQ hu huv)
    have hr : rowRatio Q P v = rowRatio P Q v := by simp [rowRatio, add_comm]
    rw [hr] at hq
    have hnorm : rowRatio P Q v * (2 * v + 1) = P v + Q v := by
      unfold rowRatio
      exact div_mul_cancel₀ _ (by linarith)
    apply (div_le_iff₀ (by linarith : 0 < 2 * u + 1)).mpr
    nlinarith
  · exact le_rfl

theorem rowRatio_le_secant {P Q : ℝ → ℝ}
    (hP : ConcaveOn ℝ (Ioi 0) P) (hQ : ConcaveOn ℝ (Ioi 0) Q)
    (htripP : ∀ s, 0 < s → 2 * P s + Q s ≤ P (3 * s + 1))
    (htripQ : ∀ s, 0 < s → 2 * Q s + P s ≤ Q (3 * s + 1))
    {u v s : ℝ} (hu : 0 < u) (huv : u < v) (hs : 0 < s) :
    rowRatio P Q s ≤ (P v - P u) / (v - u) := by
  let w := max s v + 1
  have hwv : v < w := by dsimp [w]; linarith [le_max_right s v]
  have hws : s ≤ w := by dsimp [w]; linarith [le_max_left s v]
  have hv : 0 < v := hu.trans huv
  have hw : 0 < w := hv.trans hwv
  calc
    rowRatio P Q s ≤ rowRatio P Q w := rowRatio_mono hP hQ htripP htripQ hs hw hws
    _ ≤ (P w - P v) / (w - v) := rowRatio_le_adjacent hP htripP hv hwv
    _ ≤ (P v - P u) / (v - u) := hP.slope_anti_adjacent hu hw huv hwv

theorem lower_of_positive_increments {P : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hP : ∀ s, 0 < s → 0 < P s)
    (hinc : ∀ u v, 0 < u → u < v → L * (v - u) ≤ P v - P u)
    {s : ℝ} (hs : 0 < s) : L * s ≤ P s := by
  by_contra! hbad
  let u := (L * s - P s) / (2 * L)
  have hu : 0 < u := div_pos (sub_pos.mpr hbad) (by positivity)
  have hus : u < s := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * L)).mpr
    nlinarith [hP s hs]
  have heq : 2 * L * u = L * s - P s := by
    dsimp [u]
    field_simp [ne_of_gt hL]
  have hh := hinc u s hu hus
  nlinarith [hP u hu]

structure AffineRowPair (P Q : ℝ → ℝ) where
  slope : ℝ
  leftOffset : ℝ
  rightOffset : ℝ
  slope_pos : 0 < slope
  left_nonneg : 0 ≤ leftOffset
  right_nonneg : 0 ≤ rightOffset
  budget : leftOffset + rightOffset ≤ 1
  left_lower : ∀ s, 0 < s → slope * s ≤ P s
  right_lower : ∀ s, 0 < s → slope * s ≤ Q s
  left_upper : ∀ s, 0 < s → P s ≤ slope * (s + leftOffset)
  right_upper : ∀ s, 0 < s → Q s ≤ slope * (s + rightOffset)
  left_increment : ∀ s t, 0 < s → 0 < t → P s + slope * t ≤ P (s + t)
  right_increment : ∀ s t, 0 < s → 0 < t → Q s + slope * t ≤ Q (s + t)

/-- Positive concave rows with coupled tripling have a common affine slope and a shared offset budget. -/
theorem exists_affineRowPair (P Q : ℝ → ℝ)
    (hPpos : ∀ s, 0 < s → 0 < P s) (hQpos : ∀ s, 0 < s → 0 < Q s)
    (hP : ConcaveOn ℝ (Ioi 0) P) (hQ : ConcaveOn ℝ (Ioi 0) Q)
    (htripP : ∀ s, 0 < s → 2 * P s + Q s ≤ P (3 * s + 1))
    (htripQ : ∀ s, 0 < s → 2 * Q s + P s ≤ Q (3 * s + 1)) :
    Nonempty (AffineRowPair P Q) := by
  let S : Set ℝ := {x | ∃ s : ℝ, 0 < s ∧ x = rowRatio P Q s}
  have hSne : S.Nonempty := ⟨rowRatio P Q 1, 1, by norm_num, rfl⟩
  have hSbdd : BddAbove S := by
    refine ⟨(P 2 - P 1) / (2 - 1), ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact rowRatio_le_secant hP hQ htripP htripQ (by norm_num) (by norm_num) hs
  let L := sSup S
  have hratio (s : ℝ) (hs : 0 < s) : rowRatio P Q s ≤ L :=
    le_csSup hSbdd ⟨s, hs, rfl⟩
  have hL : 0 < L := by
    have hpos : 0 < rowRatio P Q 1 := by
      apply div_pos (add_pos (hPpos 1 (by norm_num)) (hQpos 1 (by norm_num)))
      norm_num
    exact hpos.trans_le (hratio 1 (by norm_num))
  have hPinc (u v : ℝ) (hu : 0 < u) (huv : u < v) :
      L * (v - u) ≤ P v - P u := by
    apply (le_div_iff₀ (sub_pos.mpr huv)).mp
    apply csSup_le hSne
    rintro _ ⟨s, hs, rfl⟩
    exact rowRatio_le_secant hP hQ htripP htripQ hu huv hs
  have hQinc (u v : ℝ) (hu : 0 < u) (huv : u < v) :
      L * (v - u) ≤ Q v - Q u := by
    apply (le_div_iff₀ (sub_pos.mpr huv)).mp
    apply csSup_le hSne
    rintro _ ⟨s, hs, rfl⟩
    simpa only [rowRatio, add_comm] using
      rowRatio_le_secant hQ hP htripQ htripP hu huv hs
  have hPlow (s : ℝ) (hs : 0 < s) : L * s ≤ P s :=
    lower_of_positive_increments hL hPpos hPinc hs
  have hQlow (s : ℝ) (hs : 0 < s) : L * s ≤ Q s :=
    lower_of_positive_increments hL hQpos hQinc hs
  have hmajor (s : ℝ) (hs : 0 < s) : P s + Q s ≤ L * (2 * s + 1) :=
    (div_le_iff₀ (by linarith : 0 < 2 * s + 1)).mp (hratio s hs)
  let a := fun s => P s / L - s
  let b := fun s => Q s / L - s
  have ha (s : ℝ) : a s * L = P s - L * s := by
    dsimp [a]
    field_simp [ne_of_gt hL]
  have hb (s : ℝ) : b s * L = Q s - L * s := by
    dsimp [b]
    field_simp [ne_of_gt hL]
  have ha0 (s : ℝ) (hs : 0 < s) : 0 ≤ a s := by
    apply nonneg_of_mul_nonneg_right _ hL
    rw [mul_comm L, ha]
    exact sub_nonneg.mpr (hPlow s hs)
  have hb0 (s : ℝ) (hs : 0 < s) : 0 ≤ b s := by
    apply nonneg_of_mul_nonneg_right _ hL
    rw [mul_comm L, hb]
    exact sub_nonneg.mpr (hQlow s hs)
  have hab (s : ℝ) (hs : 0 < s) : a s + b s ≤ 1 := by
    apply le_of_mul_le_mul_right _ hL
    rw [add_mul, ha, hb, one_mul]
    nlinarith [hmajor s hs]
  have hmonoA : MonotoneOn a (Ioi 0) := by
    intro u hu v hv huv
    rcases lt_or_eq_of_le huv with huv | rfl
    · apply le_of_mul_le_mul_right _ hL
      rw [ha, ha]
      nlinarith [hPinc u v hu huv]
    · exact le_rfl
  have hmonoB : MonotoneOn b (Ioi 0) := by
    intro u hu v hv huv
    rcases lt_or_eq_of_le huv with huv | rfl
    · apply le_of_mul_le_mul_right _ hL
      rw [hb, hb]
      nlinarith [hQinc u v hu huv]
    · exact le_rfl
  have hab' (u v : ℝ) (hu : 0 < u) (hv : 0 < v) : a u + b v ≤ 1 := by
    let w := max u v
    have hw : 0 < w := lt_of_lt_of_le hu (le_max_left u v)
    exact (add_le_add (hmonoA hu hw (le_max_left u v))
      (hmonoB hv hw (le_max_right u v))).trans (hab w hw)
  let A : Set ℝ := {x | ∃ s : ℝ, 0 < s ∧ x = a s}
  let B : Set ℝ := {x | ∃ s : ℝ, 0 < s ∧ x = b s}
  have hAne : A.Nonempty := ⟨a 1, 1, by norm_num, rfl⟩
  have hBne : B.Nonempty := ⟨b 1, 1, by norm_num, rfl⟩
  have hAbdd : BddAbove A := by
    refine ⟨1, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    linarith [hab s hs, hb0 s hs]
  have hBbdd : BddAbove B := by
    refine ⟨1, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    linarith [hab s hs, ha0 s hs]
  let c := sSup A
  let d := sSup B
  have hc (s : ℝ) (hs : 0 < s) : a s ≤ c := le_csSup hAbdd ⟨s, hs, rfl⟩
  have hd (s : ℝ) (hs : 0 < s) : b s ≤ d := le_csSup hBbdd ⟨s, hs, rfl⟩
  have hbudget : c + d ≤ 1 := by
    have hdu (u : ℝ) (hu : 0 < u) : d ≤ 1 - a u := by
      apply csSup_le hBne
      rintro _ ⟨v, hv, rfl⟩
      linarith [hab' u v hu hv]
    have hcd : c ≤ 1 - d := by
      apply csSup_le hAne
      rintro _ ⟨u, hu, rfl⟩
      linarith [hdu u hu]
    linarith
  refine ⟨⟨L, c, d, hL, (ha0 1 (by norm_num)).trans (hc 1 (by norm_num)),
    (hb0 1 (by norm_num)).trans (hd 1 (by norm_num)), hbudget,
    hPlow, hQlow, ?_, ?_, ?_, ?_⟩⟩
  · intro s hs
    have h := mul_le_mul_of_nonneg_right (hc s hs) hL.le
    rw [ha] at h
    nlinarith
  · intro s hs
    have h := mul_le_mul_of_nonneg_right (hd s hs) hL.le
    rw [hb] at h
    nlinarith
  · intro s t hs ht
    have h := hPinc s (s + t) hs (by linarith)
    linarith
  · intro s t hs ht
    have h := hQinc s (s + t) hs (by linarith)
    linarith

end

end Lemmata.FockCircuits.Matrix.Profile
