module

public import Lemmata.FockCircuits.Matrix.Profile.RowOffsets
public import Lemmata.FockCircuits.Matrix.Profile.PairIncrement

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Profile

open Set

theorem exists_affineRowPair_of_adjacent_secants (P Q : ℝ → ℝ)
    (hPpos : ∀ s, 0 < s → 0 < P s) (hQpos : ∀ s, 0 < s → 0 < Q s)
    (hP : ∀ {u v w : ℝ}, 0 < u → u < v → v < w →
      (P w - P v) / (w - v) ≤ (P v - P u) / (v - u))
    (hQ : ∀ {u v w : ℝ}, 0 < u → u < v → v < w →
      (Q w - Q v) / (w - v) ≤ (Q v - Q u) / (v - u))
    (htripP : ∀ s, 0 < s → 2 * P s + Q s ≤ P (3 * s + 1))
    (htripQ : ∀ s, 0 < s → 2 * Q s + P s ≤ Q (3 * s + 1)) :
    Nonempty (AffineRowPair P Q) := by
  apply exists_affineRowPair P Q hPpos hQpos
  · exact concaveOn_of_slope_anti_adjacent (convex_Ioi 0) fun hu _ huv hvw => hP hu huv hvw
  · exact concaveOn_of_slope_anti_adjacent (convex_Ioi 0) fun hu _ huv hvw => hQ hu huv hvw
  · exact htripP
  · exact htripQ

theorem AffineRowPair.left_increment_factor {P Q : ℝ → ℝ} (row : AffineRowPair P Q)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    P s * (1 + t / (s + row.leftOffset)) ≤ P (s + t) := by
  have hden : 0 < s + row.leftOffset := add_pos_of_pos_of_nonneg hs row.left_nonneg
  have hratio : P s / (s + row.leftOffset) ≤ row.slope :=
    (div_le_iff₀ hden).mpr (row.left_upper s hs)
  calc
    P s * (1 + t / (s + row.leftOffset)) =
      P s + t * (P s / (s + row.leftOffset)) := by ring
    _ ≤ P s + row.slope * t := by
      nlinarith [mul_le_mul_of_nonneg_left hratio ht.le]
    _ ≤ P (s + t) := row.left_increment s t hs ht

theorem AffineRowPair.left_powered_increment {f Q : ℝ → ℝ} {p : ℝ}
    (row : AffineRowPair (fun s => f s ^ p⁻¹) Q) (hp : 0 < p)
    (hpos : ∀ s, 0 < s → 0 < f s)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    f s * (1 + t / (s + row.leftOffset)) ^ p ≤ f (s + t) := by
  have hbase : 0 ≤ 1 + t / (s + row.leftOffset) := by
    have hden := add_pos_of_pos_of_nonneg hs row.left_nonneg
    positivity
  have h := Real.rpow_le_rpow
    (mul_nonneg (Real.rpow_nonneg (hpos s hs).le _) hbase)
    (row.left_increment_factor hs ht) hp.le
  rw [Real.mul_rpow (Real.rpow_nonneg (hpos s hs).le _) hbase,
    ← Real.rpow_mul (hpos s hs).le,
    ← Real.rpow_mul (hpos (s + t) (add_pos hs ht)).le] at h
  simpa only [inv_mul_cancel₀ hp.ne', Real.rpow_one] using h

theorem second_increment_of_affine_row (g : ℝ → ℝ → ℝ) {p : ℝ} {Q : ℝ → ℝ}
    (hp : 0 < p) (row : AffineRowPair (fun s => g 1 s ^ p⁻¹) Q)
    (hpos : ∀ R S, 0 < R → 0 < S → 0 < g R S)
    (hhom : ∀ R S lam, 0 < R → 0 < S → 0 < lam →
      g (lam * R) (lam * S) = lam * g R S)
    (R S t : ℝ) (hR : 0 < R) (hS : 0 < S) (ht : 0 < t) :
    g R S * (1 + t / (S + row.leftOffset * R)) ^ p ≤ g R (S + t) := by
  have hSR := div_pos hS hR
  have htR := div_pos ht hR
  have hunit := row.left_powered_increment hp (fun s hs => hpos 1 s (by norm_num) hs) hSR htR
  have hden : 0 < S + row.leftOffset * R :=
    add_pos_of_pos_of_nonneg hS (mul_nonneg row.left_nonneg hR.le)
  have hdenunit : 0 < S / R + row.leftOffset :=
    add_pos_of_pos_of_nonneg hSR row.left_nonneg
  have hratio : (t / R) / (S / R + row.leftOffset) =
      t / (S + row.leftOffset * R) := by
    field_simp [hR.ne', hden.ne', hdenunit.ne']
  rw [hratio, show S / R + t / R = (S + t) / R by ring] at hunit
  have hslice (v : ℝ) (hv : 0 < v) : g R v = R * g 1 (v / R) := by
    have h := hhom 1 (v / R) R (by norm_num) (div_pos hv hR) hR
    simpa only [mul_one, mul_div_cancel₀ _ hR.ne'] using h
  calc
    g R S * (1 + t / (S + row.leftOffset * R)) ^ p =
      R * (g 1 (S / R) * (1 + t / (S + row.leftOffset * R)) ^ p) := by
        rw [hslice S hS]
        ring
    _ ≤ R * g 1 ((S + t) / R) := mul_le_mul_of_nonneg_left hunit hR.le
    _ = g R (S + t) := (hslice (S + t) (add_pos hS ht)).symm

theorem product_bound_of_homogeneous_increments (g : ℝ → ℝ → ℝ)
    {p q a c : ℝ} (ha : 0 ≤ a)
    (hpos : ∀ R S, 0 < R → 0 < S → 0 < g R S)
    (hhom : ∀ R S lam, 0 < R → 0 < S → 0 < lam →
      g (lam * R) (lam * S) = lam * g R S)
    (hfirst : ∀ R S v, 0 < R → 0 < S → 0 < v →
      g R S * (1 + v / (R + c * S)) ^ q ≤ g (R + v) S)
    (hsecond : ∀ R S v, 0 < R → 0 < S → 0 < v →
      g R S * (1 + v / (S + a * R)) ^ p ≤ g R (S + v))
    (R S t : ℝ) (hR : 0 < R) (hS : 0 < S) (ht : 0 < t) :
    (1 + t * R / (R + c * S)) ^ q *
      (1 + t * S / ((S + a * R) + a * R * t)) ^ p ≤ 1 + t := by
  have hfirst' := hfirst R S (t * R) hR hS (mul_pos ht hR)
  have hR' : 0 < R + t * R := add_pos hR (mul_pos ht hR)
  have hsecond' := hsecond (R + t * R) S (t * S) hR' hS (mul_pos ht hS)
  have hden : S + a * (R + t * R) = (S + a * R) + a * R * t := by ring
  rw [hden] at hsecond'
  have hfactor : 0 ≤ (1 + t * S / ((S + a * R) + a * R * t)) ^ p := by
    apply Real.rpow_nonneg
    positivity
  have hcombine := (mul_le_mul_of_nonneg_right hfirst' hfactor).trans hsecond'
  have hhom' : g (R + t * R) (S + t * S) = (1 + t) * g R S := by
    rw [show R + t * R = (1 + t) * R by ring,
      show S + t * S = (1 + t) * S by ring]
    exact hhom R S (1 + t) hR hS (by linarith)
  rw [hhom'] at hcombine
  apply (mul_le_mul_iff_right₀ (hpos R S hR hS)).mp
  calc
    g R S * ((1 + t * R / (R + c * S)) ^ q *
        (1 + t * S / ((S + a * R) + a * R * t)) ^ p) =
      (g R S * (1 + t * R / (R + c * S)) ^ q) *
        (1 + t * S / ((S + a * R) + a * R * t)) ^ p := by ring
    _ ≤ (1 + t) * g R S := hcombine
    _ = g R S * (1 + t) := by ring

theorem pairRatio_of_homogeneous_increments (g : ℝ → ℝ → ℝ)
    {p q a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hpos : ∀ R S, 0 < R → 0 < S → 0 < g R S)
    (hhom : ∀ R S lam, 0 < R → 0 < S → 0 < lam →
      g (lam * R) (lam * S) = lam * g R S)
    (hfirst : ∀ R S v, 0 < R → 0 < S → 0 < v →
      g R S * (1 + v / (R + c * S)) ^ q ≤ g (R + v) S)
    (hsecond : ∀ R S v, 0 < R → 0 < S → 0 < v →
      g R S * (1 + v / (S + a * R)) ^ p ≤ g R (S + v)) :
    PairRatio p q a c := by
  apply pairRatio_of_product_bounds ha hc
  intro R S hR hS t ht
  exact product_bound_of_homogeneous_increments g ha hpos hhom hfirst hsecond R S t hR hS ht

theorem pairRatio_of_affine_rows (g : ℝ → ℝ → ℝ) {p q : ℝ}
    {P Q : ℝ → ℝ} (hp : 0 < p) (hq : 0 < q)
    (rowS : AffineRowPair (fun s => g 1 s ^ p⁻¹) P)
    (rowR : AffineRowPair (fun r => g r 1 ^ q⁻¹) Q)
    (hpos : ∀ R S, 0 < R → 0 < S → 0 < g R S)
    (hhom : ∀ R S lam, 0 < R → 0 < S → 0 < lam →
      g (lam * R) (lam * S) = lam * g R S) :
    PairRatio p q rowS.leftOffset rowR.leftOffset := by
  apply pairRatio_of_homogeneous_increments g rowS.left_nonneg rowR.left_nonneg hpos hhom
  · intro R S t hR hS ht
    exact second_increment_of_affine_row (fun x y => g y x) hq rowR
      (fun R S hR hS => hpos S R hS hR)
      (fun R S lam hR hS hlam => hhom S R lam hS hR hlam)
      S R t hS hR ht
  · exact second_increment_of_affine_row g hp rowS hpos hhom

end Lemmata.FockCircuits.Matrix.Profile
