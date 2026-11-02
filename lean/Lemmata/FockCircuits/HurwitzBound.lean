module

public import Lemmata.FockCircuits.Families
public import Lemmata.FockCircuits.Hurwitz
public import Lemmata.FockCircuits.HurwitzCutoffs

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Topology

namespace Lemmata.FockCircuits.Hurwitz

open FiniteIdentity CrossingCircuit Families Filter

theorem finite_sum_of_squares (H n : ℕ) (hH : 0 < H)
    (hcapacity : 2 * H * n ≤ stateCount H - 1) :
    ∃ (s : ℕ) (forms : Fin s → Fin n → Fin n → ℂ),
      s ≤ 8 * H * stateCount (2 * H) ∧
      ∀ (x y : Fin n → ℂ),
        (∑ r, bilinear (forms r) x y ^ 2) = (∑ i, x i ^ 2) * (∑ j, y j ^ 2) := by
  classical
  obtain ⟨W, B, hW, hWH, hBinj, hBW, _⟩ :=
    exists_dual_family ℤ H (2 * H) n hH (by omega) hcapacity
  let B' : Fin n ↪ Index (2 * H) := ⟨B, hBinj⟩
  let middle := cutoffEmbedding (E := 2 * H) (L := 2 * H) le_rfl
  let a := coefficientA ℤ (dualFamily ℤ B') B' middle (W := W)
  let b := coefficientB ℤ (bareFamily ℤ B') B' middle (W := W)
  let c := coefficientC ℤ (dualFamily ℤ B') B' middle (W := W)
  let d := coefficientD ℤ (bareFamily ℤ B') B' middle (W := W)
  have hcoeff (i j k l : Fin n) :
      (∑ r, a r i j * b r k l) +
        (∑ r, (-(sigma W) * c r i l) * d r k j) =
          if i = k then (if j = l then 1 else 0) else 0 := by
    have h := family_coefficient_identity ℤ B' B' middle hW hBW
      (E := H) (fun j => by change doubledEnergy (B j).val ≤ 2 * H; rw [hBW]; exact hWH)
      (cutoffEmbedding_covers (2 * H)) (by omega) i k j l
    simpa [a, b, c, d, mul_assoc, ← Finset.mul_sum, neg_mul, sub_eq_add_neg,
      Finset.sum_neg_distrib] using h
  obtain ⟨forms, hforms⟩ := squares_of_integral_crossing a b
    (fun r i j => -(sigma W) * c r i j) d hcoeff
  let T := ((Fin W × ↥(fullCutoff (2 * H))) × Bool) × Bool
  let e : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  refine ⟨Fintype.card T, fun r => forms (e.symm r), ?_, ?_⟩
  · have hcard : Fintype.card T = 4 * W * stateCount (2 * H) := by
      simp only [T, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
        Fintype.card_bool, stateCount]
      ring
    rw [hcard]
    exact Nat.mul_le_mul_right _ (by omega : 4 * W ≤ 8 * H)
  · intro x y
    exact (e.symm.sum_comp (fun r => bilinear (forms r) x y ^ 2)).trans (hforms x y)

theorem eventually_sum_of_squares (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      ∃ (s : ℕ) (forms : Fin s → Fin n → Fin n → ℂ),
        (s : ℝ) ≤ (n : ℝ) ^ (Real.sqrt 2 + eps) ∧
        ∀ (x y : Fin n → ℂ),
          (∑ r, bilinear (forms r) x y ^ 2) = (∑ i, x i ^ 2) * (∑ j, y j ^ 2) := by
  obtain ⟨padding, hpadding, hparameters⟩ :=
    exists_hurwitz_energy_parameters (eps / 2) (by linarith)
  let H := ceilLogEnergy countingConstant (1 + padding)
  have hb : 0 < 1 + padding := by linarith
  obtain ⟨hHtop, hHscale, _⟩ := ceilLogEnergy_scale countingConstant (1 + padding)
    countingConstant_pos hb
  have hHlog := log_energy_ratio_tendsto_zero H _
    (sq_pos_of_pos (div_pos hb countingConstant_pos)) hHtop hHscale
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htwo : Tendsto (fun n : ℕ => Real.log ((2 : ℕ) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  have hHne : ∀ᶠ n : ℕ in atTop, H n ≠ 0 :=
    (hHtop.eventually_gt_atTop 0).mono fun _ h => h.ne'
  have h2H := log_nat_product_limit (fun _ : ℕ => 2) H 0 0
    (Eventually.of_forall fun _ => by norm_num) hHne htwo hHlog
  have hsmall := eventually_le_rpow_of_log_limit (fun n => 2 * H n) 0
    (hHne.mono fun _ h => Nat.mul_ne_zero (by norm_num) h) (by simpa using h2H)
    (eps / 2) (by linarith)
  filter_upwards [hparameters, hsmall, eventually_gt_atTop (0 : ℕ)]
    with n hparametersN hsmallN hn
  obtain ⟨s, forms, hs, hforms⟩ := finite_sum_of_squares (H n) n
    hparametersN.1 hparametersN.2.1
  refine ⟨s, forms, ?_, hforms⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (s : ℝ) ≤ ((8 * H n * stateCount (2 * H n) : ℕ) : ℝ) := by exact_mod_cast hs
    _ = ((2 * H n : ℕ) : ℝ) * ((4 * stateCount (2 * H n) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (n : ℝ) ^ (eps / 2) * (n : ℝ) ^ (Real.sqrt 2 + eps / 2) := by
      exact mul_le_mul (by simpa using hsmallN) hparametersN.2.2
        (Nat.cast_nonneg _) (Real.rpow_pos_of_pos hnR _).le
    _ = (n : ℝ) ^ (Real.sqrt 2 + eps) := by
      rw [← Real.rpow_add hnR]
      congr 1
      ring

end Lemmata.FockCircuits.Hurwitz
