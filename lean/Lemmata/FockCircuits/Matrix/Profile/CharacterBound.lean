module

public import Lemmata.FockCircuits.Matrix.Profile.RowLimits

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Profile

open Set Foundation Spectral

noncomputable section

variable {K : Type*} [Field K] [Infinite K] [IsAlgClosed K]

theorem value_convolution_swap_inputs (χ : Character K) (a b : ℕ) :
    χ.swap23Character.cyclicCharacter.value (convolution a b) =
      χ.value (convolution b a) := by
  let e : Fin (a + b - 1) ≃ Fin (b + a - 1) := finCongr (by omega)
  have heq : Tensor.pullback (Equiv.refl (Fin b)) (Equiv.refl (Fin a)) e
      (convolution (K := K) b a) = fun y x z => convolution (K := K) a b x y z := by
    funext y x z
    change (if y.val + x.val = z.val then (1 : K) else 0) =
      if x.val + y.val = z.val then (1 : K) else 0
    rw [Nat.add_comm y.val x.val]
  change χ.value (fun y x z => convolution (K := K) a b x y z) = _
  rw [← heq, χ.value_reindex]

theorem envelope_swap_inputs (χ : Character K) (r s : ℝ) :
    envelope χ.swap23Character.cyclicCharacter r s = envelope χ s r := by
  apply congrArg sSup
  ext v
  constructor
  · rintro ⟨a, b, ha, hb, t, ht, htr, hts, hv⟩
    refine ⟨b, a, hb, ha, t, ht, hts, htr, ?_⟩
    simpa only [value_convolution_swap_inputs] using hv
  · rintro ⟨a, b, ha, hb, t, ht, hts, htr, hv⟩
    refine ⟨b, a, hb, ha, t, ht, htr, hts, ?_⟩
    simpa only [value_convolution_swap_inputs] using hv

theorem poweredRow_cyclic_twice_swap (χ : Character K) (r : ℝ) :
    poweredRow χ.cyclicCharacter.cyclicCharacter.swap23Character r =
      envelope χ r 1 ^ χ.pY⁻¹ := by
  have heq : envelope χ.cyclicCharacter.cyclicCharacter.swap23Character 1 r =
      envelope χ.swap23Character.cyclicCharacter 1 r := rfl
  simp only [poweredRow, Character.swap23Character_pX,
    Character.cyclicCharacter_pX, Character.cyclicCharacter_pZ]
  rw [heq, envelope_swap_inputs]

def AffineRowPair.symm {P Q : ℝ → ℝ} (row : AffineRowPair P Q) : AffineRowPair Q P where
  slope := row.slope
  leftOffset := row.rightOffset
  rightOffset := row.leftOffset
  slope_pos := row.slope_pos
  left_nonneg := row.right_nonneg
  right_nonneg := row.left_nonneg
  budget := by simpa only [add_comm] using row.budget
  left_lower := row.right_lower
  right_lower := row.left_lower
  left_upper := row.right_upper
  right_upper := row.left_upper
  left_increment := row.right_increment
  right_increment := row.left_increment

def AffineRowPair.congr_left {P Q P' : ℝ → ℝ} (row : AffineRowPair P Q)
    (heq : ∀ s, P s = P' s) : AffineRowPair P' Q where
  slope := row.slope
  leftOffset := row.leftOffset
  rightOffset := row.rightOffset
  slope_pos := row.slope_pos
  left_nonneg := row.left_nonneg
  right_nonneg := row.right_nonneg
  budget := row.budget
  left_lower s hs := by rw [← heq s]; exact row.left_lower s hs
  right_lower := row.right_lower
  left_upper s hs := by rw [← heq s]; exact row.left_upper s hs
  right_upper := row.right_upper
  left_increment s t hs ht := by rw [← heq s, ← heq (s + t)]; exact row.left_increment s t hs ht
  right_increment := row.right_increment

theorem pairRatio_of_powered_rows (χ : Character K) (hp : 0 < χ.pX) (hq : 0 < χ.pY)
    {P Q : ℝ → ℝ} (rowS : AffineRowPair (poweredRow χ) P)
    (rowR : AffineRowPair (poweredRow χ.cyclicCharacter.cyclicCharacter.swap23Character) Q) :
    PairRatio χ.pX χ.pY rowS.leftOffset rowR.leftOffset := by
  exact pairRatio_of_affine_rows (envelope χ) hp hq rowS
    (rowR.congr_left (poweredRow_cyclic_twice_swap χ))
    (fun _ _ => envelope_positive χ)
    (fun _ _ _ => envelope_homogeneous χ)

def chosenRow (χ : Character K) (hp : 0 < χ.pX) :
    AffineRowPair (poweredRow χ) (poweredRow χ.swap23Character) :=
  Classical.choice (exists_powered_affineRowPair χ hp)

def leftOffset (χ : Character K) : ℝ :=
  if hp : 0 < χ.pX then (chosenRow χ hp).leftOffset else 0

def rightOffset (χ : Character K) : ℝ :=
  if hp : 0 < χ.pX then (chosenRow χ hp).rightOffset else 0

theorem offsets_nonneg_budget (χ : Character K) :
    0 ≤ leftOffset χ ∧ 0 ≤ rightOffset χ ∧ leftOffset χ + rightOffset χ ≤ 1 := by
  by_cases hp : 0 < χ.pX
  · simp only [leftOffset, rightOffset, dite_eq_left hp]
    exact ⟨(chosenRow χ hp).left_nonneg, (chosenRow χ hp).right_nonneg,
      (chosenRow χ hp).budget⟩
  · simp only [leftOffset, rightOffset, dite_eq_right hp]
    norm_num

theorem pairRatio_XY (χ : Character K) :
    PairRatio χ.pX χ.pY (leftOffset χ) (rightOffset χ.cyclicCharacter.cyclicCharacter) := by
  by_cases hp : 0 < χ.pX
  · by_cases hq : 0 < χ.pY
    · have hq' : 0 < χ.cyclicCharacter.cyclicCharacter.pX := by
        simpa only [Character.cyclicCharacter_pX, Character.cyclicCharacter_pZ] using hq
      simpa only [leftOffset, rightOffset, dite_eq_left hp, dite_eq_left hq', AffineRowPair.symm] using
        pairRatio_of_powered_rows χ hp hq (chosenRow χ hp)
          (chosenRow χ.cyclicCharacter.cyclicCharacter hq').symm
    · have hz : χ.pY = 0 := le_antisymm (le_of_not_gt hq) χ.pY_nonneg
      rw [hz]
      exact PairRatio.zero_right χ.pX_le_one (offsets_nonneg_budget χ).1
  · have hz : χ.pX = 0 := le_antisymm (le_of_not_gt hp) χ.pX_nonneg
    rw [hz]
    exact PairRatio.zero_left χ.pY_le_one
      (offsets_nonneg_budget χ.cyclicCharacter.cyclicCharacter).2.1

theorem pairRatio_XZ (χ : Character K) :
    PairRatio χ.pX χ.pZ (rightOffset χ) (leftOffset χ.cyclicCharacter) := by
  by_cases hp : 0 < χ.pX
  · by_cases hq : 0 < χ.pZ
    · have hp' : 0 < χ.swap23Character.pX := by simpa only [Character.swap23Character_pX] using hp
      have hq' : 0 < χ.cyclicCharacter.pX := by simpa only [Character.cyclicCharacter_pX] using hq
      have hpY : 0 < χ.swap23Character.pY := by simpa only [Character.swap23Character_pY] using hq
      let hrow : AffineRowPair
          (poweredRow χ.swap23Character.cyclicCharacter.cyclicCharacter.swap23Character)
          (poweredRow χ.cyclicCharacter.swap23Character) := chosenRow χ.cyclicCharacter hq'
      simpa only [Character.swap23Character_pX, Character.swap23Character_pY,
        leftOffset, rightOffset, dite_eq_left hp, dite_eq_left hq', hrow, AffineRowPair.symm] using
        pairRatio_of_powered_rows χ.swap23Character hp' hpY (chosenRow χ hp).symm hrow
    · have hz : χ.pZ = 0 := le_antisymm (le_of_not_gt hq) χ.pZ_nonneg
      rw [hz]
      exact PairRatio.zero_right χ.pX_le_one (offsets_nonneg_budget χ).2.1
  · have hz : χ.pX = 0 := le_antisymm (le_of_not_gt hp) χ.pX_nonneg
    rw [hz]
    exact PairRatio.zero_left χ.pZ_le_one (offsets_nonneg_budget χ.cyclicCharacter).1

theorem pairRatio_YZ (χ : Character K) :
    PairRatio χ.pY χ.pZ (leftOffset χ.cyclicCharacter.cyclicCharacter)
      (rightOffset χ.cyclicCharacter) := by
  by_cases hp : 0 < χ.pY
  · by_cases hq : 0 < χ.pZ
    · have hp' : 0 < χ.cyclicCharacter.cyclicCharacter.pX := by
        simpa only [Character.cyclicCharacter_pX, Character.cyclicCharacter_pZ] using hp
      have hq' : 0 < χ.cyclicCharacter.pX := by simpa only [Character.cyclicCharacter_pX] using hq
      have hpY : 0 < χ.cyclicCharacter.cyclicCharacter.pY := by
        simpa only [Character.cyclicCharacter_pY, Character.cyclicCharacter_pX] using hq
      let hrow : AffineRowPair
          (poweredRow χ.cyclicCharacter.cyclicCharacter.cyclicCharacter.cyclicCharacter.swap23Character)
          (poweredRow χ.cyclicCharacter) := (chosenRow χ.cyclicCharacter hq').symm
      simpa only [Character.cyclicCharacter_pX, Character.cyclicCharacter_pY,
        Character.cyclicCharacter_pZ, leftOffset, rightOffset, dite_eq_left hp', dite_eq_left hq',
        dite_eq_left hp, dite_eq_left hq, hrow,
        AffineRowPair.symm] using
        pairRatio_of_powered_rows χ.cyclicCharacter.cyclicCharacter hp' hpY
          (chosenRow χ.cyclicCharacter.cyclicCharacter hp') hrow
    · have hz : χ.pZ = 0 := le_antisymm (le_of_not_gt hq) χ.pZ_nonneg
      rw [hz]
      exact PairRatio.zero_right χ.pY_le_one
        (offsets_nonneg_budget χ.cyclicCharacter.cyclicCharacter).1
  · have hz : χ.pY = 0 := le_antisymm (le_of_not_gt hp) χ.pY_nonneg
    rw [hz]
    exact PairRatio.zero_left χ.pZ_le_one (offsets_nonneg_budget χ.cyclicCharacter).2.1

theorem weighted_character_bound (χ : Character K) (A B C : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    A * χ.pX + B * χ.pY + C * χ.pZ ≤
      (A * B + A * C + B * C) ^ 2 / (4 * A * B * C) := by
  obtain ⟨h0L, h0R, h0⟩ := offsets_nonneg_budget χ
  obtain ⟨h1L, h1R, h1⟩ := offsets_nonneg_budget χ.cyclicCharacter
  obtain ⟨h2L, h2R, h2⟩ := offsets_nonneg_budget χ.cyclicCharacter.cyclicCharacter
  exact weighted_bound_of_pair_ratios A B C χ.pX χ.pY χ.pZ
    (leftOffset χ) (rightOffset χ) (rightOffset χ.cyclicCharacter.cyclicCharacter)
    (leftOffset χ.cyclicCharacter.cyclicCharacter) (leftOffset χ.cyclicCharacter)
    (rightOffset χ.cyclicCharacter) hA hB hC χ.pX_nonneg χ.pY_nonneg χ.pZ_nonneg
    h0L h0R h2R h2L h1L h1R h0 (by simpa only [add_comm] using h2) h1
    (pairRatio_XY χ) (pairRatio_XZ χ) (pairRatio_YZ χ)

end

end Lemmata.FockCircuits.Matrix.Profile
