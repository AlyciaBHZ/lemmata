module

public import Lemmata.FockCircuits.Matrix.Determinant.Character
public import Lemmata.FockCircuits.Matrix.Sector.Character
public import Lemmata.FockCircuits.Matrix.Entropy.Optimization
public import Lemmata.FockCircuits.Matrix.Character.Permutation

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Profile

open Foundation Spectral
open Spectral.DeterminantFiltration
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def weightedLaw (w : ι → ℝ) (hw : ∀ i, 0 < w i) : FiniteLaw ι where
  mass i := w i / ∑ j, w j
  nonneg i := div_nonneg (hw i).le (Finset.sum_nonneg (fun j _ => (hw j).le))
  total := by
    have hsum : 0 < ∑ i, w i := Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
    rw [← Finset.sum_div, div_self hsum.ne']

theorem weightedLaw_entropy (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    finiteEntropy (weightedLaw w hw).mass +
      ∑ i, (weightedLaw w hw).mass i * Real.log (w i) = Real.log (∑ i, w i) := by
  have h := finite_entropy_log_partition Finset.univ w Finset.univ_nonempty
    (fun i _ => hw i)
  simpa [finiteEntropy, entropyTerm, weightedLaw, Finset.sum_neg_distrib, mul_comm] using h

/-- Optimizing the probability law turns a logarithmic tag bound into a sum of powered values. -/
theorem power_sum_of_log_tags (v : ι → ℝ) {p z : ℝ} (hv : ∀ i, 0 < v i)
    (hp : 0 < p) (hz : 0 < z)
    (htag : ∀ q : FiniteLaw ι,
      p * finiteEntropy q.mass + ∑ i, q.mass i * Real.log (v i) ≤ Real.log z) :
    ∑ i, v i ^ p⁻¹ ≤ z ^ p⁻¹ := by
  let w := fun i => v i ^ p⁻¹
  have hw (i : ι) : 0 < w i := Real.rpow_pos_of_pos (hv i) _
  let q := weightedLaw w hw
  have hlog (i : ι) : Real.log (v i) = p * Real.log (w i) := by
    dsimp [w]
    rw [Real.log_rpow (hv i), ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
  have hsum : 0 < ∑ i, w i := Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  have he := weightedLaw_entropy w hw
  have heq : ∑ i, q.mass i * Real.log (v i) =
      p * ∑ i, q.mass i * Real.log (w i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hlog]
    ring
  have hh : p * Real.log (∑ i, w i) ≤ Real.log z := by
    rw [← he, mul_add, ← heq]
    exact htag q
  apply (Real.log_le_log_iff hsum (Real.rpow_pos_of_pos hz _)).mp
  rw [Real.log_rpow hz]
  have hd := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hh)
  simpa only [div_eq_mul_inv, mul_comm] using hd

variable {K : Type*} [Field K]

theorem sharedFirst_power_sum [IsAlgClosed K] {s : ℕ} [Nonempty (Fin s)]
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (χ : Character K) (hp : 0 < χ.pX) (B : Fin s → Tensor K X Y Z)
    (hB : ∀ i, B i ≠ 0) :
    ∑ i, χ.value (B i) ^ χ.pX⁻¹ ≤ χ.value (sharedFirstTensor B) ^ χ.pX⁻¹ := by
  let i : Fin s := Classical.choice inferInstance
  have hsource := sharedFirstTensor_ne_zero_of_branch B i (hB i)
  exact power_sum_of_log_tags (fun i => χ.value (B i))
    (fun i => χ.value_pos (hB i)) hp (χ.value_pos hsource)
    (fun q => χ.log_sharedFirst_tag q B hB)

def poweredConvolution (χ : Character K) (a b : ℕ) : ℝ :=
  χ.value (convolution a b) ^ χ.pX⁻¹

/-- The determinant filtration gives discrete concavity in the oriented second input. -/
theorem poweredConvolution_concavity_dims [IsAlgClosed K] (χ : Character K)
    (hp : 0 < χ.pX) (d e : ℕ) (he : 0 < e) :
    poweredConvolution χ (d + 1) (e + 2) + poweredConvolution χ (d + 1) e ≤
      2 * poweredConvolution χ (d + 1) (e + 1) := by
  have h := sharedFirst_power_sum χ hp (branch (K := K) d e)
    (branch_ne_zero (K := K) d e he)
  rw [Fin.sum_univ_two, χ.value_determinant_branch_zero, χ.value_determinant_branch_one,
    χ.value_sharedFirstTensor_eq_sum (branch (K := K) d e)
      (branchLabel e) (branchLabel (d + e)) (branch_support (K := K) d e), sum_branch] at h
  have hu := Real.rpow_le_rpow (χ.nonneg _) (χ.value_determinant_graded_le d e)
    (inv_nonneg.mpr hp.le)
  have hh := h.trans hu
  rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (χ.nonneg _),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_inv_cancel₀ hp.ne', Real.rpow_one] at hh
  exact hh

theorem poweredConvolution_concave [IsAlgClosed K] (χ : Character K)
    (hp : 0 < χ.pX) {a b : ℕ} (ha : 0 < a) (hb : 2 ≤ b) :
    poweredConvolution χ a (b - 1) + poweredConvolution χ a (b + 1) ≤
      2 * poweredConvolution χ a b := by
  obtain ⟨d, rfl⟩ : ∃ d, a = d + 1 := ⟨a - 1, by omega⟩
  obtain ⟨e, rfl, he⟩ : ∃ e, b = e + 1 ∧ 0 < e := ⟨b - 1, by omega, by omega⟩
  rw [show e + 1 - 1 = e by omega, show e + 1 + 1 = e + 2 by omega]
  have h := poweredConvolution_concavity_dims χ hp d e he
  linarith

/-- The middle branch is retained separately, giving the oriented coupled tripling inequality. -/
theorem poweredConvolution_tripling [IsAlgClosed K] (χ : Character K)
    (hp : 0 < χ.pX) {a h : ℕ} (ha : 0 < a) (hh : 0 < h) :
    2 * poweredConvolution χ a h + poweredConvolution χ.swap23Character a h ≤
      poweredConvolution χ a (3 * h + a - 1) := by
  have ht := sharedFirst_power_sum χ hp (Sector.branchFamily (K := K) a h)
    (Sector.branchFamily_nonzero (K := K) ha hh)
  rw [Fin.sum_univ_three, Sector.branchFamily_zero, Sector.branchFamily_one,
    Sector.branchFamily_two, Sector.value_leftTensor, Sector.value_middleTensor,
    Sector.value_rightTensor, Sector.value_sharedFirst_branchFamily] at ht
  have hu := Real.rpow_le_rpow (χ.nonneg _) (Sector.value_retained_le_source χ a h)
    (inv_nonneg.mpr hp.le)
  have hresult := ht.trans hu
  simp only [poweredConvolution, Character.swap23Character_value,
    Character.swap23Character_pX]
  change 2 * χ.value (convolution a h) ^ χ.pX⁻¹ +
    χ.value (Sector.exchangedConvolution a h) ^ χ.pX⁻¹ ≤
    χ.value (convolution a (3 * h + a - 1)) ^ χ.pX⁻¹
  simp only [Sector.source, Sector.sourceWidth] at hresult
  change χ.value (convolution a h) ^ χ.pX⁻¹ +
    χ.value (Sector.exchangedConvolution a h) ^ χ.pX⁻¹ +
    χ.value (convolution a h) ^ χ.pX⁻¹ ≤
    χ.value (convolution a (3 * h + a - 1)) ^ χ.pX⁻¹ at hresult
  linarith

end

end Lemmata.FockCircuits.Matrix.Profile
