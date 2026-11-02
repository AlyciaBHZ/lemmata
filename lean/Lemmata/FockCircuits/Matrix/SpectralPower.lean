module

public import Lemmata.TensorRank.Main
public import Lemmata.FockCircuits.Matrix.Tensor.Scalar

public section

set_option autoImplicit false

@[expose] section

namespace Lemmata.FockCircuits.Matrix

open Spectral TensorSemiring
open Lemmata.TensorRank.Spectrum

noncomputable section

variable {K : Type*} [Field K]

/-- The restriction order on arbitrary-field tensors is a Strassen preorder. -/
def tensorPreorder : StrassenPreorder (TensorClass K) where
  Rel := (· ≤ ·)
  refl := le_refl
  trans := le_trans
  zero_le := TensorSemiring.zero_le
  nat_iff := natCast_le_natCast_iff
  add := TensorSemiring.add_mono
  mul := TensorSemiring.mul_mono
  cofinal := fun a b hb => ⟨TensorSemiring.rank a, le_nat_mul_of_ne_zero a b hb⟩

theorem tensorPreorder_oneLeNonzero : (tensorPreorder (K := K)).OneLeNonzero :=
  fun _ ht => TensorSemiring.one_le_of_ne_zero ht

theorem tensorPreorder_rank (t : TensorClass K) :
    (tensorPreorder (K := K)).rank t = TensorSemiring.rank t := by
  let p := tensorPreorder (K := K)
  apply le_antisymm
  · exact (p.rank_le_iff t _).mpr (TensorSemiring.le_rank t)
  · have h := TensorSemiring.rank_mono (p.rel_rank t)
    simpa only [rank_natCast] using h

/-- A uniform character bound gives an exact finite tensor-power rank certificate with any positive slack. -/
theorem finite_power_bound (t : TensorClass K) {B ρ : ℝ} (hB : 0 ≤ B)
    (h : ∀ χ : TensorClass K →+* ℝ, Monotone χ → χ t ≤ B) (hρ : B < ρ) :
    ∃ n : ℕ, 0 < n ∧ (TensorSemiring.rank (t ^ n) : ℝ) < ρ ^ n := by
  let p := tensorPreorder (K := K)
  have hp : p.OneLeNonzero := tensorPreorder_oneLeNonzero
  have hbound : p.asymptoticRank t ≤ B := (p.asymptoticRank_le_iff hp t B).mpr
    (fun f => h f.val (fun _ _ hab => f.prop hab))
  have hlt : p.asymptoticRank t < ρ := hbound.trans_lt hρ
  obtain ⟨n, hn⟩ : ∃ n : ℕ,
      (p.rank (t ^ (n + 1)) : ℝ) ^ ((n + 1 : ℝ)⁻¹) < ρ := by
    by_contra! hnot
    exact (not_le_of_gt hlt) (le_ciInf hnot)
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  have hρpos : 0 < ρ := hB.trans_lt hρ
  have hh := (Real.rpow_inv_lt_iff_of_pos (Nat.cast_nonneg (p.rank (t ^ (n + 1))))
    hρpos.le (by positivity : (0 : ℝ) < n + 1)).mp hn
  change (((tensorPreorder (K := K)).rank (t ^ (n + 1))) : ℝ) < ρ ^ ((n : ℝ) + 1) at hh
  rw [tensorPreorder_rank, show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by simp,
    Real.rpow_natCast] at hh
  exact hh

end

end Lemmata.FockCircuits.Matrix
