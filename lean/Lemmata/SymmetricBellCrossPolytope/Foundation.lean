module

/- Copyright (c) 2026 Haobo Ma and Wenlin Zhang.
   SPDX-License-Identifier: CC-BY-4.0
   Adapted from the published Trureturing proof; see the entry prose for provenance. -/

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.Basic.Real.Sign
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate RealInnerProductSpace InnerProductSpace

namespace Lemmata.SymmetricBellCrossPolytope

/-- The primitive antiperiodic phase used in the sign-sum argument. -/
def zeta (d : ℕ) : ℂ := Complex.exp (Real.pi * Complex.I / d)

/-- A finite signal evaluated at a complex phase. -/
def finiteSignal {N : ℕ} (f : Fin N → ℂ) (z : ℂ) : ℂ :=
  ∑ n, f n * z ^ (n : ℕ)

/-- The coordinate description of a cross-polytope. -/
def crossHull {n : ℕ} (I : Finset (Fin n)) : Set (Fin n → ℝ) :=
  convexHull ℝ {x | ∃ j ∈ I, x = Pi.single j 1 ∨ x = -Pi.single j 1}

/-- Nested tuple indices, used only to reindex a finite sum. -/
def TensorTowerIndex (ι : Type*) : ℕ → Type _
  | 0 => ι
  | n+1 => ι × TensorTowerIndex ι n

/-- The canonical equivalence between nested tuples and finite functions. -/
def tensorTowerTupleEquiv (ι : Type*) : (n : ℕ) → TensorTowerIndex ι n ≃ (Fin (n+1) → ι)
  | 0 => (Equiv.funUnique (Fin 1) ι).symm
  | n+1 => (Equiv.prodCongr (Equiv.refl ι) (tensorTowerTupleEquiv ι n)).trans
      (Fin.consEquiv (fun _ : Fin (n+2) => ι))

namespace CosineBound
private lemma abs_cos_sum_periodic (d : ℕ) (hd : 0 < d) :
    Function.Periodic (fun s : ℝ => ∑ y ∈ Finset.range d,
      |Real.cos (s + Real.pi / d * y)|) (Real.pi / d) := by
  intro s
  change (∑ y ∈ Finset.range d, |Real.cos (s + Real.pi / d + Real.pi / d * y)|) = _
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hend : |Real.cos (s + Real.pi / d * d)| = |Real.cos s| := by
    rw [div_mul_cancel₀ _ hdR, Real.cos_add_pi, abs_neg]
  have hshift : (∑ y ∈ Finset.range d, |Real.cos (s + Real.pi / d + Real.pi / d * y)|) =
      ∑ y ∈ Finset.range d, |Real.cos (s + Real.pi / d * (y + 1))| := by
    apply Finset.sum_congr rfl
    intro y hy
    congr 2
    ring
  rw [hshift]
  have h := Finset.sum_range_succ' (fun y : ℕ => |Real.cos (s + Real.pi / d * y)|) d
  rw [Finset.sum_range_succ, hend] at h
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, add_zero] at h
  exact (add_right_cancel h).symm

lemma abs_cos_sum_le (d : ℕ) (hd : 2 ≤ d) (s : ℝ) :
    ∑ y ∈ Finset.range d, |Real.cos (s + Real.pi / d * y)| ≤
      1 / Real.sin (Real.pi / (2 * (d : ℝ))) := by
  have hd0 : 0 < d := by omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd0
  have ha : 0 < Real.pi / (d : ℝ) := div_pos Real.pi_pos hdR
  obtain ⟨k, hk, _⟩ := existsUnique_sub_zsmul_mem_Ico ha s (-(Real.pi / 2))
  let t := s - k • (Real.pi / (d : ℝ))
  have ht : t ∈ Set.Ico (-(Real.pi / 2)) (-(Real.pi / 2) + Real.pi / d) := hk
  rw [← (abs_cos_sum_periodic d hd0).sub_zsmul_eq k]
  change (∑ y ∈ Finset.range d, |Real.cos (t + Real.pi / d * y)|) ≤ _
  have hcos : ∀ y ∈ Finset.range d, 0 ≤ Real.cos (t + Real.pi / d * y) := by
    intro y hy
    have hyR : (y : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast Finset.mem_range.mp hy
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have : 0 ≤ Real.pi / d * (y : ℝ) := mul_nonneg ha.le (Nat.cast_nonneg y)
      linarith [ht.1]
    · have hprod := mul_le_mul_of_nonneg_left hyR ha.le
      have hcancel : Real.pi / d * d = Real.pi := div_mul_cancel₀ _ hdR.ne'
      nlinarith [ht.2]
  rw [Finset.sum_congr rfl (fun y hy => abs_of_nonneg (hcos y hy))]
  have hsum := Real.sin_mul_sum_cos d (Real.pi / d) t
  have horder : (∑ y ∈ Finset.range d, Real.cos (Real.pi / d * y + t)) =
      ∑ y ∈ Finset.range d, Real.cos (t + Real.pi / d * y) := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [add_comm]
  rw [horder] at hsum
  have harg : (d : ℝ) * (Real.pi / d) / 2 = Real.pi / 2 := by
    field_simp
  have hhalf : Real.pi / (d : ℝ) / 2 = Real.pi / (2 * d) := by ring
  rw [harg, Real.sin_pi_div_two, one_mul, hhalf] at hsum
  have hspos : 0 < Real.sin (Real.pi / (2 * (d : ℝ))) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have htwo : 1 < 2 * (d : ℝ) := by exact_mod_cast (show 1 < 2 * d by omega)
      exact (div_lt_self Real.pi_pos htwo)
  apply (le_div_iff₀ hspos).mpr
  rw [mul_comm]
  rw [hsum]
  exact Real.cos_le_one _


end CosineBound

end Lemmata.SymmetricBellCrossPolytope
