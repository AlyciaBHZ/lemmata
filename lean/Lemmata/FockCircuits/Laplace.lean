module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits

noncomputable def finiteLaplace (S : Finset ℕ) (q : ℕ → ℝ) (t : ℝ) : ℝ :=
  S.sum fun e => q e * Real.exp (-t * (e : ℝ))

noncomputable def finiteCumulative (S : Finset ℕ) (q : ℕ → ℝ) (H : ℝ) : ℝ :=
  S.sum fun e => if (e : ℝ) ≤ H then q e else 0

private theorem weighted_exp_le_three
    (x q s t u L H : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hst : s ≤ t) (htu : t ≤ u) :
    q * Real.exp (-t * x) ≤
      Real.exp ((u - t) * L) * (q * Real.exp (-u * x)) +
      Real.exp (-t * L) * (if x ≤ H then q else 0) +
      Real.exp (-(t - s) * H) * (q * Real.exp (-s * x)) := by
  have hlow : 0 ≤ Real.exp ((u - t) * L) * (q * Real.exp (-u * x)) :=
    mul_nonneg (Real.exp_nonneg _) (mul_nonneg hq (Real.exp_nonneg _))
  have hcut : 0 ≤ (if x ≤ H then q else 0) := by
    by_cases hx : x ≤ H
    · simpa [hx] using hq
    · simp [hx]
  have hmiddle : 0 ≤ Real.exp (-t * L) * (if x ≤ H then q else 0) :=
    mul_nonneg (Real.exp_nonneg _) hcut
  have hhigh : 0 ≤ Real.exp (-(t - s) * H) * (q * Real.exp (-s * x)) :=
    mul_nonneg (Real.exp_nonneg _) (mul_nonneg hq (Real.exp_nonneg _))
  by_cases hxL : x ≤ L
  · have hexp : -t * x ≤ (u - t) * L + -u * x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr htu) (sub_nonneg.mpr hxL)]
    have hbound :
        q * Real.exp (-t * x) ≤
          Real.exp ((u - t) * L) * (q * Real.exp (-u * x)) := by
      calc
        q * Real.exp (-t * x) ≤ q * Real.exp ((u - t) * L + -u * x) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hq
        _ = Real.exp ((u - t) * L) * (q * Real.exp (-u * x)) := by
          rw [Real.exp_add]
          ring
    linarith
  · by_cases hxH : x ≤ H
    · have hexp : -t * x ≤ -t * L := by
        nlinarith [mul_nonneg ht (sub_nonneg.mpr (le_of_not_ge hxL))]
      have hbound :
          q * Real.exp (-t * x) ≤
            Real.exp (-t * L) * (if x ≤ H then q else 0) := by
        rw [ite_eq_left hxH]
        calc
          q * Real.exp (-t * x) ≤ q * Real.exp (-t * L) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hq
          _ = Real.exp (-t * L) * q := mul_comm _ _
      linarith
    · have hexp : -t * x ≤ -(t - s) * H + -s * x := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hst)
          (sub_nonneg.mpr (le_of_not_ge hxH))]
      have hbound :
          q * Real.exp (-t * x) ≤
            Real.exp (-(t - s) * H) * (q * Real.exp (-s * x)) := by
        calc
          q * Real.exp (-t * x) ≤ q * Real.exp (-(t - s) * H + -s * x) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hq
          _ = Real.exp (-(t - s) * H) * (q * Real.exp (-s * x)) := by
            rw [Real.exp_add]
            ring
      linarith

theorem finiteLaplace_three_evaluations
    (S : Finset ℕ) (q : ℕ → ℝ) (s t u L H : ℝ)
    (hq : ∀ e ∈ S, 0 ≤ q e) (ht : 0 ≤ t)
    (hst : s ≤ t) (htu : t ≤ u) :
    finiteLaplace S q t -
        Real.exp ((u - t) * L) * finiteLaplace S q u -
        Real.exp (-(t - s) * H) * finiteLaplace S q s ≤
      Real.exp (-t * L) * finiteCumulative S q H := by
  have hsum := Finset.sum_le_sum fun (e : ℕ) (he : e ∈ S) =>
    weighted_exp_le_three (e : ℝ) (q e) s t u L H (hq e he) ht hst htu
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  dsimp [finiteLaplace, finiteCumulative]
  linarith

noncomputable def laplaceSeries (q : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' e : ℕ, q e * Real.exp (-t * (e : ℝ))

noncomputable def cumulativeWeight (q : ℕ → ℝ) (H : ℕ) : ℝ :=
  (Finset.range (H + 1)).sum q

theorem laplaceSeries_three_evaluations
    (q : ℕ → ℝ) (H : ℕ) (s t u L : ℝ)
    (hq : ∀ e, 0 ≤ q e) (ht : 0 ≤ t)
    (hst : s ≤ t) (htu : t ≤ u)
    (hsum_s : Summable fun e : ℕ => q e * Real.exp (-s * (e : ℝ)))
    (hsum_t : Summable fun e : ℕ => q e * Real.exp (-t * (e : ℝ)))
    (hsum_u : Summable fun e : ℕ => q e * Real.exp (-u * (e : ℝ))) :
    laplaceSeries q t -
        Real.exp ((u - t) * L) * laplaceSeries q u -
        Real.exp (-(t - s) * (H : ℝ)) * laplaceSeries q s ≤
      Real.exp (-t * L) * cumulativeWeight q H := by
  let qH : ℕ → ℝ := fun e => if e ≤ H then q e else 0
  have hzero : ∀ e ∉ Finset.range (H + 1), qH e = 0 := by
    intro e he
    have hnot : ¬e ≤ H := fun hle =>
      he (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
    simp only [qH, ite_eq_right hnot]
  have hsum_qH : Summable qH := summable_of_ne_finset_zero hzero
  have hqH_sum : (∑' e : ℕ, qH e) = cumulativeWeight q H := by
    rw [tsum_eq_sum (s := Finset.range (H + 1)) hzero]
    unfold cumulativeWeight
    apply Finset.sum_congr rfl
    intro e he
    simp only [qH, ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp he))]
  have hpoint (e : ℕ) :
      q e * Real.exp (-t * (e : ℝ)) ≤
        Real.exp ((u - t) * L) * (q e * Real.exp (-u * (e : ℝ))) +
        Real.exp (-t * L) * qH e +
        Real.exp (-(t - s) * (H : ℝ)) * (q e * Real.exp (-s * (e : ℝ))) := by
    simpa only [qH, Nat.cast_le] using
      weighted_exp_le_three (e : ℝ) (q e) s t u L (H : ℝ) (hq e) ht hst htu
  have hright :
      HasSum
        (fun e : ℕ =>
          Real.exp ((u - t) * L) * (q e * Real.exp (-u * (e : ℝ))) +
          Real.exp (-t * L) * qH e +
          Real.exp (-(t - s) * (H : ℝ)) * (q e * Real.exp (-s * (e : ℝ))))
        (Real.exp ((u - t) * L) * laplaceSeries q u +
          Real.exp (-t * L) * (∑' e : ℕ, qH e) +
          Real.exp (-(t - s) * (H : ℝ)) * laplaceSeries q s) := by
    exact ((hsum_u.hasSum.mul_left _).add (hsum_qH.hasSum.mul_left _)).add
      (hsum_s.hasSum.mul_left _)
  have hbound := hasSum_le hpoint hsum_t.hasSum hright
  rw [hqH_sum] at hbound
  change laplaceSeries q t ≤
    Real.exp ((u - t) * L) * laplaceSeries q u +
      Real.exp (-t * L) * cumulativeWeight q H +
      Real.exp (-(t - s) * (H : ℝ)) * laplaceSeries q s at hbound
  linarith

end Lemmata.FockCircuits
