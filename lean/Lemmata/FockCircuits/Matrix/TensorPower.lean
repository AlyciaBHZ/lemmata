module

public import Lemmata.FockCircuits.Matrix.SpectralPower

public section

set_option autoImplicit false

@[expose] section

namespace Lemmata.FockCircuits.Matrix

open scoped BigOperators
open Foundation
open Spectral TensorSemiring

noncomputable section

variable {K X Y Z : Type*} [Field K]
variable [Fintype X] [Fintype Y] [Fintype Z]

def splitPowerIndex (X : Type*) (n : ℕ) : (Fin (n + 1) → X) ≃ X × (Fin n → X) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv x := rfl

theorem classOf_power_zero (T : Tensor K X Y Z) :
    classOf (Tensor.power T 0) = 1 := by
  classical
  change classOf (Tensor.power T 0) = classOf (fun (_ _ _ : PUnit.{1}) => (1 : K))
  apply classOf_eq_of_reindex (Equiv.equivPUnit (Fin 0 → X))
    (Equiv.equivPUnit (Fin 0 → Y)) (Equiv.equivPUnit (Fin 0 → Z))
  funext x y z
  simp [Tensor.pullback, Tensor.power]

theorem classOf_power_succ (T : Tensor K X Y Z) (n : ℕ) :
    classOf (Tensor.power T (n + 1)) = classOf T * classOf (Tensor.power T n) := by
  rw [← classOf_product]
  apply classOf_eq_of_reindex (splitPowerIndex X n)
    (splitPowerIndex Y n) (splitPowerIndex Z n)
  funext x y z
  change T (x 0) (y 0) (z 0) *
    (∏ i : Fin n, T (x i.succ) (y i.succ) (z i.succ)) =
    ∏ i : Fin (n + 1), T (x i) (y i) (z i)
  exact (Fin.prod_univ_succ (fun i : Fin (n + 1) => T (x i) (y i) (z i))).symm

theorem classOf_power (T : Tensor K X Y Z) (n : ℕ) :
    classOf (Tensor.power T n) = classOf T ^ n := by
  induction n with
  | zero => exact classOf_power_zero T
  | succ n ih => rw [classOf_power_succ, ih, pow_succ']

/-- The spectral bound yields actual coefficient arrays for a finite exact power decomposition. -/
theorem exists_coefficient_power_rank (T : Tensor K X Y Z) {B ρ : ℝ}
    (hB : 0 ≤ B)
    (h : ∀ χ : TensorClass K →+* ℝ, Monotone χ → χ (classOf T) ≤ B)
    (hρ : B < ρ) :
    ∃ n r : ℕ, 0 < n ∧ Tensor.RankAtMost (Tensor.power T n) r ∧ (r : ℝ) < ρ ^ n := by
  obtain ⟨n, hn, hr⟩ := finite_power_bound (classOf T) hB h hρ
  rw [← classOf_power T n, rank_classOf] at hr
  exact ⟨n, Spectral.exactRank (Tensor.power T n), hn,
    Spectral.exactRank_spec (Tensor.power T n), hr⟩

end

end Lemmata.FockCircuits.Matrix
