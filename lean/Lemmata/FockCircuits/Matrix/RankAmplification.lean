module

public import Lemmata.FockCircuits.Matrix.ExactBlocks
public import Lemmata.FockCircuits.Matrix.Profile.PolynomialOverhead

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix

open Foundation

noncomputable section

variable {F X Y Z : Type*} [Field F]

/-- A fixed descent overhead is absorbed in one sufficiently large exact coefficient block. -/
theorem amplify_rank_seed (T : Tensor F X Y Z) {r d : ℕ} (hd : 0 < d)
    (hblocks : ∀ n, Tensor.RankAtMost (Tensor.power T n) (r ^ n * d * d))
    {ρ : ℝ} (hr : (r : ℝ) < ρ) :
    ∃ n k : ℕ, 0 < n ∧ Tensor.RankAtMost (Tensor.power T n) k ∧ (k : ℝ) < ρ ^ n := by
  have hex : ∃ n : ℕ, 0 < n ∧ ((r ^ n * d * d : ℕ) : ℝ) < ρ ^ n := by
    by_contra! h
    have hbad : ρ ≤ (r : ℝ) :=
      Spectral.le_of_pow_le_const_mul_pow (Nat.cast_nonneg r) (C := (d : ℝ) * d) (fun n => by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp only [pow_zero, mul_one]
          have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
          nlinarith
        · have hh := h n hn
          simpa only [Nat.cast_mul, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm] using hh)
    exact hr.not_ge hbad
  obtain ⟨n, hn, hlt⟩ := hex
  exact ⟨n, r ^ n * d * d, hn, hblocks n, hlt⟩

theorem matrix_iterated_power_rank {A B C : Type*}
    [DecidableEq A] [DecidableEq B] [DecidableEq C] {N n r : ℕ}
    (h : Tensor.RankAtMost
      (Tensor.power (Tensor.power (Tensor.matrixCoefficients (K := F) A B C) N) n) r) :
    Tensor.RankAtMost (Tensor.matrixCoefficients (K := F)
      (Fin n → Fin N → A) (Fin n → Fin N → B) (Fin n → Fin N → C)) r := by
  let fx := fun x : (Fin n → Fin N → A) × (Fin n → Fin N → B) =>
    fun i j => (x.1 i j, x.2 i j)
  let fy := fun y : (Fin n → Fin N → B) × (Fin n → Fin N → C) =>
    fun i j => (y.1 i j, y.2 i j)
  let fz := fun z : (Fin n → Fin N → C) × (Fin n → Fin N → A) =>
    fun i j => (z.1 i j, z.2 i j)
  have hh := h.pullback fx fy fz
  have heq : Tensor.pullback fx fy fz
      (Tensor.power (Tensor.power (Tensor.matrixCoefficients (K := F) A B C) N) n) =
      Tensor.matrixCoefficients (K := F)
        (Fin n → Fin N → A) (Fin n → Fin N → B) (Fin n → Fin N → C) := by
    funext x y z
    simp only [Tensor.pullback, fx, fy, fz, Tensor.power, Tensor.matrixCoefficients,
      Fintype.prod_boole, forall_and, ← funext_iff]
  rwa [heq] at hh

end

end Lemmata.FockCircuits.Matrix
