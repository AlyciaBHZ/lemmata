module

public import Lemmata.FockCircuits.Matrix.Profile.ReplicationEvaluation

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Profile.Replication

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The carry has one higher parameter degree than the diagonal remainder product. -/
theorem filtered_block_product (P u v : K[X]) (hP : P.Monic)
    (hq : 0 < P.natDegree) {r s a b : ℕ} (ha : a < r) (hb : b < s)
    (c : ℕ) (x : K) (hu : u.natDegree < P.natDegree)
    (hv : v.natDegree < P.natDegree) (hx : P.eval x = 0) :
    X ^ ((r - 1 - a) + (s - 1 - b) + c) *
        C (blockEvaluation P hP c x ((u * P ^ a) * (v * P ^ b))) =
      X ^ (r + s - 2) * C (if a + b = c then u.eval x * v.eval x else 0) +
        X ^ (r + s - 1) * C (if a + b + 1 = c then (u * v /ₘ P).eval x else 0) := by
  rw [blockEvaluation_product P u v hP hq a b c x hu hv hx]
  by_cases hzero : a + b = c
  · have hone : a + b + 1 ≠ c := by omega
    have he : (r - 1 - a) + (s - 1 - b) + c = r + s - 2 := by omega
    simp only [if_pos hzero, if_neg hone, add_zero, map_zero, mul_zero, he]
  · by_cases hone : a + b + 1 = c
    · have he : (r - 1 - a) + (s - 1 - b) + c = r + s - 1 := by omega
      simp only [if_neg hzero, if_pos hone, zero_add, map_zero, mul_zero, he]
    · simp only [if_neg hzero, if_neg hone, add_zero, map_zero, mul_zero]

end

end Lemmata.FockCircuits.Matrix.Profile.Replication
