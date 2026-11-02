module

public import Lemmata.FockCircuits.CrossingPadding

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lemmata.FockCircuits.CrossingBounds

open Filter CrossingAlgorithms
open scoped Topology

noncomputable section

variable {R X O ρ J K : Type*} [CommRing R] [Fintype ρ] [Fintype J] [Fintype K]

theorem size_crossing_compile_le (sign : R) (bank : CircuitFamily R X O)
    (sa sb sc sd : ρ × J → O) (sy : J × K → O) (u : J × K → X)
    (p : AllOrders R ρ J K) {t b : ℝ} (hp : p.Bounded t)
    (hbank : (bank.size : ℝ) ≤ b * t)
    (hslots : ((Fintype.card J * Fintype.card K : ℕ) : ℝ) ≤ t) :
    ((CrossingCircuit.compile sign bank sa sb sc sd sy u p.abc p.cba p.cab p.bac).size : ℝ) ≤
      (b + 8) * t := by
  rw [CrossingCircuit.size_compile]
  push_cast
  rcases hp with ⟨hABC, _, hBAC, _, hCAB, hCBA⟩
  have hslots' : (Fintype.card J : ℝ) * Fintype.card K ≤ t := by
    simpa only [Nat.cast_mul] using hslots
  linarith

theorem cutoff_overhead_exponent (C : ℕ) (H E : ℕ → ℕ)
    (h : Tendsto (fun n : ℕ => Real.log (((H n + E n + 1 : ℕ) : ℝ) ^ 3) /
      Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log (((C + 8) * (H n + E n + 1) ^ 3 : ℕ) : ℝ) /
      Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun n : ℕ => Real.log ((C + 8 : ℕ) : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  have hpow : Tendsto (fun n : ℕ => Real.log (((H n + E n + 1) ^ 3 : ℕ) : ℝ) /
      Real.log (n : ℝ)) atTop (𝓝 0) := by simpa only [Nat.cast_pow] using h
  simpa only [zero_add] using log_nat_product_limit (fun _ : ℕ => C + 8)
    (fun n => (H n + E n + 1) ^ 3) 0 0
    (Eventually.of_forall fun _ => by omega)
    (Eventually.of_forall fun _ => pow_ne_zero _ (by omega)) hconst hpow

/-- Fixed constants and the cubic logarithmic overhead are absorbed in any positive exponent slack. -/
theorem eventually_cost_bound (C : ℕ) (H E cost : ℕ → ℕ) (L eps : ℝ) (heps : 0 < eps)
    (hoverhead : Tendsto (fun n : ℕ => Real.log (((H n + E n + 1 : ℕ) : ℝ) ^ 3) /
      Real.log (n : ℝ)) atTop (𝓝 0))
    (hcost : ∀ᶠ n : ℕ in atTop,
      (cost n : ℝ) ≤ ((C + 8 : ℕ) : ℝ) * ((H n + E n + 1 : ℕ) : ℝ) ^ 3 * (n : ℝ) ^ L) :
    ∀ᶠ n : ℕ in atTop, (cost n : ℝ) ≤ (n : ℝ) ^ (L + eps) := by
  have hpos : ∀ᶠ n : ℕ in atTop, (C + 8) * (H n + E n + 1) ^ 3 ≠ 0 :=
    Eventually.of_forall fun _ => Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  have hO := eventually_le_rpow_of_log_limit (fun n => (C + 8) * (H n + E n + 1) ^ 3)
    0 hpos (cutoff_overhead_exponent C H E hoverhead) eps heps
  filter_upwards [hcost, hO, eventually_gt_atTop (0 : ℕ)] with n hn hOn hnpos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hOn' : ((C + 8 : ℕ) : ℝ) * ((H n + E n + 1 : ℕ) : ℝ) ^ 3 ≤
      (n : ℝ) ^ eps := by simpa only [Nat.cast_mul, Nat.cast_pow, zero_add] using hOn
  calc
    (cost n : ℝ) ≤ ((C + 8 : ℕ) : ℝ) * ((H n + E n + 1 : ℕ) : ℝ) ^ 3 * (n : ℝ) ^ L := hn
    _ ≤ (n : ℝ) ^ eps * (n : ℝ) ^ L :=
      mul_le_mul_of_nonneg_right hOn' (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ (L + eps) := by rw [← Real.rpow_add hnR, add_comm]

end

end Lemmata.FockCircuits.CrossingBounds
