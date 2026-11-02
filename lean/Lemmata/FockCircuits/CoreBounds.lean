module

public import Lemmata.FockCircuits.CrossingBounds
public import Lemmata.FockCircuits.Duality

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lemmata.FockCircuits.CoreBounds

open FiniteIdentity CrossingAlgorithms CrossingPadding Filter Exponent
open scoped Topology

noncomputable section

def matrixCost {R A B C : Type*} [CommSemiring R] [Fintype A] [Fintype B] [Fintype C]
    (p : AllOrders R A B C) : ℕ :=
  p.abc.size + p.acb.size + p.bac.size + p.bca.size + p.cab.size + p.cba.size

theorem uniform_core_bound (R : Type*) [Field R] {X : ℕ → Type*}
    (P : ∀ n, FreeAlgebra R (X n)) (C : ℕ)
    (hfinite : ∀ (n H E W : ℕ) (B : Fin n ↪ Index (H + E)),
      0 < W → W ≤ 2 * H → (∀ i, doubledEnergy (B i).val = W) →
      ∀ p : AllOrders R (Fin (2 * H) × ↥(fullCutoff (H + E)))
          ↥(fullCutoff E) (Fin (batchCount n (stateCount E))),
        ∃ s : ℕ, HasCircuit (P n) s ∧
          s ≤ C * (H + E + 1)^3 * stateCount (H + E) * stateCount E + matrixCost p +
            9 * (stateCount E * batchCount n (stateCount E)))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (P n) s ∧ (s : ℝ) ≤ K * (n : ℝ) ^ (gamma + eps) := by
  classical
  obtain ⟨padding, hpadding, halg, hoverhead⟩ :=
    eventually_exterior_algorithms R (eps / 2) (by linarith)
  let H := ceilLogEnergy countingConstant (1 + padding)
  let E := floorLogEnergy countingConstant optimalInput
  let L : ℝ := gamma + eps / 2
  let bound (n : ℕ) : ℝ :=
    ((C + 15 : ℕ) : ℝ) * ((H n + E n + 1 : ℕ) : ℝ) ^ 3 * (n : ℝ) ^ L
  have hcost : ∀ᶠ n : ℕ in atTop, ∃ s : ℕ, HasCircuit (P n) s ∧ (s : ℝ) ≤ bound n := by
    filter_upwards [halg] with n hn
    rcases hn with ⟨hH, hcapacity, p, hp, harea, _, hfinal⟩
    obtain ⟨W, B, hW, hWH, hBinj, hBW, _⟩ :=
      exists_dual_family R (H n) (H n + E n) n hH (by omega) hcapacity
    obtain ⟨s, hs, hsize⟩ := hfinite n (H n) (E n) W ⟨B, hBinj⟩ hW hWH hBW p
    let t : ℝ := (n : ℝ) ^ L
    let o : ℝ := ((H n + E n + 1 : ℕ) : ℝ) ^ 3
    have ht : 0 ≤ t := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have ho : 1 ≤ o := one_le_pow₀ (by exact_mod_cast (show 1 ≤ H n + E n + 1 by omega))
    have hareaNat : stateCount (H n + E n) * stateCount (E n) ≤
        (2 * H n * stateCount (H n + E n)) * stateCount (E n) := by
      have hmul := Nat.mul_le_mul_left (stateCount (H n + E n) * stateCount (E n))
        (by omega : 1 ≤ 2 * H n)
      simpa only [mul_one, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
    have harea' : ((stateCount (H n + E n) * stateCount (E n) : ℕ) : ℝ) ≤ t :=
      (Nat.cast_le.mpr hareaNat).trans harea
    have hbank : ((C * (H n + E n + 1)^3 * stateCount (H n + E n) * stateCount (E n) : ℕ) : ℝ) ≤
        (C : ℝ) * o * t := by
      simpa only [Nat.cast_mul, Nat.cast_pow, o, mul_assoc] using
        mul_le_mul_of_nonneg_left harea' (mul_nonneg (Nat.cast_nonneg C) (zero_le_one.trans ho))
    have hmatrix : (matrixCost p : ℝ) ≤ 6 * t := by
      rcases hp with ⟨h1,h2,h3,h4,h5,h6⟩
      simp only [matrixCost, Nat.cast_add]
      change (p.abc.size : ℝ) ≤ t at h1
      change (p.acb.size : ℝ) ≤ t at h2
      change (p.bac.size : ℝ) ≤ t at h3
      change (p.bca.size : ℝ) ≤ t at h4
      change (p.cab.size : ℝ) ≤ t at h5
      change (p.cba.size : ℝ) ≤ t at h6
      linarith
    have hsizeR : (s : ℝ) ≤
        ((C * (H n + E n + 1)^3 * stateCount (H n + E n) * stateCount (E n) : ℕ) : ℝ) +
          (matrixCost p : ℝ) + 9 * ((stateCount (E n) * batchCount n (stateCount (E n)) : ℕ) : ℝ) := by
      exact_mod_cast hsize
    have hsum : (s : ℝ) ≤ ((C : ℝ) * o + 15) * t := by
      change ((stateCount (E n) * batchCount n (stateCount (E n)) : ℕ) : ℝ) ≤ t at hfinal
      linarith
    have hfactor : (C : ℝ) * o + 15 ≤ ((C : ℝ) + 15) * o := by linarith
    refine ⟨s, hs, hsum.trans ?_⟩
    simpa only [bound, Nat.cast_add, Nat.cast_ofNat, o, t, mul_assoc] using
      mul_le_mul_of_nonneg_right hfactor ht
  let size (n : ℕ) : ℕ := if h : ∃ s : ℕ, HasCircuit (P n) s ∧ (s : ℝ) ≤ bound n
    then Classical.choose h else 0
  have hchosen : ∀ᶠ n : ℕ in atTop, HasCircuit (P n) (size n) ∧ (size n : ℝ) ≤ bound n :=
    hcost.mono fun n hn => by
      dsimp only [size]
      rw [dif_pos hn]
      exact Classical.choose_spec hn
  have hsizebound := CrossingBounds.eventually_cost_bound (C + 7) H E size L (eps / 2)
    (by linarith) hoverhead (by simpa only [bound, Nat.add_assoc] using hchosen.mono fun _ h => h.2)
  apply uniform_bound_of_eventually P (gamma + eps) (by unfold gamma; positivity)
  filter_upwards [hchosen, hsizebound] with n hn hbound
  refine ⟨size n, hn.1, ?_⟩
  convert hbound using 1 <;> dsimp [L] <;> congr 1 <;> ring

end

end Lemmata.FockCircuits.CoreBounds
