module

public import Lemmata.FockCircuits.Families
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.Families

open FiniteIdentity CrossingCircuit

/-- A finite crossing decomposition with integer coefficients in both permitted directions. -/
theorem integral_crossing_decomposition (H E n : ℕ) (hH : 0 < H)
    (hcapacity : 2 * H * n ≤ stateCount H - 1) :
    ∃ r ≤ 2 * H * stateCount (H + E),
      ∃ a b c d : Fin r → Fin n → Fin (stateCount E) → ℤ,
        ∀ (i k : Fin n) (j l : Fin (stateCount E)),
          (∑ s, (a s i j * b s k l + c s i l * d s k j)) =
            if i = k then (if j = l then 1 else 0) else 0 := by
  classical
  obtain ⟨W, B, hW, hWH, hBinj, hBW, _⟩ :=
    exists_dual_family ℤ H (H + E) n hH (by omega) hcapacity
  let B' : Fin n ↪ Index (H + E) := ⟨B, hBinj⟩
  let actionEquiv : Fin (stateCount E) ≃ ↥(fullCutoff E) :=
    (Finset.equivFin (fullCutoff E)).symm
  let action : Fin (stateCount E) ↪ Index (H + E) :=
    actionEquiv.toEmbedding.trans (cutoffEmbedding (by omega : E ≤ H + E))
  let middle := cutoffEmbedding (E := H + E) (L := H + E) le_rfl
  let a := coefficientA ℤ (dualFamily ℤ B') action middle (W := W)
  let b := coefficientB ℤ (bareFamily ℤ B') action middle (W := W)
  let c := coefficientC ℤ (dualFamily ℤ B') action middle (W := W)
  let d := coefficientD ℤ (bareFamily ℤ B') action middle (W := W)
  have hcoeff (i k : Fin n) (j l : Fin (stateCount E)) :
      (∑ s : Fin W × ↥(fullCutoff (H + E)),
        (a s i j * b s k l + (-(sigma W : ℤ) * c s i l) * d s k j)) =
          if i = k then (if j = l then 1 else 0) else 0 := by
    have h := family_coefficient_identity ℤ B' action middle hW hBW (E := E)
      (fun j => cutoffEmbedding_energy (by omega : E ≤ H + E) (actionEquiv j))
      (cutoffEmbedding_covers (H + E)) (by omega) i k j l
    simpa [a, b, c, d, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
      neg_mul, sub_eq_add_neg, Finset.sum_neg_distrib] using h
  let r := W * stateCount (H + E)
  let e : Fin r ≃ Fin W × ↥(fullCutoff (H + E)) :=
    (Fintype.equivFinOfCardEq (α := Fin W × ↥(fullCutoff (H + E))) (n := r) (by
      simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, stateCount, r])).symm
  refine ⟨r, Nat.mul_le_mul_right _ hWH,
    (fun s => a (e s)), (fun s => b (e s)),
    (fun s i j => -(sigma W : ℤ) * c (e s) i j), (fun s => d (e s)), ?_⟩
  intro i k j l
  exact (e.sum_comp (fun s => a s i j * b s k l +
    (-(sigma W : ℤ) * c s i l) * d s k j)).trans (hcoeff i k j l)

end Lemmata.FockCircuits.Families
