module

/- Copyright (c) 2026 Haobo Ma and Wenlin Zhang.
   SPDX-License-Identifier: CC-BY-4.0
   Adapted from the published Trureturing proof; see the entry prose for provenance. -/

public import Lemmata.SymmetricBellCrossPolytope.Foundation

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate RealInnerProductSpace InnerProductSpace
open Set
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace Lemmata.SymmetricBellCrossPolytope



abbrev Tensor (N m : ℕ) := EuclideanSpace ℝ (Fin N → Fin m)
def normIdx (m : ℕ) (v : ℤ) : ℝ × ℕ := ((-1 : ℝ) ^ (v / (m : ℤ)), (v % (m : ℤ)).toNat)
def reduceIdx {m : ℕ} (x : Fin m) (v : ℤ) : ℝ × Fin m := ((normIdx m v).1, ⟨(normIdx m v).2, by
    have hm : (0 : ℤ) < m := by exact_mod_cast Nat.zero_lt_of_lt x.isLt
    have hlo := Int.emod_nonneg v hm.ne'; have hhi := Int.emod_lt_of_pos v hm; dsimp [normIdx]; exact (Int.toNat_lt_of_ne_zero (by omega)).mpr hhi⟩)
def gen1 {N m : ℕ} (x : Fin N → Fin m) : ℝ × (Fin N → Fin m) := (1, fun n => if h : 1 < N then x (Equiv.swap (⟨0, by omega⟩ : Fin N) ⟨1, h⟩ n) else x n)
def gen2 {N m : ℕ} (x : Fin N → Fin m) : ℝ × (Fin N → Fin m) := (1, fun n => x ((finRotate N).symm n))
def shiftParty {N m : ℕ} (x : Fin N → Fin m) (n : Fin N) : ℝ × Fin m := reduceIdx (x n) ((x n : ℤ) + if n.val = 0 then 1 else if n.val = 1 then -1 else 0)
def gen3 {N m : ℕ} (x : Fin N → Fin m) : ℝ × (Fin N → Fin m) := (∏ n, (shiftParty x n).1, fun n => (shiftParty x n).2)
def gen4 {N m : ℕ} (x : Fin N → Fin m) : ℝ × (Fin N → Fin m) := (∏ n, -(reduceIdx (x n) ((m : ℤ) - (x n : ℤ))).1, fun n => (reduceIdx (x n) ((m : ℤ) - (x n : ℤ))).2)
def gen {N m : ℕ} (i : Fin 4) : (Fin N → Fin m) → ℝ × (Fin N → Fin m) := ![gen1, gen2, gen3, gen4] i
def act {N m : ℕ} (g : (Fin N → Fin m) → ℝ × (Fin N → Fin m)) (p : Tensor N m) : Tensor N m := WithLp.toLp 2 (fun y => ∑ x, if (g x).2 = y then (g x).1 * p x else 0)
lemma act_add {N m : ℕ} (g : (Fin N → Fin m) → ℝ × (Fin N → Fin m)) (p q : Tensor N m) : act g (p + q) = act g p + act g q := by apply PiLp.ext; intro y; simp only [act, PiLp.add_apply, PiLp.toLp_apply]; simp_rw [mul_add, ite_add_zero]; exact Finset.sum_add_distrib
lemma act_smul {N m : ℕ} (g : (Fin N → Fin m) → ℝ × (Fin N → Fin m)) (c : ℝ) (p : Tensor N m) : act g (c • p) = c • act g p := by
  apply PiLp.ext; intro y; simp only [act, PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x hx
  split_ifs <;> ring
lemma act_zero {N m : ℕ} (g : (Fin N → Fin m) → ℝ × (Fin N → Fin m)) : act g (0 : Tensor N m) = 0 := by apply PiLp.ext; intro y; simp [act]
def symSub (N m : ℕ) : Submodule ℝ (Tensor N m) where
  carrier := {p | ∀ i : Fin 4, act (gen i) p = p}
  zero_mem' := fun _ => act_zero _
  add_mem' := by intro p q hp hq i; rw [act_add, hp i, hq i]
  smul_mem' := by   intro c p hp i; rw [act_smul, hp i]
def Gamma (N m : ℕ) : Tensor N m →L[ℝ] Tensor N m := (symSub N m).starProjection
def strategySet (N m : ℕ) : Set (Tensor N m) := {v | ∃ a : Fin N → Fin m → ℝ, (∀ n x, a n x = 1 ∨ a n x = -1) ∧ ∀ x, v x = ∏ n, a n (x n)}
def localPolytope (N m : ℕ) : Set (Tensor N m) := convexHull ℝ (strategySet N m)
def crossPolytope (k : ℕ) : Set (EuclideanSpace ℝ (Fin k)) := (EuclideanSpace.equiv (Fin k) ℝ).symm ''
    Lemmata.SymmetricBellCrossPolytope.crossHull Finset.univ
def claim : Prop := ∀ N m : ℕ, 3 ≤ N → 2 ≤ m →
  ∃ f : Tensor N m →ᵃ[ℝ] EuclideanSpace ℝ (Fin ((m + 1) / 2)),
    Set.InjOn f (Gamma N m '' localPolytope N m) ∧
      f '' (Gamma N m '' localPolytope N m) = crossPolytope ((m + 1) / 2)

/-- The concrete obstruction at three parties and seventeen inputs. -/
def Counterexample : Prop :=
  ¬ ∃ f : Tensor 3 17 →ᵃ[ℝ] EuclideanSpace ℝ (Fin 9),
    Set.InjOn f (Gamma 3 17 '' localPolytope 3 17) ∧
      f '' (Gamma 3 17 '' localPolytope 3 17) = crossPolytope 9

end Lemmata.SymmetricBellCrossPolytope
