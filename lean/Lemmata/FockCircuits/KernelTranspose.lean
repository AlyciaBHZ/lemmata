module

public import Lemmata.FockCircuits.KernelStages
public import Lemmata.FockCircuits.ScalarAdjoints

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.KernelTranspose

open KernelRectangle KernelStages ScalarAdjoints
open scoped BigOperators

noncomputable section

variable {R D E M : Type*} [CommRing R] [Fintype D] [DecidableEq D]
  [AddCommGroup M] [Module R M]

def retype {a b : D → D → R} (ta : ScalarTransposeAlgorithm R D D a) (h : a = b) :
    ScalarTransposeAlgorithm R D D b where
  circuit := ta.circuit
  correct := by simpa only [← h] using ta.correct

@[simp] theorem size_retype {a b : D → D → R}
    (ta : ScalarTransposeAlgorithm R D D a) (h : a = b) : (retype ta h).size = ta.size := rfl

theorem exists_sparse_transpose (b : Module.Basis E R M) (index : D → E)
    (hinj : Function.Injective index) (T : M →ₗ[R] M)
    (hsparse : ∀ j : D, ∃ e : E, ∃ c : R, T (b (index j)) = b (index j) + c • b e) :
    ∃ ta : ScalarTransposeAlgorithm R D D
      (coefficientMatrix b index ((projection b index).comp T)),
      ta.size = 2 * Fintype.card D := by
  classical
  have hcol (j : D) : ∃ k : D, ∃ c : R,
      ((projection b index).comp T) (b (index j)) = b (index j) + c • b (index k) := by
    obtain ⟨e, c, he⟩ := hsparse j
    by_cases hmem : ∃ k : D, index k = e
    · obtain ⟨k, hk⟩ := hmem
      exact ⟨k, c, by simp only [LinearMap.comp_apply, he, map_add, map_smul, ← hk,
        projection_basis b index hinj]⟩
    · have hz : projection b index (b e) = 0 := by
        apply projection_basis_outside
        intro k hk
        exact hmem ⟨k, hk.symm⟩
      exact ⟨j, 0, by simp only [LinearMap.comp_apply, he, map_add, map_smul,
        projection_basis b index hinj, hz, smul_zero, add_zero, zero_smul]⟩
  choose target a hc using hcol
  let ta : ScalarTransposeAlgorithm R D D
      (coefficientMatrix b index ((projection b index).comp T)) :=
    ScalarTransposeAlgorithm.ofAdjoint
      (SparseCircuit.scatter (inputs D) target a) (SparseCircuit.gather (inputs D) target a)
      (by
        intro i
        change (SparseCircuit.scatter (inputs D) target a).eval
          (algebraMap R (FreeAlgebra R D)) (FreeAlgebra.ι R) i = _
        rw [SparseCircuit.scatter_basis_matrix b index hinj ((projection b index).comp T)
          (inputs D) target a hc (FreeAlgebra.ι R) i]
        simp only [eval_inputs]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Algebra.smul_def]
        exact (Algebra.commutes
          (coefficientMatrix b index ((projection b index).comp T) i j)
          (FreeAlgebra.ι R j)).symm)
      (by
        intro x y
        simpa only [eval_inputs] using
          SparseCircuit.scatter_gather_adjoint (inputs D) (inputs D) target a x y)
  exact ⟨ta, by
    change (SparseCircuit.gather (inputs D) target a).size = _
    rw [SparseCircuit.size_gather, size_inputs, zero_add]⟩

theorem exists_stages_transpose (b : Module.Basis E R M) (index : D → E)
    (hinj : Function.Injective index) (steps : List (M →ₗ[R] M))
    (hsparse : ∀ T ∈ steps, ∀ j : D, ∃ e : E, ∃ c : R,
      T (b (index j)) = b (index j) + c • b e) :
    ∃ ta : ScalarTransposeAlgorithm R D D
      (coefficientMatrix b index (maskedSteps (projection b index) steps)),
      ta.size = 2 * Fintype.card D * steps.length := by
  classical
  induction steps with
  | nil =>
    have hmat : (fun o i : D => if i = o then (1 : R) else 0) =
        coefficientMatrix b index (LinearMap.id : M →ₗ[R] M) := by
      funext i j
      simp [coefficientMatrix, Finsupp.single_apply, hinj.eq_iff]
    refine ⟨retype (injectionTranspose (R := R) (Function.Embedding.refl D)) hmat, ?_⟩
    change (injectionTranspose (R := R) (Function.Embedding.refl D)).size = 0
    exact size_injectionTranspose _
  | cons T rest ih =>
    obtain ⟨tr, htr⟩ := ih (fun S hS => hsparse S (by simp [hS]))
    obtain ⟨tt, htt⟩ := exists_sparse_transpose b index hinj T (hsparse T (by simp))
    have hmat :
        (fun p i => ∑ o, coefficientMatrix b index (maskedSteps (projection b index) rest) o i *
          coefficientMatrix b index ((projection b index).comp T) p o) =
        coefficientMatrix b index (maskedSteps (projection b index) (T :: rest)) := by
      funext p i
      simpa only [maskedSteps, LinearMap.comp_assoc] using
        (coefficientMatrix_comp_projection b index (maskedSteps (projection b index) rest)
          ((projection b index).comp T) p i).symm
    refine ⟨retype (compose tr tt) hmat, ?_⟩
    rw [size_retype, size_compose, htr, htt, List.length_cons]
    ring

def stacked {I O : Type*} [Fintype I] [Fintype O] (W : ℕ)
    (a : Fin W → O → I → R)
    (ta : ∀ r : Fin W, ScalarTransposeAlgorithm R I O (a r)) :
    ScalarTransposeAlgorithm R I (Fin W × O) (fun o i => a o.1 o.2 i) where
  circuit :=
    let bank := Matrix.CircuitBuilders.parallelFin W
      (fun r => (ta r).circuit.mapInputs (fun o => (r,o)))
    bank.substitute (Matrix.CircuitBuilders.linearFamily (fun (_ : I) (_ : Fin W) => (1 : R))
      (fun i r => (r,i)))
  correct := by
    intro i
    change ((Matrix.CircuitBuilders.parallelFin W
      (fun r => (ta r).circuit.mapInputs (fun o => (r,o)))).substitute
        (Matrix.CircuitBuilders.linearFamily (fun (_ : I) (_ : Fin W) => (1 : R))
          (fun i r => (r,i)))).polynomial i = _
    rw [CircuitFamily.polynomial_substitute]
    have hsum : (Matrix.CircuitBuilders.linearFamily (fun (_ : I) (_ : Fin W) => (1 : R))
        (fun i r => (r,i))).polynomial i = ∑ r : Fin W, FreeAlgebra.ι R (r,i) := by
      change (Matrix.CircuitBuilders.linearFamily _ _).eval
        (algebraMap R (FreeAlgebra R (Fin W × I))) (FreeAlgebra.ι R) i = _
      simp only [Matrix.CircuitBuilders.eval_linearFamily, one_smul]
    rw [hsum]
    simp only [map_sum, FreeAlgebra.lift_ι_apply]
    change (∑ r : Fin W, (Matrix.CircuitBuilders.parallelFin W
      (fun r => (ta r).circuit.mapInputs (fun o => (r,o)))).polynomial (r,i)) = _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro r hr
    change (Matrix.CircuitBuilders.parallelFin W
      (fun r => (ta r).circuit.mapInputs (fun o => (r,o)))).eval
        (algebraMap R (FreeAlgebra R (Fin W × O))) (FreeAlgebra.ι R) (r,i) = _
    rw [Matrix.CircuitBuilders.eval_parallelFin, CircuitFamily.eval_mapInputs]
    change (ta r).circuit.eval (algebraMap R (FreeAlgebra R (Fin W × O)))
      (fun o => FreeAlgebra.ι R (r,o)) i = _
    rw [← CircuitFamily.polynomial_lift, (ta r).correct]
    simp only [map_sum, map_smul, FreeAlgebra.lift_ι_apply]

theorem size_stacked {I O : Type*} [Fintype I] [Fintype O] (W : ℕ)
    (a : Fin W → O → I → R)
    (ta : ∀ r : Fin W, ScalarTransposeAlgorithm R I O (a r)) :
    (stacked W a ta).size = (∑ r : Fin W, (ta r).size) + 2*W*Fintype.card I := by
  simp only [stacked, ScalarTransposeAlgorithm.size, CircuitFamily.size_substitute,
    Matrix.CircuitBuilders.size_parallelFin, CircuitFamily.size_mapInputs,
    Matrix.CircuitBuilders.size_linearFamily, Fintype.card_fin]

end

end Lemmata.FockCircuits.KernelTranspose
