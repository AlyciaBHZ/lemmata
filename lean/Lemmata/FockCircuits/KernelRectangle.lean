module

public import Lemmata.FockCircuits.KernelCoevaluation
public import Lemmata.FockCircuits.Partition
public import Lemmata.FockCircuits.SparseCircuit

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.KernelRectangle

noncomputable section

variable {R D E M X : Type*} [CommRing R] [Fintype D]
  [AddCommGroup M] [Module R M]

def projection (b : Module.Basis E R M) (index : D → E) : M →ₗ[R] M where
  toFun v := ∑ d, b.repr v (index d) • b (index d)
  map_add' x y := by
    simp only [map_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum, RingHom.id_apply]

@[simp] theorem projection_apply (b : Module.Basis E R M) (index : D → E) (v : M) :
    projection b index v = ∑ d, b.repr v (index d) • b (index d) := rfl

@[simp] theorem projection_basis (b : Module.Basis E R M) (index : D → E)
    (hinj : Function.Injective index) (d : D) :
    projection b index (b (index d)) = b (index d) := by
  classical
  simp only [projection_apply, Module.Basis.repr_self_apply, hinj.eq_iff]
  simp

theorem projection_basis_outside (b : Module.Basis E R M) (index : D → E)
    {e : E} (he : ∀ d, e ≠ index d) : projection b index (b e) = 0 := by
  classical
  simp [projection_apply, Module.Basis.repr_self_apply, he]

@[simp] theorem repr_projection (b : Module.Basis E R M) (index : D → E)
    (hinj : Function.Injective index) (v : M) (d : D) :
    b.repr (projection b index v) (index d) = b.repr v (index d) := by
  classical
  simp only [projection_apply, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self_apply, hinj.eq_iff]
  simp

theorem projection_idempotent (b : Module.Basis E R M) (index : D → E)
    (hinj : Function.Injective index) :
    (projection b index).comp (projection b index) = projection b index := by
  ext v
  change projection b index (projection b index v) = projection b index v
  rw [projection_apply]
  simpa only [repr_projection b index hinj] using (projection_apply b index v).symm

def coefficientMatrix (b : Module.Basis E R M) (index : D → E)
    (T : M →ₗ[R] M) (i j : D) : R := b.repr (T (b (index j))) (index i)

theorem coefficientMatrix_comp_projection (b : Module.Basis E R M) (index : D → E)
    (S T : M →ₗ[R] M) (i j : D) :
    coefficientMatrix b index (T.comp ((projection b index).comp S)) i j =
      ∑ k, coefficientMatrix b index S k j * coefficientMatrix b index T i k := by
  simp only [coefficientMatrix, LinearMap.comp_apply, projection_apply, map_sum, map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem coefficientMatrix_projection (b : Module.Basis E R M) (index : D → E)
    (hinj : Function.Injective index) (T : M →ₗ[R] M) :
    coefficientMatrix b index ((projection b index).comp T) = coefficientMatrix b index T := by
  funext i j
  exact repr_projection b index hinj _ _

theorem sum_mul_matrix {A : Type*} [Semiring A] [Algebra R A]
    (v : D → A) (S T : D → D → R) (i : D) :
    (∑ k, (∑ j, v j * algebraMap R A (S k j)) * algebraMap R A (T i k)) =
      ∑ j, v j * algebraMap R A (∑ k, S k j * T i k) := by
  simp only [Finset.sum_mul, map_sum, map_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

def Represents (b : Module.Basis E R M) (index : D → E)
    (bank p : CircuitFamily R X D) (T : M →ₗ[R] M) : Prop :=
  ∀ i, p.polynomial i = ∑ j, bank.polynomial j *
    algebraMap R (FreeAlgebra R X) (coefficientMatrix b index T i j)

theorem Represents.eval {b : Module.Basis E R M} {index : D → E}
    {bank p : CircuitFamily R X D} {T : M →ₗ[R] M}
    (hp : Represents b index bank p T)
    {A : Type*} [Semiring A] [Algebra R A] (x : X → A) (i : D) :
    p.eval (algebraMap R A) x i = ∑ j, bank.eval (algebraMap R A) x j *
      algebraMap R A (coefficientMatrix b index T i j) := by
  have h := congrArg (FreeAlgebra.lift R x) (hp i)
  simpa only [map_sum, map_mul, CircuitFamily.polynomial_lift, AlgHom.commutes] using h

theorem Represents.identity (b : Module.Basis E R M) (index : D → E)
    (hinj : Function.Injective index) (bank : CircuitFamily R X D) :
    Represents b index bank bank LinearMap.id := by
  classical
  intro i
  simp [coefficientMatrix, Finsupp.single_apply, hinj.eq_iff, eq_comm]

theorem Represents.comp {b : Module.Basis E R M} {index : D → E}
    {bank p q : CircuitFamily R X D} {S T : M →ₗ[R] M}
    (hp : Represents b index bank p S) (hq : Represents b index p q T) :
    Represents b index bank q (T.comp ((projection b index).comp S)) := by
  unfold Represents at hp hq ⊢
  intro i
  calc
    q.polynomial i = ∑ k, p.polynomial k *
        algebraMap R (FreeAlgebra R X) (coefficientMatrix b index T i k) := hq i
    _ = ∑ k, (∑ j, bank.polynomial j *
        algebraMap R (FreeAlgebra R X) (coefficientMatrix b index S k j)) *
        algebraMap R (FreeAlgebra R X) (coefficientMatrix b index T i k) := by simp_rw [hp]
    _ = ∑ j, bank.polynomial j * algebraMap R (FreeAlgebra R X)
        (∑ k, coefficientMatrix b index S k j * coefficientMatrix b index T i k) :=
      sum_mul_matrix _ _ _ _
    _ = _ := by simp only [coefficientMatrix_comp_projection]

theorem exists_projected_sparse_circuit (b : Module.Basis E R M) (index : D → E)
    (hinj : Function.Injective index) (S : M →ₗ[R] M) (bank : CircuitFamily R X D)
    (hsparse : ∀ j : D, ∃ e : E, ∃ c : R, S (b (index j)) = b (index j) + c • b e) :
    ∃ p : CircuitFamily R X D, p.size = bank.size + 2 * Fintype.card D ∧
      Represents b index bank p ((projection b index).comp S) := by
  classical
  have hcol (j : D) : ∃ k : D, ∃ c : R,
      ((projection b index).comp S) (b (index j)) = b (index j) + c • b (index k) := by
    obtain ⟨e, c, he⟩ := hsparse j
    by_cases hmem : ∃ k : D, index k = e
    · obtain ⟨k, hk⟩ := hmem
      refine ⟨k, c, ?_⟩
      simp only [LinearMap.comp_apply, he, map_add, map_smul, ← hk,
        projection_basis b index hinj]
    · refine ⟨j, 0, ?_⟩
      have hzero : projection b index (b e) = 0 := by
        apply projection_basis_outside
        intro k hk
        exact hmem ⟨k, hk.symm⟩
      simp only [LinearMap.comp_apply, he, map_add, map_smul,
        projection_basis b index hinj, hzero, smul_zero, add_zero, zero_smul]
  choose target c hc using hcol
  refine ⟨SparseCircuit.scatter bank target c, SparseCircuit.size_scatter _ _ _, ?_⟩
  intro i
  exact SparseCircuit.scatter_basis_matrix b index hinj ((projection b index).comp S)
    bank target c hc (FreeAlgebra.ι R) i

abbrev Index (U V : ℕ) := ↥(fullCutoff U) × ↥(fullCutoff V)

def basisIndex {U V : ℕ} (d : Index U V) : Finset (ℕ ⊕ₗ ℕ) :=
  FiniteIdentity.colourIndex d.1.val d.2.val

theorem basisIndex_injective (U V : ℕ) : Function.Injective (basisIndex (U := U) (V := V)) := by
  intro d e h
  have heq := (FiniteIdentity.colourIndex_eq_iff _ _ _ _).mp h
  exact Prod.ext (Subtype.ext heq.1) (Subtype.ext heq.2)

@[simp] theorem card_index (U V : ℕ) : Fintype.card (Index U V) = stateCount U * stateCount V := by
  simp only [Index, Fintype.card_prod, Fintype.card_coe, stateCount]

end

end Lemmata.FockCircuits.KernelRectangle
