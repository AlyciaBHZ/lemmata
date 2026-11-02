module

public import Lemmata.FockCircuits.KernelAlgorithm
public import Lemmata.FockCircuits.ScalarAdjoints

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lemmata.FockCircuits.SourceBanks

open FiniteIdentity KernelRectangle
open Lemmata.FockCircuits.Matrix

noncomputable section

variable {R X I D E M : Type*} [CommRing R] [Fintype I] [Fintype D]

def sourceBank (index : I ↪ D) (label : I → X) : CircuitFamily R X D :=
  CircuitBuilders.family (Function.extend index
    (fun i => CircuitBuilders.input (R := R) (label i)) (fun _ => CircuitBuilders.scalar 0))

theorem size_sourceBank (index : I ↪ D) (label : I → X) :
    (sourceBank (R := R) index label).size = 0 := by
  classical
  rw [sourceBank, CircuitBuilders.size_family]
  apply Finset.sum_eq_zero
  intro d hd
  by_cases h : ∃ i, index i = d
  · obtain ⟨i, rfl⟩ := h
    rw [index.injective.extend_apply]
    exact CircuitBuilders.size_input _
  · rw [Function.extend_apply' _ _ _ h]
    exact CircuitBuilders.size_scalar _

theorem polynomial_sourceBank (index : I ↪ D) (label : I → X) (d : D) :
    (sourceBank (R := R) index label).polynomial d =
      Function.extend index (fun i => FreeAlgebra.ι R (label i)) (fun _ => 0) d := by
  classical
  change (sourceBank index label).eval
    (algebraMap R (FreeAlgebra R X)) (FreeAlgebra.ι R) d = _
  rw [sourceBank, CircuitBuilders.eval_family]
  by_cases h : ∃ i, index i = d
  · obtain ⟨i, rfl⟩ := h
    rw [index.injective.extend_apply, index.injective.extend_apply]
    exact CircuitBuilders.eval_input _ _ _
  · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
    simp

theorem sourceBank_weighted_sum (index : I ↪ D) (label : I → X) (c : D → R) :
    (∑ d, (sourceBank (R := R) index label).polynomial d *
      algebraMap R (FreeAlgebra R X) (c d)) =
        ∑ i, FreeAlgebra.ι R (label i) * algebraMap R (FreeAlgebra R X) (c (index i)) := by
  classical
  symm
  apply Fintype.sum_of_injective index index.injective
  · intro d hd
    rw [polynomial_sourceBank, Function.extend_apply' _ _ _ hd, zero_mul]
  · intro i
    rw [polynomial_sourceBank, index.injective.extend_apply]

theorem represents_sourceBank [AddCommGroup M] [Module R M]
    (basis : Module.Basis E R M) (coordinates : D → E)
    (index : I ↪ D) (label : I → X) (p : CircuitFamily R X D) (T : M →ₗ[R] M)
    (hp : Represents basis coordinates (sourceBank index label) p T) (d : D) :
    p.polynomial d = ∑ i,
      coefficientMatrix basis coordinates T d (index i) • FreeAlgebra.ι R (label i) := by
  rw [hp d, sourceBank_weighted_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Algebra.smul_def]
  exact (Algebra.commutes (coefficientMatrix basis coordinates T d (index i))
    (FreeAlgebra.ι R (label i))).symm

def scaleOutputs (a : D → R) (p : CircuitFamily R X D) : CircuitFamily R X D :=
  p.substitute (ScalarAdjoints.diagonalCircuit a)

theorem size_scaleOutputs (a : D → R) (p : CircuitFamily R X D) :
    (scaleOutputs a p).size = p.size + Fintype.card D := by
  simp [scaleOutputs, ScalarAdjoints.diagonalCircuit]

theorem polynomial_scaleOutputs (a : D → R) (p : CircuitFamily R X D) (d : D) :
    (scaleOutputs a p).polynomial d = a d • p.polynomial d := by
  simp [scaleOutputs, CircuitFamily.polynomial_substitute, ScalarAdjoints.diagonalCircuit,
    CircuitFamily.polynomial, Algebra.smul_def]

def leftSource {L U V : ℕ} (B : I ↪ FiniteIdentity.Index L)
    (hB : ∀ i, doubledEnergy (B i).val ≤ 2 * U) : I ↪ KernelRectangle.Index U V where
  toFun i := (⟨(B i).val, mem_fullCutoff.mpr (hB i)⟩, ⟨∅, by simp [doubledEnergy]⟩)
  inj' i j h := B.injective (Subtype.ext
    (congrArg (fun d : KernelRectangle.Index U V => d.1.val) h))

def rightSource {L U V : ℕ} (B : I ↪ FiniteIdentity.Index L)
    (hB : ∀ i, doubledEnergy (B i).val ≤ 2 * V) : I ↪ KernelRectangle.Index U V where
  toFun i := (⟨∅, by simp [doubledEnergy]⟩, ⟨(B i).val, mem_fullCutoff.mpr (hB i)⟩)
  inj' i j h := B.injective (Subtype.ext
    (congrArg (fun d : KernelRectangle.Index U V => d.2.val) h))

theorem leftSource_basis {L U V : ℕ} (B : I ↪ FiniteIdentity.Index L)
    (hB : ∀ i, doubledEnergy (B i).val ≤ 2 * U) (i : I) :
    colourBasis R (basisIndex (leftSource (V := V) B hB i)) =
      leftInclusion R (Fock.basis R (B i).val) :=
  (leftInclusion_basis R (B i).val).symm

theorem rightSource_basis {L U V : ℕ} (B : I ↪ FiniteIdentity.Index L)
    (hB : ∀ i, doubledEnergy (B i).val ≤ 2 * V) (i : I) :
    colourBasis R (basisIndex (rightSource (U := U) B hB i)) =
      KernelAlgorithm.rightInclusion R (Fock.basis R (B i).val) :=
  (KernelAlgorithm.rightInclusion_basis R (B i).val).symm

def modeScale {U V : ℕ} (r : ℤ) (d : KernelRectangle.Index U V) : R :=
  if (doubledEnergy d.1.val : ℤ) - doubledEnergy d.2.val = r then
    (dualSign d.2.val : R) else 0

theorem modeScale_kernel {L U V : ℕ} (r : ℤ) (v : State R L)
    (d : KernelRectangle.Index U V) (I J : FiniteIdentity.Index L)
    (hI : I.val = d.1.val) (hJ : J.val = d.2.val) :
    modeScale (R := R) r d *
        (colourBasis R).repr (kernel R L v) (basisIndex d) = diagonal R L r v I J := by
  classical
  simp only [modeScale, diagonal, matrix, basisIndex, hI, hJ]
  split_ifs <;> simp

def selectionTranspose [DecidableEq D] (index : I ↪ D) :
    ScalarTransposeAlgorithm R D I (fun i d => if index i = d then 1 else 0) where
  circuit := sourceBank index id
  correct := by
    classical
    intro d
    change (sourceBank (R := R) index id).polynomial d = _
    rw [polynomial_sourceBank]
    by_cases h : ∃ i, index i = d
    · obtain ⟨i, rfl⟩ := h
      rw [index.injective.extend_apply]
      simp [index.injective.eq_iff, ite_smul, eq_comm]
    · rw [Function.extend_apply' _ _ _ h]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      have hne : index i ≠ d := fun he => h ⟨i, he⟩
      simp [hne]

theorem size_selectionTranspose [DecidableEq D] (index : I ↪ D) :
    (selectionTranspose (R := R) index).size = 0 :=
  size_sourceBank index id

end

end Lemmata.FockCircuits.SourceBanks
