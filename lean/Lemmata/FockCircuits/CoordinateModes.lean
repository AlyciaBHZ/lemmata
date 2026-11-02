module

public import Lemmata.FockCircuits.KernelModes
public import Lemmata.FockCircuits.CrossingExistence

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lemmata.FockCircuits.CoordinateModes

open FiniteIdentity Families CrossingCircuit CrossingExistence KernelRectangle
open KernelAlgorithm KernelStages KernelBanks KernelInput SourceBanks KernelModes
open KernelPipeline

noncomputable section

variable (R : Type*) [CommRing R]

def sourceSteps (marked right : Bool) (L W : ℕ) (k : Fin W) : List (Fock R →ₗ[R] Fock R) :=
  if marked then markedPrefix R right L W k else barePrefix R right

def states {I : Type*} {L W : ℕ} (marked : Bool) (B : I → FiniteIdentity.Index L)
    (k : Fin W) (i : I) : State R L :=
  if marked then mark R L W k (dualFamily R B i) else bareFamily R B i

def selectedShift (marked : Bool) (W : ℕ) (k : Fin W) : ℤ :=
  if marked then shift W k else -shift W k

theorem sourceSteps_sparse (marked right : Bool) (L W : ℕ) (k : Fin W) :
    ∀ T ∈ sourceSteps R marked right L W k, SparseColumns R T := by
  cases marked
  · exact barePrefix_sparse R right
  · exact markedPrefix_sparse R right L W k

theorem sourceSteps_preserves (U V L W : ℕ) (marked right : Bool) (k : Fin W) :
    ∀ T ∈ sourceSteps R marked right L W k,
      let P := projection (colourBasis R) (basisIndex (U := U) (V := V))
      P.comp (T.comp P) = T.comp P := by
  cases marked
  · exact barePrefix_preserves R U V right
  · exact markedPrefix_preserves R U V L W right k

theorem sourceSteps_length (marked right : Bool) (L W : ℕ) (k : Fin W) :
    (sourceSteps R marked right L W k).length ≤ (Fock.raisingSteps R L).length + 2 := by
  cases marked
  · change (barePrefix R right).length ≤ _
    rw [barePrefix_length]
    omega
  · change (markedPrefix R right L W k).length ≤ _
    rw [markedPrefix_length]

theorem sourceSteps_kernel {I : Type*} {L W : ℕ} (marked right : Bool)
    (B : I → FiniteIdentity.Index L) (k : Fin W) (i : I)
    (hB : doubledEnergy (B i).val ≤ 2 * L) :
    actualSteps (kernelSteps R right L ++ sourceSteps R marked right L W k)
        (sourceInclusion R right (Fock.basis R (B i).val)) =
      kernel R L (states R marked B k i) := by
  cases marked
  · exact bareKernel_basis R right L (B i)
  · exact markedKernel_basis R right L W k (B i) hB

theorem exists_coordinate_mode {X : Type*} (n H E W : ℕ) (marked right : Bool)
    (B : Fin n ↪ FiniteIdentity.Index (H + E))
    (hWH : W ≤ 2 * H) (hBW : ∀ i, doubledEnergy (B i).val = W)
    (k : Fin W) (label : Fin n → X) :
    ∃ p : CircuitFamily R X (KernelRectangle.Index (H + E) E),
      p.size ≤ 32 * (H + E + 1)^2 * stateCount (H + E) * stateCount E ∧
      ∀ f, p.polynomial f = ∑ i,
        diagonal R (H + E) (selectedShift marked W k) (states R marked B k i)
          (if right then action H E f.2 else middle (H + E) f.1)
          (if right then middle (H + E) f.1 else action H E f.2) •
            FreeAlgebra.ι R (label i) := by
  classical
  let L := H + E
  have hB (i : Fin n) : doubledEnergy (B i).val ≤ 2 * L := by rw [hBW]; dsimp [L]; omega
  cases right with
  | false =>
    let source := leftSource (V := E) B hB
    obtain ⟨p, hsize, hp⟩ := exists_mode_circuit R L E L false (selectedShift marked W k)
      (sourceSteps R marked false L W k) (sourceSteps_sparse R marked false L W k)
      (sourceSteps_preserves R L E L W marked false k)
      (sourceSteps_length R marked false L W k) source label (Function.Embedding.refl _)
      (fun f => middle L f.1) (fun f => action H E f.2)
      (fun _ => rfl) (fun _ => rfl) (states R marked B k) (by
        intro i
        rw [leftSource_basis]
        exact sourceSteps_kernel R marked false B k i (hB i))
    refine ⟨p, hsize, ?_⟩
    intro f
    simpa only [Bool.false_eq_true, ite_false] using hp f
  | true =>
    let source := rightSource (U := E) B hB
    let output : KernelRectangle.Index L E ↪ KernelRectangle.Index E L :=
      (Equiv.prodComm _ _).toEmbedding
    obtain ⟨p, hsize, hp⟩ := exists_mode_circuit R E L L true (selectedShift marked W k)
      (sourceSteps R marked true L W k) (sourceSteps_sparse R marked true L W k)
      (sourceSteps_preserves R E L L W marked true k)
      (sourceSteps_length R marked true L W k) source label output
      (fun f => action H E f.2) (fun f => middle L f.1)
      (fun _ => rfl) (fun _ => rfl) (states R marked B k) (by
        intro i
        rw [rightSource_basis]
        exact sourceSteps_kernel R marked true B k i (hB i))
    refine ⟨p, ?_, ?_⟩
    · simpa only [L, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsize
    · intro f
      simpa only [ite_true] using hp f

end

end Lemmata.FockCircuits.CoordinateModes
