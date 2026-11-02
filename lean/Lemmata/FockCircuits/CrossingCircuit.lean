module

public import Lemmata.FockCircuits.Compiler
public import Lemmata.FockCircuits.FiniteIdentity
public import Lemmata.FockCircuits.Matrix.CircuitBuilders
public import Lemmata.FockCircuits.Partition

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lemmata.FockCircuits.CrossingCircuit

open FiniteIdentity
open scoped BigOperators

noncomputable section

variable (R : Type*) [CommRing R]

def cutoffEmbedding {E L : ℕ} (hEL : E ≤ L) : ↥(fullCutoff E) ↪ Index L where
  toFun I := ⟨I.val, Finset.mem_powerset.mpr (by
    intro i hi
    have he := mem_fullCutoff.mp I.property
    have hw := Finset.single_le_sum (f := fun j : ℕ => 2 * j + 1)
      (fun _ _ => Nat.zero_le _) hi
    change 2 * i + 1 ≤ doubledEnergy I.val at hw
    exact Finset.mem_range.mpr (by omega))⟩
  inj' I J h := Subtype.ext (congrArg (fun z : Index L => z.val) h)

theorem cutoffEmbedding_covers (L : ℕ) (s : Index L) (hs : doubledEnergy s.val ≤ 2 * L) :
    s ∈ Set.range (cutoffEmbedding (E := L) (L := L) le_rfl) := by
  refine ⟨⟨s.val, mem_fullCutoff.mpr hs⟩, ?_⟩
  exact Subtype.ext rfl

theorem cutoffEmbedding_energy {E L : ℕ} (hEL : E ≤ L) (j : ↥(fullCutoff E)) :
    doubledEnergy (cutoffEmbedding hEL j).val ≤ 2 * E := mem_fullCutoff.mp j.property

def markedMode (L W : ℕ) (r : Fin W) (v : State R L) : Matrix (Index L) (Index L) R :=
  diagonal R L (shift W r) (mark R L W r v)

def oppositeMode (L W : ℕ) (r : Fin W) (v : State R L) : Matrix (Index L) (Index L) R :=
  diagonal R L (-shift W r) v

theorem markedMode_zero_above {L E W : ℕ} (r : Fin W) (v : State R L) (s j : Index L)
    (hs : 2 * L < doubledEnergy s.val) (hj : doubledEnergy j.val ≤ 2 * E)
    (hcut : 2 * E + W ≤ 2 * L) : markedMode R L W r v s j = 0 := by
  have hs' : (2 : ℤ) * L < doubledEnergy s.val := by exact_mod_cast hs
  have hj' : (doubledEnergy j.val : ℤ) ≤ 2 * E := by exact_mod_cast hj
  have hcut' : (2 : ℤ) * E + W ≤ 2 * L := by exact_mod_cast hcut
  have hr := (shift_bounds W r).2
  have he : (doubledEnergy s.val : ℤ) - doubledEnergy j.val ≠ shift W r := by omega
  simp only [markedMode, diagonal, ite_eq_right he]

theorem oppositeMode_zero_above {L E W : ℕ} (r : Fin W) (v : State R L) (s j : Index L)
    (hs : 2 * L < doubledEnergy s.val) (hj : doubledEnergy j.val ≤ 2 * E)
    (hcut : 2 * E + W ≤ 2 * L) : oppositeMode R L W r v s j = 0 := by
  have hs' : (2 : ℤ) * L < doubledEnergy s.val := by exact_mod_cast hs
  have hj' : (doubledEnergy j.val : ℤ) ≤ 2 * E := by exact_mod_cast hj
  have hcut' : (2 : ℤ) * E + W ≤ 2 * L := by exact_mod_cast hcut
  have hr := (shift_bounds W r).1
  have he : (doubledEnergy s.val : ℤ) - doubledEnergy j.val ≠ -shift W r := by omega
  simp only [oppositeMode, diagonal, ite_eq_right he]

theorem matrix_product_cut {S T : Type*} [Fintype S] [Fintype T]
    (index : T ↪ S) (A B : Matrix S S R) (i j : S)
    (hzero : ∀ s ∉ Set.range index, A i s * B s j = 0) :
    (A * B) i j = ∑ t, A i (index t) * B (index t) j := by
  rw [Matrix.mul_apply]
  exact (Fintype.sum_of_injective index index.injective _ _ hzero (fun _ => rfl)).symm

variable {I J ρ : Type*} [Fintype I] [Fintype J] [Fintype ρ]

def coefficientA {L W : ℕ} (a : I → State R L) (action : J → Index L) (middle : ρ ↪ Index L)
    (s : Fin W × ρ) (i : I) (j : J) : R := markedMode R L W s.1 (a i) (middle s.2) (action j)

def coefficientB {L W : ℕ} (b : I → State R L) (action : J → Index L) (middle : ρ ↪ Index L)
    (s : Fin W × ρ) (i : I) (j : J) : R := oppositeMode R L W s.1 (b i) (action j) (middle s.2)

def coefficientC {L W : ℕ} (a : I → State R L) (action : J → Index L) (middle : ρ ↪ Index L)
    (s : Fin W × ρ) (i : I) (j : J) : R := markedMode R L W s.1 (a i) (action j) (middle s.2)

def coefficientD {L W : ℕ} (b : I → State R L) (action : J → Index L) (middle : ρ ↪ Index L)
    (s : Fin W × ρ) (i : I) (j : J) : R := oppositeMode R L W s.1 (b i) (middle s.2) (action j)

/-- The energy filters insert the intermediate cutoff into both products of the finite signed identity. -/
theorem coefficient_identity_of_signed [DecidableEq I] [DecidableEq J] {L E W : ℕ}
    (a b : I → State R L) (action : J → Index L) (middle : ρ ↪ Index L)
    (haction : ∀ j, doubledEnergy (action j).val ≤ 2 * E)
    (hcover : ∀ s : Index L, doubledEnergy s.val ≤ 2 * L → s ∈ Set.range middle)
    (hcut : 2 * E + W ≤ 2 * L)
    (hsigned : ∀ i k j l,
      (∑ r : Fin W,
        ((oppositeMode R L W r (b k) * markedMode R L W r (a i)) (action l) (action j) -
          (sigma W : R) *
            ((markedMode R L W r (a i) * oppositeMode R L W r (b k)) (action l) (action j)))) =
        if i = k then (if j = l then 1 else 0) else 0)
    (i k : I) (j l : J) :
    (∑ s : Fin W × ρ, coefficientA R a action middle s i j * coefficientB R b action middle s k l) -
      (sigma W : R) *
        (∑ s : Fin W × ρ, coefficientC R a action middle s i l * coefficientD R b action middle s k j) =
      if i = k then (if j = l then 1 else 0) else 0 := by
  have hBA (r : Fin W) :
      (oppositeMode R L W r (b k) * markedMode R L W r (a i)) (action l) (action j) =
        ∑ t, oppositeMode R L W r (b k) (action l) (middle t) *
          markedMode R L W r (a i) (middle t) (action j) := by
    apply matrix_product_cut R middle
    intro s hs
    have henergy : 2 * L < doubledEnergy s.val := by
      by_contra! henergy
      exact hs (hcover s henergy)
    rw [markedMode_zero_above R r (a i) s (action j) henergy (haction j) hcut, mul_zero]
  have hAB (r : Fin W) :
      (markedMode R L W r (a i) * oppositeMode R L W r (b k)) (action l) (action j) =
        ∑ t, markedMode R L W r (a i) (action l) (middle t) *
          oppositeMode R L W r (b k) (middle t) (action j) := by
    apply matrix_product_cut R middle
    intro s hs
    have henergy : 2 * L < doubledEnergy s.val := by
      by_contra! henergy
      exact hs (hcover s henergy)
    rw [oppositeMode_zero_above R r (b k) s (action j) henergy (haction j) hcut, mul_zero]
  have h := hsigned i k j l
  simp_rw [hBA, hAB] at h
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  simp only [coefficientA, coefficientB, coefficientC, coefficientD, Fintype.sum_prod_type]
  calc
    _ = (∑ r : Fin W, ∑ t : ρ,
        oppositeMode R L W r (b k) (action l) (middle t) *
          markedMode R L W r (a i) (middle t) (action j)) -
        (sigma W : R) *
          (∑ r : Fin W, ∑ t : ρ, markedMode R L W r (a i) (action l) (middle t) *
            oppositeMode R L W r (b k) (middle t) (action j)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro t ht
      exact mul_comm _ _
    _ = _ := h

section SignedAssembly

open Lemmata.FockCircuits.Matrix

variable {R} {X O P K : Type*} [Fintype P] [Fintype K]

/-- Apply the common sign after the negative matrix product, retaining the shared bank once. -/
def scaleSecond (s : R) (bank : CircuitFamily R X (Bool × P)) :
    CircuitFamily R X (Bool × P) :=
  bank.substitute (CircuitBuilders.family fun p : Bool × P =>
    if p.1 then CircuitBuilders.input p else
      CircuitBuilders.mul (CircuitBuilders.scalar s) (CircuitBuilders.input p))

theorem size_scaleSecond (s : R) (bank : CircuitFamily R X (Bool × P)) :
    (scaleSecond s bank).size = bank.size + Fintype.card P := by
  simp [scaleSecond, Fintype.sum_prod_type]

theorem eval_scaleSecond {A : Type*} [Add A] [Mul A]
    (s : R) (bank : CircuitFamily R X (Bool × P)) (r : R → A) (x : X → A)
    (b : Bool) (p : P) :
    (scaleSecond s bank).eval r x (b, p) =
      if b then bank.eval r x (true, p) else r s * bank.eval r x (false, p) := by
  cases b <;> simp [scaleSecond]

@[simp] theorem polynomial_scaleSecond_true (s : R)
    (bank : CircuitFamily R X (Bool × P)) (p : P) :
    (scaleSecond s bank).polynomial (true, p) = bank.polynomial (true, p) :=
  eval_scaleSecond s bank (algebraMap R (FreeAlgebra R X)) (FreeAlgebra.ι R) true p

@[simp] theorem polynomial_scaleSecond_false (s : R)
    (bank : CircuitFamily R X (Bool × P)) (p : P) :
    (scaleSecond s bank).polynomial (false, p) = s • bank.polynomial (false, p) := by
  change (scaleSecond s bank).eval (algebraMap R (FreeAlgebra R X)) (FreeAlgebra.ι R)
    (false, p) = _
  rw [eval_scaleSecond]
  simp [Algebra.smul_def, CircuitFamily.polynomial]

def compile (s : R) (bank : CircuitFamily R X O)
    (sa sb sc sd : ρ × J → O) (sy : J × K → O) (u : J × K → X)
    (p : OrderedMatrixAlgorithm R ρ J K) (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J) (zm : OrderedMatrixAlgorithm R J ρ K) :
    CircuitFamily R X PUnit :=
  Assembly.finish (scaleSecond s (FourProducts.build bank sa sb sc sd sy p q zp zm)) u

theorem size_compile (s : R) (bank : CircuitFamily R X O)
    (sa sb sc sd : ρ × J → O) (sy : J × K → O) (u : J × K → X)
    (p : OrderedMatrixAlgorithm R ρ J K) (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J) (zm : OrderedMatrixAlgorithm R J ρ K) :
    (compile s bank sa sb sc sd sy u p q zp zm).size =
      bank.size + p.size + q.size + zp.size + zm.size +
        4 * (Fintype.card J * Fintype.card K) := by
  rw [compile, Assembly.size_finish, size_scaleSecond, FourProducts.size_build,
    Fintype.card_prod]
  omega

theorem polynomial_compile (s : R) (bank : CircuitFamily R X O)
    (sa sb sc sd : ρ × J → O) (sy : J × K → O) (y u : Matrix J K X)
    (hy : ∀ j t, bank.polynomial (sy (j, t)) = FreeAlgebra.ι R (y j t))
    (p : OrderedMatrixAlgorithm R ρ J K) (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J) (zm : OrderedMatrixAlgorithm R J ρ K) :
    (compile s bank sa sb sc sd sy (fun v => u v.1 v.2) p q zp zm).polynomial PUnit.unit =
      orderedAssembly
        (Matrix.of (fun r j => bank.polynomial (sa (r, j))))
        (Matrix.of (fun r j => bank.polynomial (sb (r, j))))
        (Matrix.of (fun r j => s • bank.polynomial (sc (r, j))))
        (Matrix.of (fun r j => bank.polynomial (sd (r, j))))
        (Matrix.of (fun j t => FreeAlgebra.ι R (y j t)))
        (Matrix.of (fun j t => FreeAlgebra.ι R (u j t))) := by
  apply Assembly.polynomial_finish_eq_orderedAssembly
  · intro l t
    rw [polynomial_scaleSecond_true, FourProducts.polynomial_build_true]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, hy]
  · intro l t
    rw [polynomial_scaleSecond_false, FourProducts.polynomial_build_false]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, hy,
      Algebra.smul_def, Finset.mul_sum, mul_assoc]

theorem coefficientRows_scale {A : Type*} [Semiring A] [Algebra R A]
    (s : R) (a : ρ → I → J → R) (x : I → A) (r : ρ) (j : J) :
    coefficientRows (fun r i j => s * a r i j) x r j = s • coefficientRows a x r j := by
  simp only [coefficientRows, mul_smul, Finset.smul_sum]

theorem polynomial_compile_crossing [DecidableEq I] [DecidableEq J]
    (s : R) (a b c d : ρ → I → J → R)
    (hcoeff : ∀ i j k l,
      (∑ r, a r i j * b r k l) + s * (∑ r, c r i l * d r k j) =
        if i = k then (if j = l then 1 else 0) else 0)
    (bank : CircuitFamily R X O) (sa sb sc sd : ρ × J → O) (sy : J × K → O)
    (x v : I → X) (y u : Matrix J K X)
    (ha : ∀ r j, bank.polynomial (sa (r, j)) =
      coefficientRows a (fun i => FreeAlgebra.ι R (x i)) r j)
    (hb : ∀ r j, bank.polynomial (sb (r, j)) =
      coefficientRows b (fun i => FreeAlgebra.ι R (v i)) r j)
    (hc : ∀ r j, bank.polynomial (sc (r, j)) =
      coefficientRows c (fun i => FreeAlgebra.ι R (x i)) r j)
    (hd : ∀ r j, bank.polynomial (sd (r, j)) =
      coefficientRows d (fun i => FreeAlgebra.ι R (v i)) r j)
    (hy : ∀ j t, bank.polynomial (sy (j, t)) = FreeAlgebra.ι R (y j t))
    (p : OrderedMatrixAlgorithm R ρ J K) (q : OrderedMatrixAlgorithm R K J ρ)
    (zp : OrderedMatrixAlgorithm R K ρ J) (zm : OrderedMatrixAlgorithm R J ρ K) :
    (compile s bank sa sb sc sd sy (fun z => u z.1 z.2) p q zp zm).polynomial PUnit.unit =
      batchedCrossing (fun i => FreeAlgebra.ι R (x i)) (fun i => FreeAlgebra.ι R (v i))
        (Matrix.of (fun j t => FreeAlgebra.ι R (y j t)))
        (Matrix.of (fun j t => FreeAlgebra.ι R (u j t))) := by
  rw [polynomial_compile s bank sa sb sc sd sy y u hy p q zp zm]
  have ha' : Matrix.of (fun r j => bank.polynomial (sa (r, j))) =
      coefficientRows a (fun i => FreeAlgebra.ι R (x i)) := by ext r j; exact ha r j
  have hb' : Matrix.of (fun r j => bank.polynomial (sb (r, j))) =
      coefficientRows b (fun i => FreeAlgebra.ι R (v i)) := by ext r j; exact hb r j
  have hc' : Matrix.of (fun r j => s • bank.polynomial (sc (r, j))) =
      coefficientRows (fun r i j => s * c r i j) (fun i => FreeAlgebra.ι R (x i)) := by
    ext r j
    rw [Matrix.of_apply, hc, coefficientRows_scale]
  have hd' : Matrix.of (fun r j => bank.polynomial (sd (r, j))) =
      coefficientRows d (fun i => FreeAlgebra.ι R (v i)) := by ext r j; exact hd r j
  rw [ha', hb', hc', hd']
  apply directAssembly_eq_crossing
  intro i j k l
  simpa only [mul_assoc, ← Finset.mul_sum] using hcoeff i j k l

end SignedAssembly

section ModeAssembly

variable {R} {X O K : Type*} [Fintype K]

/-- The universal coefficient banks and the finite signed identity assemble a shared crossing circuit. -/
theorem compile_modes_correct [DecidableEq I] [DecidableEq J] {L E W : ℕ}
    (a b : I → State R L) (action : J → Index L) (middle : ρ ↪ Index L)
    (haction : ∀ j, doubledEnergy (action j).val ≤ 2 * E)
    (hcover : ∀ z : Index L, doubledEnergy z.val ≤ 2 * L → z ∈ Set.range middle)
    (hcut : 2 * E + W ≤ 2 * L)
    (hsigned : ∀ i k j l,
      (∑ r : Fin W,
        ((oppositeMode R L W r (b k) * markedMode R L W r (a i)) (action l) (action j) -
          (sigma W : R) *
            ((markedMode R L W r (a i) * oppositeMode R L W r (b k)) (action l) (action j)))) =
        if i = k then (if j = l then 1 else 0) else 0)
    (bank : CircuitFamily R X O)
    (sa sb sc sd : (Fin W × ρ) × J → O) (sy : J × K → O)
    (x v : I → X) (y u : Matrix J K X)
    (ha : ∀ r j, bank.polynomial (sa (r, j)) =
      coefficientRows (coefficientA R a action middle) (fun i => FreeAlgebra.ι R (x i)) r j)
    (hb : ∀ r j, bank.polynomial (sb (r, j)) =
      coefficientRows (coefficientB R b action middle) (fun i => FreeAlgebra.ι R (v i)) r j)
    (hc : ∀ r j, bank.polynomial (sc (r, j)) =
      coefficientRows (coefficientC R a action middle) (fun i => FreeAlgebra.ι R (x i)) r j)
    (hd : ∀ r j, bank.polynomial (sd (r, j)) =
      coefficientRows (coefficientD R b action middle) (fun i => FreeAlgebra.ι R (v i)) r j)
    (hy : ∀ j t, bank.polynomial (sy (j, t)) = FreeAlgebra.ι R (y j t))
    (p : OrderedMatrixAlgorithm R (Fin W × ρ) J K)
    (q : OrderedMatrixAlgorithm R K J (Fin W × ρ))
    (zp : OrderedMatrixAlgorithm R K (Fin W × ρ) J)
    (zm : OrderedMatrixAlgorithm R J (Fin W × ρ) K) :
    (compile (-(sigma W : R)) bank sa sb sc sd sy (fun z => u z.1 z.2) p q zp zm).polynomial
        PUnit.unit =
      batchedCrossing (fun i => FreeAlgebra.ι R (x i)) (fun i => FreeAlgebra.ι R (v i))
        (Matrix.of (fun j t => FreeAlgebra.ι R (y j t)))
        (Matrix.of (fun j t => FreeAlgebra.ι R (u j t))) ∧
    (compile (-(sigma W : R)) bank sa sb sc sd sy (fun z => u z.1 z.2) p q zp zm).size =
      bank.size + p.size + q.size + zp.size + zm.size +
        4 * (Fintype.card J * Fintype.card K) := by
  refine ⟨?_, size_compile _ _ _ _ _ _ _ _ _ _ _ _⟩
  apply polynomial_compile_crossing (-(sigma W : R))
    (coefficientA R a action middle) (coefficientB R b action middle)
    (coefficientC R a action middle) (coefficientD R b action middle) _
    bank sa sb sc sd sy x v y u ha hb hc hd hy p q zp zm
  intro i j k l
  simpa only [neg_mul, sub_eq_add_neg] using
    coefficient_identity_of_signed R a b action middle haction hcover hcut hsigned i k j l

end ModeAssembly

end

end Lemmata.FockCircuits.CrossingCircuit
