module

public import Lemmata.FockCircuits.Compiler
public import Lemmata.FockCircuits.Matrix.CircuitBuilders

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits

open scoped BigOperators

namespace PrefixExtraction

variable {R A I J ρ K : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable [Fintype I] [Fintype J] [Fintype ρ] [Fintype K]

def firstContext (b : Matrix ρ J A) (y u : Matrix J K A) : Matrix ρ J A :=
  (y * (b * u).transpose).transpose

def secondContext (d : Matrix ρ J A) (y u : Matrix J K A) : Matrix ρ J A :=
  (y.transpose * d.transpose).transpose * u.transpose

private theorem move_third_sum {L Q S T : Type*}
    [Fintype L] [Fintype Q] [Fintype S] [Fintype T] (f : L → Q → S → T → A) :
    (∑ l, ∑ q, ∑ s, ∑ t, f l q s t) = ∑ s, ∑ l, ∑ q, ∑ t, f l q s t := by
  calc
    _ = ∑ l, ∑ s, ∑ q, ∑ t, f l q s t := by
      apply Finset.sum_congr rfl
      intro l hl
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private theorem reverse_three_sums {L Q S : Type*}
    [Fintype L] [Fintype Q] [Fintype S] (f : L → Q → S → A) :
    (∑ l, ∑ q, ∑ s, f l q s) = ∑ s, ∑ q, ∑ l, f l q s := by
  rw [Finset.sum_comm]
  calc
    (∑ q, ∑ l, ∑ s, f l q s) = ∑ q, ∑ s, ∑ l, f l q s := by
      apply Finset.sum_congr rfl
      intro q hq
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Array transposes only exchange indices; every noncommutative product keeps its order. -/
theorem assembly_contexts (a b c d : Matrix ρ J A) (y u : Matrix J K A) :
    orderedAssembly a b c d y u =
      (∑ r, ∑ j, a r j * firstContext b y u r j) +
        (∑ r, ∑ l, c r l * secondContext d y u r l) := by
  rw [orderedAssembly_expansion]
  simp only [Finset.sum_add_distrib]
  congr 1
  · simp only [firstContext, Matrix.transpose_apply, Matrix.mul_apply,
      Finset.mul_sum, mul_assoc]
    rw [move_third_sum]
    apply Finset.sum_congr rfl
    intro r hr
    exact reverse_three_sums _
  · simp only [secondContext, Matrix.transpose_apply, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact move_third_sum _

def scalarTranspose (a : ρ → I → J → R) (z : Matrix ρ J A) (i : I) : A :=
  ∑ r, ∑ j, a r i j • z r j

theorem coefficientRows_adjoint (a : ρ → I → J → R) (x : I → A) (z : Matrix ρ J A) :
    (∑ r, ∑ j, coefficientRows a x r j * z r j) =
      ∑ i, x i * scalarTranspose a z i := by
  simp only [coefficientRows, scalarTranspose, Finset.sum_mul, Finset.mul_sum,
    mul_smul_comm, smul_mul_assoc]
  calc
    (∑ r, ∑ j, ∑ i, a r i j • (x i * z r j)) =
        ∑ r, ∑ i, ∑ j, a r i j • (x i * z r j) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

def coefficients (a c : ρ → I → J → R) (b d : Matrix ρ J A)
    (y u : Matrix J K A) (i : I) : A :=
  scalarTranspose a (firstContext b y u) i + scalarTranspose c (secondContext d y u) i

theorem assembly_prefix (a c : ρ → I → J → R) (x : I → A)
    (b d : Matrix ρ J A) (y u : Matrix J K A) :
    orderedAssembly (coefficientRows a x) b (coefficientRows c x) d y u =
      ∑ i, x i * coefficients a c b d y u i := by
  rw [assembly_contexts, coefficientRows_adjoint, coefficientRows_adjoint]
  simp only [coefficients, mul_add, Finset.sum_add_distrib]

theorem coefficients_crossing [DecidableEq I] [DecidableEq J]
    (a b c d : ρ → I → J → R)
    (h : ∀ i j k l, (∑ r, a r i j * b r k l) + (∑ r, c r i l * d r k j) =
      if i = k then (if j = l then 1 else 0) else 0)
    (v : I → A) (y u : Matrix J K A) (i : I) :
    coefficients a c (coefficientRows b v) (coefficientRows d v) y u i =
      ∑ j, ∑ q, y j q * v i * u j q := by
  let x : I → A := fun k => if k = i then 1 else 0
  have hforward := directAssembly_eq_crossing a b c d h x v y u
  rw [assembly_prefix] at hforward
  simpa [x, batchedCrossing, ite_mul] using hforward

theorem quintic_crossing [DecidableEq I] [DecidableEq J]
    (a b c d : ρ → I → J → R)
    (h : ∀ i j k l, (∑ r, a r i j * b r k l) + (∑ r, c r i l * d r k j) =
      if i = k then (if j = l then 1 else 0) else 0)
    (x v w : I → A) (y u : Matrix J K A) :
    (∑ i, x i * coefficients a c (coefficientRows b v) (coefficientRows d v) y u i * w i) =
      ∑ i, ∑ j, ∑ q, x i * y j q * v i * u j q * w i := by
  simp only [coefficients_crossing a b c d h, Finset.mul_sum, Finset.sum_mul, mul_assoc]

end PrefixExtraction

end Lemmata.FockCircuits
