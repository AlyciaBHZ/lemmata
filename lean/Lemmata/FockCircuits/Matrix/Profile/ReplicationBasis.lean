module

public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Profile.Replication

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

def blockPolynomial (P : K[X]) (n : ℕ) : K[X] :=
  X ^ (n % P.natDegree) * P ^ (n / P.natDegree)

theorem blockPolynomial_monic {P : K[X]} (hP : P.Monic) (n : ℕ) :
    (blockPolynomial P n).Monic :=
  (monic_X_pow _).mul (hP.pow _)

theorem blockPolynomial_natDegree {P : K[X]} (hP : P.Monic) (n : ℕ) :
    (blockPolynomial P n).natDegree = n := by
  unfold blockPolynomial
  rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hP.ne_zero),
    natDegree_X_pow, natDegree_pow]
  simpa only [Nat.mul_comm] using Nat.mod_add_div n P.natDegree

/-- Monic polynomial division orders the finite multiplication coordinates by their leading degree. -/
def blockSequence (P : K[X]) (hP : P.Monic) : Polynomial.Sequence K where
  elems' := blockPolynomial P
  degree_eq' n := by
    rw [degree_eq_natDegree (blockPolynomial_monic hP n).ne_zero,
      blockPolynomial_natDegree hP n]

theorem blockSequence_leadingCoeff_unit {P : K[X]} (hP : P.Monic) (n : ℕ) :
    IsUnit ((blockSequence P hP) n).leadingCoeff := by
  change IsUnit (blockPolynomial P n).leadingCoeff
  rw [(blockPolynomial_monic hP n).leadingCoeff]
  exact isUnit_one

def blockBasis (P : K[X]) (hP : P.Monic) : Module.Basis ℕ K K[X] :=
  (blockSequence P hP).basis (blockSequence_leadingCoeff_unit hP)

@[simp] theorem blockBasis_apply (P : K[X]) (hP : P.Monic) (n : ℕ) :
    blockBasis P hP n = blockPolynomial P n :=
  (blockSequence P hP).basis_eq_self _ n

theorem span_initial_blocks (P : K[X]) (hP : P.Monic) (m : ℕ) :
    Submodule.span K ((blockSequence P hP) '' Set.Iio m) = degreeLT K m :=
  (blockSequence P hP).span_degreeLT (fun n _ => blockSequence_leadingCoeff_unit hP n)

/-- Multiplying two blocks produces one remainder block and at most one carry block. -/
theorem product_two_blocks (P u v : K[X]) (a b : ℕ) :
    (u * P ^ a) * (v * P ^ b) =
      (u * v %ₘ P) * P ^ (a + b) + (u * v /ₘ P) * P ^ (a + b + 1) := by
  calc
    (u * P ^ a) * (v * P ^ b) = (u * v) * P ^ (a + b) := by rw [pow_add]; ring
    _ = ((u * v %ₘ P) + P * (u * v /ₘ P)) * P ^ (a + b) := by
      rw [modByMonic_add_div]
    _ = _ := by rw [pow_succ]; ring

theorem product_remainder_degree {P u v : K[X]} (hP : P.Monic)
    (hq : 0 < P.natDegree) : (u * v %ₘ P).natDegree < P.natDegree := by
  apply natDegree_modByMonic_lt _ hP
  intro heq
  rw [heq, natDegree_one] at hq
  omega

theorem product_carry_degree {P u v : K[X]} (hP : P.Monic)
    (hu : u.natDegree < P.natDegree) (hv : v.natDegree < P.natDegree) :
    (u * v /ₘ P).natDegree < P.natDegree := by
  rw [natDegree_divByMonic _ hP]
  have hprod := natDegree_mul_le (p := u) (q := v)
  omega

theorem eval_product_remainder {P u v : K[X]} {x : K} (hx : P.eval x = 0) :
    (u * v %ₘ P).eval x = u.eval x * v.eval x := by
  rw [modByMonic_eq_sub_mul_div]
  simp only [eval_sub, eval_mul, hx, zero_mul, sub_zero]

end

end Lemmata.FockCircuits.Matrix.Profile.Replication
