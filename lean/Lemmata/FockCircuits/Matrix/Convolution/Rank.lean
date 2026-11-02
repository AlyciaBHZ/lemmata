module

/- Adapted from the pinned OpenAI/selanavot field-generic sources.
The interpolation nodes use a natural-number embedding; complex border-rank APIs are omitted.
See Matrix/NOTICE.md and Matrix/Apache-2.0.txt. -/

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
Namespace, imports, and selected scope adapted for FockCircuits; see Matrix/NOTICE.md.
Apache-2.0 license retained in Matrix/Apache-2.0.txt.
-/

public import Lemmata.FockCircuits.Matrix.Convolution.Basic
public import Mathlib.LinearAlgebra.Lagrange

public section

set_option autoImplicit false

@[expose] section

namespace Lemmata.FockCircuits.Matrix

/-!
# Polynomial convolution by evaluation and interpolation

Evaluating the two input polynomials at `a + b - 1` distinct points of an infinite field,
then interpolating their product, expresses the convolution tensor as a sum
of `a + b - 1` rank-one tensors. This is the polynomial multiplication rank
upper bound used in Section 5.
-/

open scoped BigOperators
open Polynomial

namespace Spectral

variable {K : Type*} [Field K]

open Foundation

/-- Recover each monomial coefficient from evaluations at distinct nodes. -/
lemma monomial_coeff_eq_sum_interpolation {n m : ℕ} (hm : m < n)
    (v : Fin n → K) (hv : Function.Injective v) (k : ℕ) :
    (if m = k then (1 : K) else 0) =
      ∑ r : Fin n, v r ^ m * (Lagrange.basis Finset.univ v r).coeff k := by
  have hdeg : (X ^ m : K[X]).degree < (Finset.univ : Finset (Fin n)).card := by
    simpa using hm
  have hpoly := Lagrange.eq_interpolate (f := (X ^ m : K[X])) hv.injOn hdeg
  have hcoeff := congrArg (fun p : K[X] => p.coeff k) hpoly
  simpa only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.coeff_X_pow, eq_comm] using hcoeff

/-- Evaluation at distinct nodes and Lagrange interpolation give an explicit
rank-one decomposition of polynomial convolution. -/
theorem convolution_eq_sum_rankOne {a b : ℕ}
    (v : Fin (a + b - 1) → K) (hv : Function.Injective v) :
    convolution (K := K) a b = fun i j k => ∑ r : Fin (a + b - 1),
      Tensor.rankOne (fun i : Fin a => v r ^ i.val)
        (fun j : Fin b => v r ^ j.val)
        (fun k : Fin (a + b - 1) => (Lagrange.basis Finset.univ v r).coeff k.val)
        i j k := by
  funext i j k
  have hij : i.val + j.val < a + b - 1 := (convolutionOutput i j).isLt
  simpa only [convolution_apply, Tensor.rankOne, pow_add] using
    monomial_coeff_eq_sum_interpolation hij v hv k.val

/-- The convolution tensor `C(a,b)` has rank at most `a + b - 1` over `K`. -/
theorem convolution_rankAtMost [Infinite K] (a b : ℕ) :
    Tensor.RankAtMost (convolution (K := K) a b) (a + b - 1) := by
  let v : Fin (a + b - 1) → K := fun r => Infinite.natEmbedding K r.val
  have hv : Function.Injective v := by
    intro i j h
    exact Fin.ext ((Infinite.natEmbedding K).injective h)
  rw [convolution_eq_sum_rankOne v hv]
  simpa using Tensor.rankAtMost_sum_rankOne
    (fun r (i : Fin a) => v r ^ i.val)
    (fun r (j : Fin b) => v r ^ j.val)
    (fun r (k : Fin (a + b - 1)) => (Lagrange.basis Finset.univ v r).coeff k.val)

end Spectral

end Lemmata.FockCircuits.Matrix
