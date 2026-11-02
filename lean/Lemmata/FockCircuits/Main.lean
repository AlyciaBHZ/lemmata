module

public import Lemmata.FockCircuits.RecordBounds
public import Lemmata.FockCircuits.IntegralCrossing
public import Lemmata.FockCircuits.HurwitzBound
public import Lemmata.FockCircuits.FiniteModeTransfer
public import Lemmata.FockCircuits.QuarticBound
public import Lemmata.FockCircuits.QuinticBound
public import Lemmata.FockCircuits.HomogeneousIdentity

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits

-- DOCS_BEGIN_MAIN
/-- The positional quartic crossing has a subquadratic circuit over every field. -/
theorem quarticCircuits (F : Type*) [Field F] :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (Positional.quartic F n) s ∧
        (s : ℝ) ≤ C * (n : ℝ) ^ (5 / 3 : ℝ) :=
  RecordBounds.quartic_bound F

/-- The construction extends the uniform bound to degree at most five. -/
theorem quinticCircuits (F : Type*) [Field F] :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ p : FreeAlgebra F (Fin n),
      Symmetric.IsSymmetric p → Symmetric.DegreeLE 5 p →
        ∃ s : ℕ, HasCircuit p s ∧ (s : ℝ) ≤ C * (n : ℝ) ^ (5 / 3 : ℝ) :=
  RecordBounds.symmetric_five_bound F

/-- One constant covers all row-ordered permanents with at most five rows. -/
theorem permanentCircuits (F : Type*) [Field F] :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, k ≤ 5 → ∀ n : ℕ, 1 ≤ n →
      ∃ s : ℕ, HasCircuit (Patterns.rectangularPermanent F k n) s ∧
        (s : ℝ) ≤ C * (n : ℝ) ^ (5 / 3 : ℝ) :=
  RecordBounds.permanent_five_bound F

/-- The signed finite identity on every action state within the energy cutoff. -/
theorem signedFiniteIdentity (R : Type*) [CommRing R] (L E W : ℕ)
    (ξ η : FiniteIdentity.State R L) (hW : 0 < W)
    (hξ : ∀ A, ξ A ≠ 0 → doubledEnergy A.val ≤ W ∧
      doubledEnergy A.val % 2 = W % 2)
    (hη : ∀ B, η B ≠ 0 → doubledEnergy B.val = W)
    (hcut : 2 * E + W ≤ 2 * L) (I J : FiniteIdentity.Index L)
    (hJ : doubledEnergy J.val ≤ 2 * E) :
    (∑ k : Fin W,
      ((CrossingCircuit.oppositeMode R L W k η *
          CrossingCircuit.markedMode R L W k ξ) I J -
        (FiniteIdentity.sigma W : R) *
          (CrossingCircuit.markedMode R L W k ξ *
            CrossingCircuit.oppositeMode R L W k η) I J)) =
      (if I = J then (1 : R) else 0) * FiniteIdentity.vacuumPairing R L ξ η :=
  FiniteIdentity.homogeneous_signed_identity R L E W ξ η hW hξ hη hcut I J hJ

/-- An integer coefficient decomposition of the crossing across its two cuts. -/
theorem integralCrossingDecomposition (H E n : ℕ) (hH : 0 < H)
    (hcapacity : 2 * H * n ≤ stateCount H - 1) :
    ∃ r ≤ 2 * H * stateCount (H + E),
      ∃ a b c d : Fin r → Fin n → Fin (stateCount E) → ℤ,
        ∀ (i k : Fin n) (j l : Fin (stateCount E)),
          (∑ s, (a s i j * b s k l + c s i l * d s k j)) =
            if i = k then (if j = l then 1 else 0) else 0 :=
  Families.integral_crossing_decomposition H E n hH hcapacity

/-- The crossing gives bilinear sum-of-squares identities over the complex numbers. -/
theorem hurwitzSquareRootBound (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ (s : ℕ) (forms : Fin s → Fin n → Fin n → ℂ),
        (s : ℝ) ≤ (n : ℝ) ^ (Real.sqrt 2 + eps) ∧
        ∀ (x y : Fin n → ℂ),
          (∑ r, Hurwitz.bilinear (forms r) x y ^ 2) =
            (∑ i, x i ^ 2) * (∑ j, y j ^ 2) :=
  Hurwitz.eventually_sum_of_squares eps heps
-- DOCS_END_MAIN

end Lemmata.FockCircuits
