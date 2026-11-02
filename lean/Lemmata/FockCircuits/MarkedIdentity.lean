module

public import Lemmata.FockCircuits.SignedKernel

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.FiniteIdentity

variable (R : Type*) [CommRing R]

theorem weightPolynomial_product_constantTerm (W w : ℕ) (r : ℤ) (a b : R) :
    (weightPolynomial R W w *
      ((LaurentPolynomial.C a * LaurentPolynomial.T (R := R) (r - w)) *
        LaurentPolynomial.C b)).coeff 0 =
      ∑ k : Fin W, if r = shift W k then (weightCoefficient W w k : R) * (a * b) else 0 := by
  have he : (LaurentPolynomial.C a * LaurentPolynomial.T (R := R) (r - w)) *
      LaurentPolynomial.C b =
      LaurentPolynomial.C (a * b) * LaurentPolynomial.T (R := R) (r - w) := by
    rw [map_mul]
    ring
  rw [he, weightPolynomial_constantTerm]

theorem forward_weighted_matrix_constantTerm (L W : ℕ) (A B I J : Index L)
    (hW : 0 < W) (hw : doubledEnergy A.val ≤ W)
    (hparity : doubledEnergy A.val % 2 = W % 2)
    (hIJ : doubledEnergy I.val = doubledEnergy J.val) :
    ((LaurentPolynomial.T (R := R) 2 - 1) ^ ((W + doubledEnergy A.val) / 2 - 1) *
        (scaledMatrix R L A * constantMatrix R L B) I J).coeff 0 =
      ∑ k : Fin W, (weightCoefficient W (doubledEnergy A.val) k : R) *
        (diagonal R L (shift W k) (Pi.single A 1) *
          diagonal R L (-shift W k) (Pi.single B 1)) I J := by
  classical
  rw [← weightPolynomial_eq_power R W (doubledEnergy A.val) hW hw hparity,
    Matrix.mul_apply, Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [scaledMatrix_eq_monomial, constantMatrix, weightPolynomial_product_constantTerm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K hK
  by_cases he : (doubledEnergy I.val : ℤ) - doubledEnergy K.val = shift W k
  · have he' : (doubledEnergy K.val : ℤ) - doubledEnergy J.val = -shift W k := by omega
    simp only [he, ite_true, diagonal, he', mul_assoc]
  · have he' : (doubledEnergy K.val : ℤ) - doubledEnergy J.val ≠ -shift W k := by omega
    simp only [he, ite_false, diagonal, he', zero_mul, mul_zero]

theorem reverse_weighted_matrix_constantTerm (L W : ℕ) (A B I J : Index L)
    (hW : 0 < W) (hw : doubledEnergy A.val ≤ W)
    (hparity : doubledEnergy A.val % 2 = W % 2)
    (hIJ : doubledEnergy I.val = doubledEnergy J.val) :
    ((LaurentPolynomial.T (R := R) 2 - 1) ^ ((W + doubledEnergy A.val) / 2 - 1) *
        (constantMatrix R L B * scaledMatrix R L A) I J).coeff 0 =
      ∑ k : Fin W, (weightCoefficient W (doubledEnergy A.val) k : R) *
        (diagonal R L (-shift W k) (Pi.single B 1) *
          diagonal R L (shift W k) (Pi.single A 1)) I J := by
  classical
  rw [← weightPolynomial_eq_power R W (doubledEnergy A.val) hW hw hparity,
    Matrix.mul_apply, Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  have hterm (K : Index L) :
      (weightPolynomial R W (doubledEnergy A.val) *
        (constantMatrix R L B I K * scaledMatrix R L A K J)).coeff 0 =
      ∑ k : Fin W, if (doubledEnergy K.val : ℤ) - doubledEnergy J.val = shift W k then
        (weightCoefficient W (doubledEnergy A.val) k : R) *
          (matrix R L (Pi.single B 1) I K * matrix R L (Pi.single A 1) K J) else 0 := by
    rw [constantMatrix, scaledMatrix_eq_monomial]
    have he : LaurentPolynomial.C (matrix R L (Pi.single B 1) I K) *
        (LaurentPolynomial.C (matrix R L (Pi.single A 1) K J) *
          LaurentPolynomial.T (R := R)
            ((doubledEnergy K.val : ℤ) - doubledEnergy J.val - doubledEnergy A.val)) =
        LaurentPolynomial.C
            (matrix R L (Pi.single B 1) I K * matrix R L (Pi.single A 1) K J) *
          LaurentPolynomial.T (R := R)
            ((doubledEnergy K.val : ℤ) - doubledEnergy J.val - doubledEnergy A.val) := by
      rw [map_mul]
      ring
    rw [he, weightPolynomial_constantTerm]
  simp only [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K hK
  by_cases he : (doubledEnergy K.val : ℤ) - doubledEnergy J.val = shift W k
  · have he' : (doubledEnergy I.val : ℤ) - doubledEnergy K.val = -shift W k := by omega
    simp only [he, ite_true, diagonal, he', mul_assoc]
  · have he' : (doubledEnergy I.val : ℤ) - doubledEnergy K.val ≠ -shift W k := by omega
    simp only [he, ite_false, diagonal, he', zero_mul, mul_zero]

theorem marked_supercommutator_cast (W w : ℕ) (k : Fin W) (x y : R) :
    (markCoefficient W w k : R) * (y - (sigma W : R) * x) =
      (weightCoefficient W w k : R) * (x - (sigma W : R) * y) := by
  have hm : (markCoefficient W w k : R) =
      -(sigma W : R) * (weightCoefficient W w k : R) := by
    simpa only [Int.coe_castRingHom, Int.cast_mul, Int.cast_neg, weightCoefficient] using
      congrArg (Int.castRingHom R) (markCoefficient_eq_neg_sigma W w k)
  have hs : (sigma W : R) * (sigma W : R) = 1 := by
    simpa only [Int.coe_castRingHom, Int.cast_mul, Int.cast_one] using
      congrArg (Int.castRingHom R) (sigma_mul_self W)
  rw [hm]
  calc
    _ = ((sigma W : R) * (sigma W : R)) * (weightCoefficient W w k : R) * x -
        (sigma W : R) * (weightCoefficient W w k : R) * y := by ring
    _ = _ := by rw [hs]; ring

theorem mark_single (L W : ℕ) (k : Fin W) (A : Index L) :
    mark R L W k (Pi.single A 1) =
      (markCoefficient W (doubledEnergy A.val) k : R) • Pi.single A 1 := by
  classical
  ext B
  by_cases h : B = A
  · subst B
    simp [mark_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
  · simp [mark_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul, h, Ne.symm h]

theorem diagonal_mark_single (L W : ℕ) (k : Fin W) (r : ℤ) (A : Index L) :
    diagonal R L r (mark R L W k (Pi.single A 1)) =
      (markCoefficient W (doubledEnergy A.val) k : R) • diagonal R L r (Pi.single A 1) := by
  rw [mark_single]
  change diagonalLinear R L r
      ((markCoefficient W (doubledEnergy A.val) k : R) • Pi.single A 1) =
    (markCoefficient W (doubledEnergy A.val) k : R) • diagonalLinear R L r (Pi.single A 1)
  simpa only [RingHom.id_apply] using (diagonalLinear R L r).map_smul
    (markCoefficient W (doubledEnergy A.val) k : R) (Pi.single A 1)

theorem marked_entry (L W : ℕ) (A B I J : Index L) (k : Fin W) :
    (diagonal R L (-shift W k) (Pi.single B 1) *
        diagonal R L (shift W k) (mark R L W k (Pi.single A 1))) I J -
      (sigma W : R) *
        (diagonal R L (shift W k) (mark R L W k (Pi.single A 1)) *
          diagonal R L (-shift W k) (Pi.single B 1)) I J =
      (weightCoefficient W (doubledEnergy A.val) k : R) *
        ((diagonal R L (shift W k) (Pi.single A 1) *
            diagonal R L (-shift W k) (Pi.single B 1)) I J -
          (sigma W : R) *
            (diagonal R L (-shift W k) (Pi.single B 1) *
              diagonal R L (shift W k) (Pi.single A 1)) I J) := by
  rw [diagonal_mark_single, mul_smul_comm, smul_mul_assoc]
  simp only [Matrix.smul_apply, smul_eq_mul]
  calc
    _ = (markCoefficient W (doubledEnergy A.val) k : R) *
        ((diagonal R L (-shift W k) (Pi.single B 1) *
            diagonal R L (shift W k) (Pi.single A 1)) I J -
          (sigma W : R) *
            (diagonal R L (shift W k) (Pi.single A 1) *
              diagonal R L (-shift W k) (Pi.single B 1)) I J) := by ring
    _ = _ := marked_supercommutator_cast R W (doubledEnergy A.val) k _ _

theorem opposite_diagonal_product_zero (L : ℕ) (r : ℤ) (v w : State R L) (I J : Index L)
    (hIJ : doubledEnergy I.val ≠ doubledEnergy J.val) :
    (diagonal R L r v * diagonal R L (-r) w) I J = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro K hK
  by_cases h : (doubledEnergy I.val : ℤ) - doubledEnergy K.val = r
  · have h' : (doubledEnergy K.val : ℤ) - doubledEnergy J.val ≠ -r := by omega
    simp [diagonal, h, h']
  · simp [diagonal, h]

theorem singleton_signed_identity (L W : ℕ) (A B I J : Index L)
    (hW : 0 < W) (hB : doubledEnergy B.val = W) (hA : doubledEnergy A.val ≤ W)
    (hparity : doubledEnergy A.val % 2 = W % 2)
    (hcut : doubledEnergy J.val + W ≤ 2 * L) :
    (∑ k : Fin W,
      ((diagonal R L (-shift W k) (Pi.single B 1) *
          diagonal R L (shift W k) (mark R L W k (Pi.single A 1))) I J -
        (sigma W : R) *
          (diagonal R L (shift W k) (mark R L W k (Pi.single A 1)) *
            diagonal R L (-shift W k) (Pi.single B 1)) I J)) =
      (if I = J then (1 : R) else 0) * matrix R L (Pi.single A 1) ⟨∅, by simp⟩ B := by
  classical
  by_cases hIJ : doubledEnergy I.val = doubledEnergy J.val
  · let d := (W + doubledEnergy A.val) / 2 - 1
    have hsum := source_sum_two_le hW hparity
    have hdegree : 2 * d + 2 = sourceEnergy A.val.sort + sourceEnergy B.val.sort := by
      rw [sourceEnergy_sort, sourceEnergy_sort, hB]
      dsimp [d]
      omega
    have hw : sourceEnergy A.val.sort ≤ sourceEnergy B.val.sort := by
      simpa only [sourceEnergy_sort, hB] using hA
    have hc : doubledEnergy I.val + sourceEnergy B.val.sort ≤ 2 * L := by
      simpa only [sourceEnergy_sort, hB, hIJ] using hcut
    have h := weighted_matrix_residue R L A B I J d hdegree hw hIJ hc
    have hp : sourceEnergy A.val.sort % 2 = sourceEnergy B.val.sort % 2 := by
      simpa only [sourceEnergy_sort, hB] using hparity
    have hsign := blockSign_smul R
      (A.val.sort (fun i j : ℕ => i ≤ j)) (B.val.sort (fun i j : ℕ => i ≤ j)) hp
      (((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
        (constantMatrix R L B * scaledMatrix R L A) I J).coeff 0)
    rw [hsign] at h
    simp only [sourceEnergy_sort, hB] at h
    dsimp only [d] at h
    rw [forward_weighted_matrix_constantTerm R L W A B I J hW hA hparity hIJ,
      reverse_weighted_matrix_constantTerm R L W A B I J hW hA hparity hIJ] at h
    calc
      _ = ∑ k : Fin W, (weightCoefficient W (doubledEnergy A.val) k : R) *
          ((diagonal R L (shift W k) (Pi.single A 1) *
              diagonal R L (-shift W k) (Pi.single B 1)) I J -
            (sigma W : R) *
              (diagonal R L (-shift W k) (Pi.single B 1) *
                diagonal R L (shift W k) (Pi.single A 1)) I J) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact marked_entry R L W A B I J k
      _ = _ := by
        rw [← h]
        simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        ring
  · have hne : I ≠ J := by
      intro he
      subst J
      exact hIJ rfl
    rw [if_neg hne, zero_mul]
    apply Finset.sum_eq_zero
    intro k hk
    have h₁ := opposite_diagonal_product_zero R L (-shift W k) (Pi.single B 1)
      (mark R L W k (Pi.single A 1)) I J hIJ
    have h₂ := opposite_diagonal_product_zero R L (shift W k)
      (mark R L W k (Pi.single A 1)) (Pi.single B 1) I J hIJ
    simp only [neg_neg] at h₁
    rw [h₁, h₂, mul_zero, sub_self]

end Lemmata.FockCircuits.FiniteIdentity
