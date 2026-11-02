module

public import Lemmata.FockCircuits.KernelScaling
public import Lemmata.FockCircuits.OperatorMatrix
public import Lemmata.FockCircuits.MatchingResidue

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.FiniteIdentity

abbrev SourceIndex := ℕ ⊕ ℕ

def derivative (i : SourceIndex) : ℕ := Sum.elim id id i

def leftSourceWeight (i : SourceIndex) : ℕ :=
  match i with
  | Sum.inl m => 2 * m + 1
  | Sum.inr _ => 0

def rightSourceWeight (i : SourceIndex) : ℕ :=
  match i with
  | Sum.inl _ => 0
  | Sum.inr m => 2 * m + 1

def sourceEnergy (A : List ℕ) : ℕ := Matching.weight id A

@[simp] theorem sourceEnergy_nil : sourceEnergy [] = 0 := rfl

@[simp] theorem sourceEnergy_cons (m : ℕ) (A : List ℕ) :
    sourceEnergy (m :: A) = 2 * m + 1 + sourceEnergy A := rfl

def IsCrossPair (p : SourceIndex × SourceIndex) : Prop :=
  (∃ m n, p = (Sum.inl m, Sum.inr n)) ∨ (∃ m n, p = (Sum.inr n, Sum.inl m))

def orientPair (p : SourceIndex × SourceIndex) : ℕ × ℕ :=
  match p.1, p.2 with
  | Sum.inr n, Sum.inl m => (m, n)
  | i, j => (derivative i, derivative j)

def orientedPairs (t : Matching.Term SourceIndex) : List (ℕ × ℕ) := t.pairs.map orientPair

theorem orientPair_pole (p : SourceIndex × SourceIndex) :
    (orientPair p).1 + (orientPair p).2 + 1 = derivative p.1 + derivative p.2 + 1 := by
  rcases p with ⟨i, j⟩
  cases i <;> cases j <;> simp [orientPair, derivative, Nat.add_comm]

theorem orientPair_left (p : SourceIndex × SourceIndex) (hp : IsCrossPair p) :
    2 * (orientPair p).1 + 1 = leftSourceWeight p.1 + leftSourceWeight p.2 := by
  rcases hp with ⟨m, n, rfl⟩ | ⟨m, n, rfl⟩ <;>
    simp [orientPair, derivative, leftSourceWeight]

theorem orientPair_right (p : SourceIndex × SourceIndex) (hp : IsCrossPair p) :
    2 * (orientPair p).2 + 1 = rightSourceWeight p.1 + rightSourceWeight p.2 := by
  rcases hp with ⟨m, n, rfl⟩ | ⟨m, n, rfl⟩ <;>
    simp [orientPair, derivative, rightSourceWeight]

theorem orientedPairs_pole (t : Matching.Term SourceIndex) :
    poleSum (orientedPairs t) = Matching.pole derivative t := by
  simp only [poleSum, orientedPairs, Matching.pole, List.map_map, Function.comp_def,
    orientPair_pole]

theorem orientedPairs_left (t : Matching.Term SourceIndex)
    (ht : ∀ p ∈ t.pairs, IsCrossPair p) :
    pairedLeftWeight (orientedPairs t) =
      (t.pairs.map fun p => leftSourceWeight p.1 + leftSourceWeight p.2).sum := by
  simp only [pairedLeftWeight, orientedPairs, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  exact fun p hp => orientPair_left p (ht p hp)

theorem orientedPairs_right (t : Matching.Term SourceIndex)
    (ht : ∀ p ∈ t.pairs, IsCrossPair p) :
    pairedRightWeight (orientedPairs t) =
      (t.pairs.map fun p => rightSourceWeight p.1 + rightSourceWeight p.2).sum := by
  simp only [pairedRightWeight, orientedPairs, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  exact fun p hp => orientPair_right p (ht p hp)

theorem forward_pairs_cross {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (A.map Sum.inl) (B.map Sum.inr)) :
    ∀ p ∈ t.pairs, IsCrossPair p := by
  intro p hp
  have hs := Matching.pair_mem_sources ht hp
  obtain ⟨m, hm, he⟩ := List.mem_map.mp hs.1
  obtain ⟨n, hn, hf⟩ := List.mem_map.mp hs.2
  left
  refine ⟨m, n, ?_⟩
  exact Prod.ext he.symm hf.symm

theorem reverse_pairs_cross {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (B.map Sum.inr) (A.map Sum.inl)) :
    ∀ p ∈ t.pairs, IsCrossPair p := by
  intro p hp
  have hs := Matching.pair_mem_sources ht hp
  obtain ⟨n, hn, he⟩ := List.mem_map.mp hs.1
  obtain ⟨m, hm, hf⟩ := List.mem_map.mp hs.2
  right
  refine ⟨m, n, ?_⟩
  exact Prod.ext he.symm hf.symm

theorem forward_left_conservation {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (A.map Sum.inl) (B.map Sum.inr)) :
    (t.remaining.map leftSourceWeight).sum + pairedLeftWeight (orientedPairs t) = sourceEnergy A := by
  have h := Matching.term_weight_conservation leftSourceWeight ht
  rw [← orientedPairs_left t (forward_pairs_cross ht)] at h
  simpa [sourceEnergy, Matching.weight, List.map_map, Function.comp_def, leftSourceWeight] using h

theorem forward_right_conservation {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (A.map Sum.inl) (B.map Sum.inr)) :
    (t.remaining.map rightSourceWeight).sum + pairedRightWeight (orientedPairs t) = sourceEnergy B := by
  have h := Matching.term_weight_conservation rightSourceWeight ht
  rw [← orientedPairs_right t (forward_pairs_cross ht)] at h
  simpa [sourceEnergy, Matching.weight, List.map_map, Function.comp_def, rightSourceWeight] using h

theorem reverse_left_conservation {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (B.map Sum.inr) (A.map Sum.inl)) :
    (t.remaining.map leftSourceWeight).sum + pairedLeftWeight (orientedPairs t) = sourceEnergy A := by
  have h := Matching.term_weight_conservation leftSourceWeight ht
  rw [← orientedPairs_left t (reverse_pairs_cross ht)] at h
  simpa [sourceEnergy, Matching.weight, List.map_map, Function.comp_def, leftSourceWeight] using h

theorem reverse_right_conservation {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (B.map Sum.inr) (A.map Sum.inl)) :
    (t.remaining.map rightSourceWeight).sum + pairedRightWeight (orientedPairs t) = sourceEnergy B := by
  have h := Matching.term_weight_conservation rightSourceWeight ht
  rw [← orientedPairs_right t (reverse_pairs_cross ht)] at h
  simpa [sourceEnergy, Matching.weight, List.map_map, Function.comp_def, rightSourceWeight] using h

theorem sourceWeight_sum (A : List SourceIndex) :
    (A.map sourceWeight).sum = ((A.map leftSourceWeight).sum : ℤ) := by
  induction A with
  | nil => simp
  | cons i A ih =>
    cases i <;> simp [sourceWeight, leftSourceWeight, ih, Nat.cast_add,
      Nat.cast_mul, Nat.cast_one]

theorem forward_unmatched_weight {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (A.map Sum.inl) (B.map Sum.inr)) :
    (t.remaining.map sourceWeight).sum =
      ((sourceEnergy A - pairedLeftWeight (orientedPairs t) : ℕ) : ℤ) := by
  rw [sourceWeight_sum]
  have h := forward_left_conservation ht
  have he : (t.remaining.map leftSourceWeight).sum =
      sourceEnergy A - pairedLeftWeight (orientedPairs t) := by omega
  rw [he]

theorem reverse_unmatched_weight {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (B.map Sum.inr) (A.map Sum.inl)) :
    (t.remaining.map sourceWeight).sum =
      ((sourceEnergy A - pairedLeftWeight (orientedPairs t) : ℕ) : ℤ) := by
  rw [sourceWeight_sum]
  have h := reverse_left_conservation ht
  have he : (t.remaining.map leftSourceWeight).sum =
      sourceEnergy A - pairedLeftWeight (orientedPairs t) := by omega
  rw [he]

theorem sourceEnergy_mod_two (A : List ℕ) : sourceEnergy A % 2 = A.length % 2 := by
  induction A with
  | nil => simp
  | cons m A ih =>
    rw [sourceEnergy_cons, List.length_cons]
    omega

theorem weight_derivative_left (A : List ℕ) :
    Matching.weight derivative (A.map Sum.inl) = sourceEnergy A := by
  simp [Matching.weight, sourceEnergy, List.map_map, Function.comp_def, derivative]

theorem weight_derivative_right (A : List ℕ) :
    Matching.weight derivative (A.map Sum.inr) = sourceEnergy A := by
  simp [Matching.weight, sourceEnergy, List.map_map, Function.comp_def, derivative]

theorem forward_partial_pole {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (A.map Sum.inl) (B.map Sum.inr))
    (hne : t.remaining ≠ []) (d : ℕ) (hdegree : 2 * d + 2 = sourceEnergy A + sourceEnergy B) :
    poleSum (orientedPairs t) ≤ d := by
  have hparity : Even ((A.map (Sum.inl : ℕ → SourceIndex)).length +
      (B.map (Sum.inr : ℕ → SourceIndex)).length) := by
    rw [Nat.even_iff]
    simp only [List.length_map]
    have hA := sourceEnergy_mod_two A
    have hB := sourceEnergy_mod_two B
    omega
  have h := Matching.incomplete_pole_bound derivative ht hparity hne
  rw [weight_derivative_left, weight_derivative_right, ← orientedPairs_pole] at h
  omega

theorem reverse_partial_pole {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (B.map Sum.inr) (A.map Sum.inl))
    (hne : t.remaining ≠ []) (d : ℕ) (hdegree : 2 * d + 2 = sourceEnergy A + sourceEnergy B) :
    poleSum (orientedPairs t) ≤ d := by
  have hparity : Even ((B.map (Sum.inr : ℕ → SourceIndex)).length +
      (A.map (Sum.inl : ℕ → SourceIndex)).length) := by
    rw [Nat.even_iff]
    simp only [List.length_map]
    have hA := sourceEnergy_mod_two A
    have hB := sourceEnergy_mod_two B
    omega
  have h := Matching.incomplete_pole_bound derivative ht hparity hne
  rw [weight_derivative_right, weight_derivative_left, ← orientedPairs_pole] at h
  omega

theorem forward_full_pole {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (A.map Sum.inl) (B.map Sum.inr))
    (hempty : t.remaining = []) (d : ℕ) (hdegree : 2 * d + 2 = sourceEnergy A + sourceEnergy B) :
    poleSum (orientedPairs t) = d + 1 := by
  have h := Matching.term_energy derivative ht
  rw [hempty, Matching.weight_nil, weight_derivative_left, weight_derivative_right,
    ← orientedPairs_pole] at h
  omega

theorem reverse_full_pole {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (B.map Sum.inr) (A.map Sum.inl))
    (hempty : t.remaining = []) (d : ℕ) (hdegree : 2 * d + 2 = sourceEnergy A + sourceEnergy B) :
    poleSum (orientedPairs t) = d + 1 := by
  have h := Matching.term_energy derivative ht
  rw [hempty, Matching.weight_nil, weight_derivative_right, weight_derivative_left,
    ← orientedPairs_pole] at h
  omega

variable (R : Type*) [CommRing R]

noncomputable def normalCoefficient (L : ℕ) (A : List SourceIndex) (I J : Finset ℕ) :
    LaurentPolynomial R :=
  (colourBasis (LaurentPolynomial R)).repr
    (Fock.normalList (LaurentPolynomial R)
      (TwoColour.colouredList (LaurentPolynomial R) L (A.map (sourceCoefficients R L)))
      (TwoColour.kernel (LaurentPolynomial R) L)) (colourIndex I J)

theorem forward_partial_coefficient_bounds (L : ℕ) {A B : List ℕ}
    {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (A.map Sum.inl) (B.map Sum.inr))
    (I J : Finset ℕ) (hIJ : doubledEnergy I = doubledEnergy J) :
    UpperBound R (normalCoefficient R L t.remaining I J)
        ((doubledEnergy I : ℤ) -
          (sourceEnergy A - pairedLeftWeight (orientedPairs t) : ℕ)) ∧
      LowerBound R (normalCoefficient R L t.remaining I J)
        (-(doubledEnergy I : ℤ) -
          (sourceEnergy A - pairedLeftWeight (orientedPairs t) : ℕ)) := by
  have h := normal_remainder_coefficient_bounds R L t.remaining I J
  dsimp only at h
  rw [forward_unmatched_weight ht, ← hIJ] at h
  exact h

theorem reverse_partial_coefficient_bounds (L : ℕ) {A B : List ℕ}
    {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (B.map Sum.inr) (A.map Sum.inl))
    (I J : Finset ℕ) (hIJ : doubledEnergy I = doubledEnergy J) :
    UpperBound R (normalCoefficient R L t.remaining I J)
        ((doubledEnergy I : ℤ) -
          (sourceEnergy A - pairedLeftWeight (orientedPairs t) : ℕ)) ∧
      LowerBound R (normalCoefficient R L t.remaining I J)
        (-(doubledEnergy I : ℤ) -
          (sourceEnergy A - pairedLeftWeight (orientedPairs t) : ℕ)) := by
  have h := normal_remainder_coefficient_bounds R L t.remaining I J
  dsimp only at h
  rw [reverse_unmatched_weight ht, ← hIJ] at h
  exact h

theorem coordinateDual_leftVectors (L : ℕ) (a b : Fin L → R) :
    Fock.coordinateDual R (TwoColour.leftVector R L a) (TwoColour.leftVector R L b) =
      ∑ i, a i * b i := by
  change Fock.coordinateDual R (∑ i : Fin L, a i • Finsupp.single (2 * (i : ℕ)) (1 : R))
    (TwoColour.leftVector R L b) = _
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Fock.coordinateDual_single, one_mul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← leftParticle_finiteVector, leftParticle_even, finiteVector_apply]

noncomputable def normalSource (L : ℕ) (i : SourceIndex) :
    OneParticle (LaurentPolynomial R) × OneParticle (LaurentPolynomial R) :=
  (TwoColour.leftVector (LaurentPolynomial R) L (sourceCoefficients R L i).1,
    TwoColour.leftVector (LaurentPolynomial R) L (sourceCoefficients R L i).2)

theorem normalSource_forward (L m n : ℕ) :
    Fock.coordinateDual (LaurentPolynomial R) (normalSource R L (Sum.inl m)).2
        (normalSource R L (Sum.inr n)).1 = forwardTail R 0 L m n := by
  rw [normalSource, normalSource, coordinateDual_leftVectors]
  change (∑ k : Fin L, scaledNegative R m k *
      LaurentPolynomial.C (positiveCoefficient n k : R)) = forwardTail R 0 L m n
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => scaledNegative R m k * LaurentPolynomial.C (positiveCoefficient n k : R)) L]
  simp only [forwardTail, Nat.Ico_zero_eq_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [scaledNegative, forwardMonomial, Int.cast_mul, map_mul]
  ring

theorem normalSource_reverse (L m n : ℕ) :
    Fock.coordinateDual (LaurentPolynomial R) (normalSource R L (Sum.inr n)).2
        (normalSource R L (Sum.inl m)).1 = reverseTail R 0 L m n := by
  rw [normalSource, normalSource, coordinateDual_leftVectors]
  change (∑ k : Fin L, LaurentPolynomial.C (negativeCoefficient n k : R) *
      scaledPositive R m k) = reverseTail R 0 L m n
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => LaurentPolynomial.C (negativeCoefficient n k : R) * scaledPositive R m k) L]
  simp only [reverseTail, Nat.Ico_zero_eq_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [scaledPositive, reverseMonomial, Int.cast_mul, map_mul]
  ring

theorem normalSource_list (L : ℕ) (A : List SourceIndex) :
    A.map (normalSource R L) =
      TwoColour.colouredList (LaurentPolynomial R) L (A.map (sourceCoefficients R L)) := by
  simp only [TwoColour.colouredList, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i hi
  rfl

theorem forward_matching_coefficient (L : ℕ) {A B : List ℕ}
    {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (A.map Sum.inl) (B.map Sum.inr)) :
    Matching.coefficient (LaurentPolynomial R)
        (fun i j => Fock.coordinateDual (LaurentPolynomial R)
          (normalSource R L i).2 (normalSource R L j).1) t =
      LaurentPolynomial.C (t.sign : R) *
        ((orientedPairs t).map fun p => forwardTail R 0 L p.1 p.2).prod := by
  unfold Matching.coefficient
  have hs : (t.sign : LaurentPolynomial R) = LaurentPolynomial.C (t.sign : R) := by simp
  rw [hs]
  congr 1
  unfold orientedPairs
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  have h := Matching.pair_mem_sources ht hp
  obtain ⟨m, hm, hi⟩ := List.mem_map.mp h.1
  obtain ⟨n, hn, hj⟩ := List.mem_map.mp h.2
  simp only [Function.comp_apply]
  have hp' : p = (Sum.inl m, Sum.inr n) := Prod.ext hi.symm hj.symm
  rw [hp']
  simpa [orientPair, derivative] using normalSource_forward R L m n

theorem reverse_matching_coefficient (L : ℕ) {A B : List ℕ}
    {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (B.map Sum.inr) (A.map Sum.inl)) :
    Matching.coefficient (LaurentPolynomial R)
        (fun i j => Fock.coordinateDual (LaurentPolynomial R)
          (normalSource R L i).2 (normalSource R L j).1) t =
      LaurentPolynomial.C (t.sign : R) *
        ((orientedPairs t).map fun p => reverseTail R 0 L p.1 p.2).prod := by
  unfold Matching.coefficient
  have hs : (t.sign : LaurentPolynomial R) = LaurentPolynomial.C (t.sign : R) := by simp
  rw [hs]
  congr 1
  unfold orientedPairs
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  have h := Matching.pair_mem_sources ht hp
  obtain ⟨n, hn, hi⟩ := List.mem_map.mp h.1
  obtain ⟨m, hm, hj⟩ := List.mem_map.mp h.2
  simp only [Function.comp_apply]
  have hp' : p = (Sum.inr n, Sum.inl m) := Prod.ext hi.symm hj.symm
  rw [hp']
  simpa [orientPair, derivative] using normalSource_reverse R L m n

theorem forward_term_replacement (L : ℕ) {A B : List ℕ}
    {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (A.map Sum.inl) (B.map Sum.inr)) (hne : t.remaining ≠ [])
    (d : ℕ) (hdegree : 2 * d + 2 = sourceEnergy A + sourceEnergy B)
    (hw : sourceEnergy A ≤ sourceEnergy B) (I J : Finset ℕ)
    (hIJ : doubledEnergy I = doubledEnergy J)
    (hcut : doubledEnergy I + sourceEnergy B ≤ 2 * L) :
    (((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
        ((orientedPairs t).map fun p => forwardTail R 0 L p.1 p.2).prod *
        normalCoefficient R L t.remaining I J).coeff 0 =
      ((LaurentPolynomial.T (R := R) 2 - 1) ^ (d - poleSum (orientedPairs t)) *
        ((orientedPairs t).map (pairConstant R)).prod *
        normalCoefficient R L t.remaining I J).coeff 0) := by
  have hleft := forward_left_conservation ht
  have hright := forward_right_conservation ht
  have hv := forward_partial_coefficient_bounds R L ht I J hIJ
  exact (cutoff_partial_replacements R L (doubledEnergy I) (sourceEnergy B)
    (sourceEnergy A) d (orientedPairs t) (forward_partial_pole ht hne d hdegree)
    (by omega) (by omega) (by omega) hw hcut _ hv.1 hv.2).1

theorem reverse_term_replacement (L : ℕ) {A B : List ℕ}
    {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (B.map Sum.inr) (A.map Sum.inl)) (hne : t.remaining ≠ [])
    (d : ℕ) (hdegree : 2 * d + 2 = sourceEnergy A + sourceEnergy B)
    (hw : sourceEnergy A ≤ sourceEnergy B) (I J : Finset ℕ)
    (hIJ : doubledEnergy I = doubledEnergy J)
    (hcut : doubledEnergy I + sourceEnergy B ≤ 2 * L) :
    (((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
        ((orientedPairs t).map fun p => reverseTail R 0 L p.1 p.2).prod *
        normalCoefficient R L t.remaining I J).coeff 0 =
      ((LaurentPolynomial.T (R := R) 2 - 1) ^ (d - poleSum (orientedPairs t)) *
        ((orientedPairs t).map fun p => -pairConstant R p).prod *
        normalCoefficient R L t.remaining I J).coeff 0) := by
  have hleft := reverse_left_conservation ht
  have hright := reverse_right_conservation ht
  have hv := reverse_partial_coefficient_bounds R L ht I J hIJ
  exact (cutoff_partial_replacements R L (doubledEnergy I) (sourceEnergy B)
    (sourceEnergy A) d (orientedPairs t) (reverse_partial_pole ht hne d hdegree)
    (by omega) (by omega) (by omega) hw hcut _ hv.1 hv.2).2

theorem matrix_single_vacuum (L : ℕ) (A B : Index L) :
    matrix R L (Pi.single A 1) ⟨∅, by simp⟩ B =
      Fock.augmentation R
        (Fock.normalList R (plainList R L (sourceWord R L A)) (Fock.basis R B.val)) := by
  rw [matrix_single_eq_normalList, one_mul, Fock.augmentation_eq_basis_empty]

theorem constantTerm_C_mul (c : R) (p : LaurentPolynomial R) :
    (LaurentPolynomial.C c * p).coeff 0 = c * p.coeff 0 := by
  simp only [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply,
    neg_zero, zero_add]

theorem normalCoefficient_nil (L : ℕ) (I J : Finset ℕ) :
    normalCoefficient R L [] I J =
      LaurentPolynomial.C ((colourBasis R).repr (TwoColour.kernel R L) (colourIndex I J)) := by
  simp only [normalCoefficient, List.map_nil, TwoColour.colouredList,
    Fock.normalList_nil, LinearMap.id_coe, id_eq, kernel_diagonal_coefficient]
  by_cases hIJ : I = J
  · subst J
    by_cases hI : I ⊆ Finset.range L <;> simp [hI]
  · simp [hIJ]

theorem full_forward_term_zero (L : ℕ) {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (A.map Sum.inl) (B.map Sum.inr)) (hempty : t.remaining = [])
    (d : ℕ) (hdegree : 2 * d + 2 = sourceEnergy A + sourceEnergy B) (I J : Finset ℕ) :
    ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
        Matching.coefficient (LaurentPolynomial R)
          (fun i j => Fock.coordinateDual (LaurentPolynomial R)
            (normalSource R L i).2 (normalSource R L j).1) t *
        normalCoefficient R L t.remaining I J).coeff 0 = 0 := by
  rw [forward_matching_coefficient R L ht, hempty, normalCoefficient_nil]
  have hpoly : (LaurentPolynomial.T (R := R) 2 - 1) ^ d *
      (LaurentPolynomial.C (t.sign : R) *
        ((orientedPairs t).map fun p => forwardTail R 0 L p.1 p.2).prod) *
      LaurentPolynomial.C ((colourBasis R).repr (TwoColour.kernel R L) (colourIndex I J)) =
      LaurentPolynomial.C
        ((t.sign : R) * (colourBasis R).repr (TwoColour.kernel R L) (colourIndex I J)) *
        ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
          ((orientedPairs t).map fun p => forwardTail R 0 L p.1 p.2).prod) := by
    rw [map_mul]
    ring
  rw [hpoly, constantTerm_C_mul,
    full_forward_constantTerm R L (orientedPairs t) d (forward_full_pole ht hempty d hdegree),
    mul_zero]

theorem full_reverse_term_value (L : ℕ) {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (B.map Sum.inr) (A.map Sum.inl)) (hempty : t.remaining = [])
    (d : ℕ) (hw : sourceEnergy A ≤ sourceEnergy B) (I J : Finset ℕ)
    (hcut : doubledEnergy I + sourceEnergy B ≤ 2 * L) :
    ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
        Matching.coefficient (LaurentPolynomial R)
          (fun i j => Fock.coordinateDual (LaurentPolynomial R)
            (normalSource R L i).2 (normalSource R L j).1) t *
        normalCoefficient R L t.remaining I J).coeff 0 =
      ((t.sign : R) * (colourBasis R).repr (TwoColour.kernel R L) (colourIndex I J)) *
        ((-1 : R) ^ d *
          ((orientedPairs t).map fun p => (Fock.contractionCoefficient p.2 p.1 : R)).prod) := by
  have hleft := reverse_left_conservation ht
  have hP : ∀ p ∈ orientedPairs t, p.1 < L := by
    intro p hp
    have h := pairedLeftWeight_mem hp
    omega
  rw [reverse_matching_coefficient R L ht, hempty, normalCoefficient_nil]
  have hpoly : (LaurentPolynomial.T (R := R) 2 - 1) ^ d *
      (LaurentPolynomial.C (t.sign : R) *
        ((orientedPairs t).map fun p => reverseTail R 0 L p.1 p.2).prod) *
      LaurentPolynomial.C ((colourBasis R).repr (TwoColour.kernel R L) (colourIndex I J)) =
      LaurentPolynomial.C
        ((t.sign : R) * (colourBasis R).repr (TwoColour.kernel R L) (colourIndex I J)) *
        ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
          ((orientedPairs t).map fun p => reverseTail R 0 L p.1 p.2).prod) := by
    rw [map_mul]
    ring
  rw [hpoly, constantTerm_C_mul, full_reverse_constantTerm R L (orientedPairs t) d hP]

noncomputable def kernelEntry (L : ℕ) (I J : Finset ℕ) :
    Module.End (LaurentPolynomial R) (Fock (LaurentPolynomial R)) →ₗ[LaurentPolynomial R]
      LaurentPolynomial R :=
  (Finsupp.lapply (colourIndex I J)).comp
    ((colourBasis (LaurentPolynomial R)).repr.toLinearMap.comp
      (LinearMap.applyₗ (R := LaurentPolynomial R) (TwoColour.kernel (LaurentPolynomial R) L)))

theorem kernelEntry_normalList (L : ℕ) (A : List SourceIndex) (I J : Finset ℕ) :
    kernelEntry R L I J (Fock.normalList (LaurentPolynomial R) (A.map (normalSource R L))) =
      normalCoefficient R L A I J := by
  change (colourBasis (LaurentPolynomial R)).repr
    (Fock.normalList (LaurentPolynomial R) (A.map (normalSource R L))
      (TwoColour.kernel (LaurentPolynomial R) L)) (colourIndex I J) = _
  rw [normalSource_list]
  rfl

theorem crossPole_sum (t : Matching.Term SourceIndex) :
    (t.pairs.map fun p => Matching.crossPole p.1 p.2).sum = poleSum (orientedPairs t) := by
  rw [orientedPairs_pole]
  rfl

noncomputable def commonTerm (L d : ℕ) (t : Matching.Term SourceIndex) (I J : Finset ℕ) :
    LaurentPolynomial R :=
  (if poleSum (orientedPairs t) ≤ d then
    (LaurentPolynomial.T (R := R) 2 - 1) ^ (d - poleSum (orientedPairs t)) *
      Matching.coefficient (LaurentPolynomial R)
        (Matching.crossGamma (LaurentPolynomial R)
          (fun m n => (Fock.contractionCoefficient m n : LaurentPolynomial R))) t else 0) *
    normalCoefficient R L t.remaining I J

theorem kernelEntry_selectedEvaluate (L d : ℕ) (T : List (Matching.Term SourceIndex))
    (I J : Finset ℕ) :
    kernelEntry R L I J
        (Matching.selectedEvaluate (LaurentPolynomial R)
          (LaurentPolynomial.T (R := R) 2 - 1) d
          (Matching.crossGamma (LaurentPolynomial R)
            (fun m n => (Fock.contractionCoefficient m n : LaurentPolynomial R)))
          Matching.crossPole (normalSource R L) T) =
      (T.map fun t => commonTerm R L d t I J).sum := by
  simp only [Matching.selectedEvaluate, map_list_sum, List.map_map, Function.comp_def,
    map_smul, kernelEntry_normalList, crossPole_sum, commonTerm, smul_eq_mul]

theorem common_sum_exchange (L d : ℕ) (A B : List ℕ) (I J : Finset ℕ) :
    ((Matching.terms (A.map Sum.inl) (B.map Sum.inr)).map
      fun t => commonTerm R L d t I J).sum =
      ((-1 : ℤˣ) ^ (A.length * B.length)) •
        ((Matching.terms (B.map Sum.inr) (A.map Sum.inl)).map
          fun t => commonTerm R L d t I J).sum := by
  have h := Matching.selected_matching_exchange (LaurentPolynomial R)
    (LaurentPolynomial.T (R := R) 2 - 1) d
    (fun m n => (Fock.contractionCoefficient m n : LaurentPolynomial R))
    (normalSource R L) A B
  have he := congrArg (kernelEntry R L I J) h
  simpa only [Units.smul_def, map_zsmul, kernelEntry_selectedEvaluate] using he

theorem forward_common_coefficient {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (A.map Sum.inl) (B.map Sum.inr)) :
    Matching.coefficient (LaurentPolynomial R)
        (Matching.crossGamma (LaurentPolynomial R)
          (fun m n => (Fock.contractionCoefficient m n : LaurentPolynomial R))) t =
      LaurentPolynomial.C (t.sign : R) * ((orientedPairs t).map (pairConstant R)).prod := by
  unfold Matching.coefficient
  have hs : (t.sign : LaurentPolynomial R) = LaurentPolynomial.C (t.sign : R) := by simp
  rw [hs]
  congr 1
  unfold orientedPairs
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  have h := Matching.pair_mem_sources ht hp
  obtain ⟨m, hm, hi⟩ := List.mem_map.mp h.1
  obtain ⟨n, hn, hj⟩ := List.mem_map.mp h.2
  have hp' : p = (Sum.inl m, Sum.inr n) := Prod.ext hi.symm hj.symm
  rw [hp']
  simp [Matching.crossGamma, orientPair, derivative, pairConstant]

theorem reverse_common_coefficient {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (B.map Sum.inr) (A.map Sum.inl)) :
    Matching.coefficient (LaurentPolynomial R)
        (Matching.crossGamma (LaurentPolynomial R)
          (fun m n => (Fock.contractionCoefficient m n : LaurentPolynomial R))) t =
      LaurentPolynomial.C (t.sign : R) *
        ((orientedPairs t).map fun p => -pairConstant R p).prod := by
  unfold Matching.coefficient
  have hs : (t.sign : LaurentPolynomial R) = LaurentPolynomial.C (t.sign : R) := by simp
  rw [hs]
  congr 1
  unfold orientedPairs
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  have h := Matching.pair_mem_sources ht hp
  obtain ⟨n, hn, hi⟩ := List.mem_map.mp h.1
  obtain ⟨m, hm, hj⟩ := List.mem_map.mp h.2
  have hp' : p = (Sum.inr n, Sum.inl m) := Prod.ext hi.symm hj.symm
  rw [hp']
  simp [Matching.crossGamma, orientPair, derivative, pairConstant]

theorem constantTerm_weighted_C (c : R) (s p v : LaurentPolynomial R) :
    (s * (LaurentPolynomial.C c * p) * v).coeff 0 = c * (s * p * v).coeff 0 := by
  have he : s * (LaurentPolynomial.C c * p) * v = LaurentPolynomial.C c * (s * p * v) := by ring
  rw [he, constantTerm_C_mul]

noncomputable def actualTerm (L d : ℕ) (t : Matching.Term SourceIndex) (I J : Finset ℕ) :
    LaurentPolynomial R :=
  (LaurentPolynomial.T (R := R) 2 - 1) ^ d *
    Matching.coefficient (LaurentPolynomial R)
      (fun i j => Fock.coordinateDual (LaurentPolynomial R)
        (normalSource R L i).2 (normalSource R L j).1) t *
    normalCoefficient R L t.remaining I J

theorem forward_term_constantTerm (L : ℕ) {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (A.map Sum.inl) (B.map Sum.inr))
    (d : ℕ) (hdegree : 2 * d + 2 = sourceEnergy A + sourceEnergy B)
    (hw : sourceEnergy A ≤ sourceEnergy B) (I J : Finset ℕ)
    (hIJ : doubledEnergy I = doubledEnergy J)
    (hcut : doubledEnergy I + sourceEnergy B ≤ 2 * L) :
    (actualTerm R L d t I J).coeff 0 = (commonTerm R L d t I J).coeff 0 := by
  classical
  by_cases hempty : t.remaining = []
  · have hp := forward_full_pole ht hempty d hdegree
    have hnot : ¬poleSum (orientedPairs t) ≤ d := by omega
    rw [actualTerm, full_forward_term_zero R L ht hempty d hdegree I J]
    simp only [commonTerm, hnot, ite_false, zero_mul, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply]
  · have hp := forward_partial_pole ht hempty d hdegree
    rw [actualTerm, forward_matching_coefficient R L ht,
      constantTerm_weighted_C, commonTerm, if_pos hp,
      forward_common_coefficient R ht, constantTerm_weighted_C]
    rw [forward_term_replacement R L ht hempty d hdegree hw I J hIJ hcut]

noncomputable def reverseScalar (L d : ℕ) (t : Matching.Term SourceIndex) (I J : Finset ℕ) : R :=
  if t.remaining = [] then
    ((t.sign : R) * (colourBasis R).repr (TwoColour.kernel R L) (colourIndex I J)) *
      ((-1 : R) ^ d *
        ((orientedPairs t).map fun p => (Fock.contractionCoefficient p.2 p.1 : R)).prod)
  else 0

theorem reverse_term_constantTerm (L : ℕ) {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (B.map Sum.inr) (A.map Sum.inl))
    (d : ℕ) (hdegree : 2 * d + 2 = sourceEnergy A + sourceEnergy B)
    (hw : sourceEnergy A ≤ sourceEnergy B) (I J : Finset ℕ)
    (hIJ : doubledEnergy I = doubledEnergy J)
    (hcut : doubledEnergy I + sourceEnergy B ≤ 2 * L) :
    (actualTerm R L d t I J).coeff 0 =
      (commonTerm R L d t I J).coeff 0 + reverseScalar R L d t I J := by
  classical
  by_cases hempty : t.remaining = []
  · have hp := reverse_full_pole ht hempty d hdegree
    have hnot : ¬poleSum (orientedPairs t) ≤ d := by omega
    rw [actualTerm, full_reverse_term_value R L ht hempty d hw I J hcut]
    simp only [commonTerm, hnot, ite_false, zero_mul, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply, reverseScalar, hempty, ite_true, zero_add]
  · have hp := reverse_partial_pole ht hempty d hdegree
    rw [actualTerm, reverse_matching_coefficient R L ht,
      constantTerm_weighted_C, commonTerm, if_pos hp,
      reverse_common_coefficient R ht, constantTerm_weighted_C,
      reverseScalar, if_neg hempty, add_zero]
    rw [reverse_term_replacement R L ht hempty d hdegree hw I J hIJ hcut]

noncomputable def colourEntry (I J : Finset ℕ) :
    Fock (LaurentPolynomial R) →ₗ[LaurentPolynomial R] LaurentPolynomial R :=
  (Finsupp.lapply (colourIndex I J)).comp (colourBasis (LaurentPolynomial R)).repr.toLinearMap

theorem colourEntry_normalList (L : ℕ) (A : List SourceIndex) (I J : Finset ℕ) :
    colourEntry R I J
        (Fock.normalList (LaurentPolynomial R) (A.map (normalSource R L))
          (TwoColour.kernel (LaurentPolynomial R) L)) = normalCoefficient R L A I J := by
  change kernelEntry R L I J
    (Fock.normalList (LaurentPolynomial R) (A.map (normalSource R L))) = _
  exact kernelEntry_normalList R L A I J

noncomputable def productPolynomial (L d : ℕ) (A B : List SourceIndex) (I J : Finset ℕ) :
    LaurentPolynomial R :=
  (LaurentPolynomial.T (R := R) 2 - 1) ^ d * colourEntry R I J
    (Fock.normalList (LaurentPolynomial R) (A.map (normalSource R L))
      (Fock.normalList (LaurentPolynomial R) (B.map (normalSource R L))
        (TwoColour.kernel (LaurentPolynomial R) L)))

theorem productPolynomial_eq_sum (L d : ℕ) (A B : List SourceIndex) (I J : Finset ℕ) :
    productPolynomial R L d A B I J =
      ((Matching.terms A B).map fun t => actualTerm R L d t I J).sum := by
  let wEntry : Fock (LaurentPolynomial R) →ₗ[LaurentPolynomial R] LaurentPolynomial R :=
    (LinearMap.mulLeft (LaurentPolynomial R) ((LaurentPolynomial.T (R := R) 2 - 1) ^ d)).comp
      (colourEntry R I J)
  change wEntry
    (Fock.normalList (LaurentPolynomial R) (A.map (normalSource R L))
      (Fock.normalList (LaurentPolynomial R) (B.map (normalSource R L))
        (TwoColour.kernel (LaurentPolynomial R) L))) = _
  rw [Matching.normalList_product]
  unfold Matching.evaluate
  rw [map_list_sum]
  simp only [List.map_map, Function.comp_def, map_smul]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  have heta : t.remaining.map (fun a => ((normalSource R L a).1, (normalSource R L a).2)) =
      t.remaining.map (normalSource R L) := by
    apply List.map_congr_left
    intro a ha
    cases a <;> rfl
  rw [heta]
  simp only [wEntry, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    colourEntry_normalList, smul_eq_mul, actualTerm]
  ring

theorem constantTerm_list_sum (P : List (LaurentPolynomial R)) :
    P.sum.coeff 0 = (P.map fun p => p.coeff 0).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
    simp only [List.sum_cons, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      ih, List.map_cons]

theorem forward_product_constantTerm (L : ℕ) (A B : List ℕ) (d : ℕ)
    (hdegree : 2 * d + 2 = sourceEnergy A + sourceEnergy B)
    (hw : sourceEnergy A ≤ sourceEnergy B) (I J : Finset ℕ)
    (hIJ : doubledEnergy I = doubledEnergy J)
    (hcut : doubledEnergy I + sourceEnergy B ≤ 2 * L) :
    (productPolynomial R L d (A.map Sum.inl) (B.map Sum.inr) I J).coeff 0 =
      (((Matching.terms (A.map Sum.inl) (B.map Sum.inr)).map
        fun t => commonTerm R L d t I J).sum).coeff 0 := by
  rw [productPolynomial_eq_sum, constantTerm_list_sum, constantTerm_list_sum]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  exact forward_term_constantTerm R L ht d hdegree hw I J hIJ hcut

theorem reverse_product_constantTerm (L : ℕ) (A B : List ℕ) (d : ℕ)
    (hdegree : 2 * d + 2 = sourceEnergy A + sourceEnergy B)
    (hw : sourceEnergy A ≤ sourceEnergy B) (I J : Finset ℕ)
    (hIJ : doubledEnergy I = doubledEnergy J)
    (hcut : doubledEnergy I + sourceEnergy B ≤ 2 * L) :
    (productPolynomial R L d (B.map Sum.inr) (A.map Sum.inl) I J).coeff 0 =
      (((Matching.terms (B.map Sum.inr) (A.map Sum.inl)).map
        fun t => commonTerm R L d t I J).sum).coeff 0 +
      ((Matching.terms (B.map Sum.inr) (A.map Sum.inl)).map
        fun t => reverseScalar R L d t I J).sum := by
  rw [productPolynomial_eq_sum, constantTerm_list_sum, constantTerm_list_sum]
  simp only [List.map_map, Function.comp_def]
  have he : ((Matching.terms (B.map Sum.inr) (A.map Sum.inl)).map
      fun t => (actualTerm R L d t I J).coeff 0).sum =
      ((Matching.terms (B.map Sum.inr) (A.map Sum.inl)).map
        fun t => (commonTerm R L d t I J).coeff 0 + reverseScalar R L d t I J).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro t ht
    exact reverse_term_constantTerm R L ht d hdegree hw I J hIJ hcut
  rw [he, List.sum_map_add]

theorem product_residue (L : ℕ) (A B : List ℕ) (d : ℕ)
    (hdegree : 2 * d + 2 = sourceEnergy A + sourceEnergy B)
    (hw : sourceEnergy A ≤ sourceEnergy B) (I J : Finset ℕ)
    (hIJ : doubledEnergy I = doubledEnergy J)
    (hcut : doubledEnergy I + sourceEnergy B ≤ 2 * L) :
    (productPolynomial R L d (A.map Sum.inl) (B.map Sum.inr) I J).coeff 0 -
        ((-1 : ℤˣ) ^ (A.length * B.length)) •
          (productPolynomial R L d (B.map Sum.inr) (A.map Sum.inl) I J).coeff 0 =
      - (((-1 : ℤˣ) ^ (A.length * B.length)) •
        ((Matching.terms (B.map Sum.inr) (A.map Sum.inl)).map
          fun t => reverseScalar R L d t I J).sum) := by
  have hc : (((Matching.terms (A.map Sum.inl) (B.map Sum.inr)).map
      fun t => commonTerm R L d t I J).sum).coeff 0 =
      ((-1 : ℤˣ) ^ (A.length * B.length)) •
        (((Matching.terms (B.map Sum.inr) (A.map Sum.inl)).map
          fun t => commonTerm R L d t I J).sum).coeff 0 := by
    simpa only [Units.smul_def, AddMonoidAlgebra.coeff_smul_apply] using
      congrArg (fun p : LaurentPolynomial R => p.coeff 0) (common_sum_exchange R L d A B I J)
  rw [forward_product_constantTerm R L A B d hdegree hw I J hIJ hcut,
    reverse_product_constantTerm R L A B d hdegree hw I J hIJ hcut, hc, smul_add]
  abel

noncomputable def augmentationEntry : Module.End R (Fock R) →ₗ[R] R :=
  (Fock.augmentation R).toLinearMap.comp (LinearMap.applyₗ (R := R) (1 : Fock R))

theorem augmentationEntry_normalList (A : List (OneParticle R × OneParticle R)) :
    augmentationEntry R (Fock.normalList R A) = if A = [] then 1 else 0 :=
  Fock.augmentation_normalList_one R A

noncomputable def fullMatchingSum (γ : SourceIndex → SourceIndex → R)
    (T : List (Matching.Term SourceIndex)) : R :=
  (T.map fun t => if t.remaining = [] then Matching.coefficient R γ t else 0).sum

theorem augmentationEntry_selected (D : ℕ) (γ : SourceIndex → SourceIndex → R)
    (x : SourceIndex → OneParticle R × OneParticle R) (T : List (Matching.Term SourceIndex))
    (hfull : ∀ t ∈ T, t.remaining = [] → poleSum (orientedPairs t) = D) :
    augmentationEntry R (Matching.selectedEvaluate R 0 D γ Matching.crossPole x T) =
      fullMatchingSum R γ T := by
  simp only [Matching.selectedEvaluate, fullMatchingSum, map_list_sum,
    List.map_map, Function.comp_def, map_smul]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [augmentationEntry_normalList]
  simp only [List.map_eq_nil_iff]
  by_cases he : t.remaining = []
  · have hp := hfull t ht he
    simp [crossPole_sum, hp, he, smul_eq_mul]
  · simp [he, smul_eq_mul]

theorem fullMatchingSum_exchange (A B : List ℕ) (d : ℕ)
    (hdegree : 2 * d + 2 = sourceEnergy A + sourceEnergy B) :
    fullMatchingSum R (Matching.crossGamma R (fun m n => (Fock.contractionCoefficient m n : R)))
        (Matching.terms (A.map Sum.inl) (B.map Sum.inr)) =
      ((-1 : ℤˣ) ^ (A.length * B.length)) •
        fullMatchingSum R (Matching.crossGamma R (fun m n => (Fock.contractionCoefficient m n : R)))
          (Matching.terms (B.map Sum.inr) (A.map Sum.inl)) := by
  let x : SourceIndex → OneParticle R × OneParticle R := fun _ => (0, 0)
  have h := Matching.selected_matching_exchange R 0 (d + 1)
    (fun m n => (Fock.contractionCoefficient m n : R)) x A B
  have he := congrArg (augmentationEntry R) h
  rw [Units.smul_def, map_zsmul,
    augmentationEntry_selected R (d + 1) _ x _
      (fun t ht hempty => forward_full_pole ht hempty d hdegree),
    augmentationEntry_selected R (d + 1) _ x _
      (fun t ht hempty => reverse_full_pole ht hempty d hdegree)] at he
  simpa only [Units.smul_def] using he

theorem finiteVector_single (L : ℕ) (i : Fin L) :
    finiteVector R L (Pi.single i (1 : R)) = Finsupp.single (i : ℕ) 1 := by
  classical
  simp [finiteVector, Pi.single_apply]

noncomputable def vacuumSource (L : ℕ) (i : SourceIndex) : OneParticle R × OneParticle R :=
  match i with
  | Sum.inl m =>
    (finiteVector R L (fun k => (positiveCoefficient m k : R)),
      finiteVector R L (fun k => (negativeCoefficient m k : R)))
  | Sum.inr n => (Finsupp.single n 1, 0)

theorem vacuumSource_forward (L m n : ℕ) (hn : n < L) :
    Fock.coordinateDual R (vacuumSource R L (Sum.inl m)).2
        (vacuumSource R L (Sum.inr n)).1 = (Fock.contractionCoefficient m n : R) := by
  change Fock.coordinateDual R (finiteVector R L (fun k => (negativeCoefficient m k : R)))
    (Finsupp.single n 1) = _
  rw [← finiteVector_single R L ⟨n, hn⟩, coordinateDual_finiteVector]
  simp [Pi.single_apply, negativeCoefficient, Fock.contractionCoefficient, Nat.add_comm]

theorem vacuumSource_left_list (L : ℕ) (A : Index L) :
    ((A.val.sort.map Sum.inl).map (vacuumSource R L)) = plainList R L (sourceWord R L A) := by
  simp only [plainList, sourceWord, List.map_map, Function.comp_def, vacuumSource]

theorem vacuumSource_right_vacuum (L : ℕ) (B : Index L) :
    Fock.normalList R ((B.val.sort.map Sum.inr).map (vacuumSource R L)) 1 = Fock.basis R B.val := by
  rw [Fock.normalList_one, Fock.basis_eq_sorted_prod]
  simp only [List.map_map, Function.comp_def, vacuumSource, Fock.generator]
  rfl

theorem vacuum_matching_coefficient (L : ℕ) (A B : Index L) {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (A.val.sort.map Sum.inl) (B.val.sort.map Sum.inr)) :
    Matching.coefficient R
        (fun i j => Fock.coordinateDual R (vacuumSource R L i).2 (vacuumSource R L j).1) t =
      Matching.coefficient R
        (Matching.crossGamma R (fun m n => (Fock.contractionCoefficient m n : R))) t := by
  unfold Matching.coefficient
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro p hp
  have h := Matching.pair_mem_sources ht hp
  obtain ⟨m, hm, hi⟩ := List.mem_map.mp h.1
  obtain ⟨n, hn, hj⟩ := List.mem_map.mp h.2
  have hnB : n ∈ B.val := by simpa only [Finset.mem_sort] using hn
  have hnL : n < L := Finset.mem_range.mp (Finset.mem_powerset.mp B.property hnB)
  have hp' : p = (Sum.inl m, Sum.inr n) := Prod.ext hi.symm hj.symm
  rw [hp']
  simp only [vacuumSource_forward R L m n hnL, Matching.crossGamma]

theorem matrix_single_vacuum_eq_fullMatchingSum (L : ℕ) (A B : Index L) :
    matrix R L (Pi.single A 1) ⟨∅, by simp⟩ B =
      fullMatchingSum R
        (Matching.crossGamma R (fun m n => (Fock.contractionCoefficient m n : R)))
        (Matching.terms (A.val.sort.map Sum.inl) (B.val.sort.map Sum.inr)) := by
  rw [matrix_single_vacuum, ← vacuumSource_left_list, ← vacuumSource_right_vacuum]
  have h := Matching.full_matching_vacuum R
    (fun i => (vacuumSource R L i).1) (fun i => (vacuumSource R L i).2)
    (A.val.sort.map Sum.inl) (B.val.sort.map Sum.inr)
  change Fock.augmentation R
    (Fock.normalList R ((A.val.sort.map Sum.inl).map (vacuumSource R L))
      (Fock.normalList R ((B.val.sort.map Sum.inr).map (vacuumSource R L)) 1)) = _
  rw [h]
  unfold fullMatchingSum
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rw [vacuum_matching_coefficient R L A B ht]

theorem reverse_gamma_coefficient {A B : List ℕ} {t : Matching.Term SourceIndex}
    (ht : t ∈ Matching.terms (B.map Sum.inr) (A.map Sum.inl)) :
    Matching.coefficient R
        (Matching.crossGamma R (fun m n => (Fock.contractionCoefficient m n : R))) t =
      (t.sign : R) *
        ((orientedPairs t).map fun p => -(Fock.contractionCoefficient p.1 p.2 : R)).prod := by
  unfold Matching.coefficient
  congr 1
  unfold orientedPairs
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p hp
  have h := Matching.pair_mem_sources ht hp
  obtain ⟨n, hn, hi⟩ := List.mem_map.mp h.1
  obtain ⟨m, hm, hj⟩ := List.mem_map.mp h.2
  have hp' : p = (Sum.inr n, Sum.inl m) := Prod.ext hi.symm hj.symm
  rw [hp']
  simp only [Matching.crossGamma, Function.comp_def, orientPair, derivative]

theorem neg_contraction_product (P : List (ℕ × ℕ)) :
    (P.map fun p => -(Fock.contractionCoefficient p.1 p.2 : R)).prod =
      (P.map fun p => (Fock.contractionCoefficient p.2 p.1 : R)).prod * (-1 : R) ^ poleSum P := by
  have hn : (P.map fun p => -(Fock.contractionCoefficient p.1 p.2 : R)).prod =
      (-1 : R) ^ P.length * (P.map fun p => (Fock.contractionCoefficient p.1 p.2 : R)).prod := by
    simpa only [List.map_map, Function.comp_def, List.length_map] using
      List.prod_map_neg (P.map fun p => (Fock.contractionCoefficient p.1 p.2 : R))
  rw [hn]
  exact (contraction_product_reversal R P).symm

noncomputable def reverseFullSum (A B : List ℕ) : R :=
  ((Matching.terms (B.map Sum.inr) (A.map Sum.inl)).map fun t =>
    if t.remaining = [] then
      (t.sign : R) *
        ((orientedPairs t).map fun p => (Fock.contractionCoefficient p.2 p.1 : R)).prod
    else 0).sum

theorem reverse_fullMatchingSum (A B : List ℕ) (d : ℕ)
    (hdegree : 2 * d + 2 = sourceEnergy A + sourceEnergy B) :
    fullMatchingSum R (Matching.crossGamma R (fun m n => (Fock.contractionCoefficient m n : R)))
        (Matching.terms (B.map Sum.inr) (A.map Sum.inl)) =
      (-1 : R) ^ (d + 1) * reverseFullSum R A B := by
  unfold fullMatchingSum reverseFullSum
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  by_cases hempty : t.remaining = []
  · have hp := reverse_full_pole ht hempty d hdegree
    rw [if_pos hempty, if_pos hempty, reverse_gamma_coefficient R ht,
      neg_contraction_product, hp]
    ring
  · simp only [hempty, ite_false, mul_zero]

theorem reverseScalar_sum (L d : ℕ) (A B : List ℕ) (I J : Finset ℕ) :
    ((Matching.terms (B.map Sum.inr) (A.map Sum.inl)).map
        fun t => reverseScalar R L d t I J).sum =
      (colourBasis R).repr (TwoColour.kernel R L) (colourIndex I J) *
        ((-1 : R) ^ d * reverseFullSum R A B) := by
  unfold reverseScalar reverseFullSum
  rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  by_cases hempty : t.remaining = []
  · simp only [hempty, ite_true]
    ring
  · simp only [hempty, ite_false, mul_zero]

theorem product_residue_scalar_lists (L : ℕ) (A B : List ℕ) (d : ℕ)
    (hdegree : 2 * d + 2 = sourceEnergy A + sourceEnergy B)
    (hw : sourceEnergy A ≤ sourceEnergy B) (I J : Finset ℕ)
    (hIJ : doubledEnergy I = doubledEnergy J)
    (hcut : doubledEnergy I + sourceEnergy B ≤ 2 * L) :
    (productPolynomial R L d (A.map Sum.inl) (B.map Sum.inr) I J).coeff 0 -
        ((-1 : ℤˣ) ^ (A.length * B.length)) •
          (productPolynomial R L d (B.map Sum.inr) (A.map Sum.inl) I J).coeff 0 =
      (colourBasis R).repr (TwoColour.kernel R L) (colourIndex I J) *
        fullMatchingSum R
          (Matching.crossGamma R (fun m n => (Fock.contractionCoefficient m n : R)))
          (Matching.terms (A.map Sum.inl) (B.map Sum.inr)) := by
  rw [product_residue R L A B d hdegree hw I J hIJ hcut,
    reverseScalar_sum, fullMatchingSum_exchange R A B d hdegree,
    reverse_fullMatchingSum R A B d hdegree]
  simp only [Units.smul_def, zsmul_eq_mul]
  rw [pow_succ]
  ring

theorem product_residue_scalar (L : ℕ) (A B : Index L) (d : ℕ)
    (hdegree : 2 * d + 2 = sourceEnergy A.val.sort + sourceEnergy B.val.sort)
    (hw : sourceEnergy A.val.sort ≤ sourceEnergy B.val.sort) (I J : Finset ℕ)
    (hIJ : doubledEnergy I = doubledEnergy J)
    (hcut : doubledEnergy I + sourceEnergy B.val.sort ≤ 2 * L) :
    (productPolynomial R L d (A.val.sort.map Sum.inl) (B.val.sort.map Sum.inr) I J).coeff 0 -
        ((-1 : ℤˣ) ^ (A.val.sort.length * B.val.sort.length)) •
          (productPolynomial R L d (B.val.sort.map Sum.inr) (A.val.sort.map Sum.inl) I J).coeff 0 =
      (colourBasis R).repr (TwoColour.kernel R L) (colourIndex I J) *
        matrix R L (Pi.single A 1) ⟨∅, by simp⟩ B := by
  rw [matrix_single_vacuum_eq_fullMatchingSum]
  generalize ha : A.val.sort = a at hdegree hw ⊢
  generalize hb : B.val.sort = b at hdegree hw hcut ⊢
  exact product_residue_scalar_lists R L a b d hdegree hw I J hIJ hcut

noncomputable def normalMatrix (L : ℕ) (S : List ((Fin L → R) × (Fin L → R))) :
    Matrix (Index L) (Index L) R :=
  fun I J => (Fock.basis R).repr
    (Fock.normalList R (plainList R L S) (Fock.basis R J.val)) I.val

theorem normalMatrix_mul {L : ℕ} (S T : List ((Fin L → R) × (Fin L → R))) (I J : Index L) :
    (normalMatrix R L S * normalMatrix R L T) I J =
      (Fock.basis R).repr
        (Fock.normalList R (plainList R L S)
          (Fock.normalList R (plainList R L T) (Fock.basis R J.val))) I.val := by
  classical
  rw [Matrix.mul_apply]
  simp only [normalMatrix]
  have hcomp := KernelRectangle.coefficientMatrix_comp_projection (Fock.basis R)
    (fun I : Index L => I.val) (Fock.normalList R (plainList R L T))
    (Fock.normalList R (plainList R L S)) I J
  have hfixed := finiteProjection_normalList R T (Fock.basis R J.val)
    (finiteProjection_basis R J.val (Finset.mem_powerset.mp J.property))
  change (Fock.basis R).repr (Fock.normalList R (plainList R L S)
    (finiteProjection R L (Fock.normalList R (plainList R L T) (Fock.basis R J.val)))) I.val = _ at hcomp
  rw [hfixed] at hcomp
  rw [hcomp]
  apply Finset.sum_congr rfl
  intro k hk
  exact mul_comm _ _

theorem kernel_normalMatrix {L : ℕ} (S : List ((Fin L → R) × (Fin L → R))) (I J : Index L) :
    (dualSign J.val : R) * (colourBasis R).repr
        (Fock.normalList R (TwoColour.colouredList R L S) (TwoColour.kernel R L))
        (colourIndex I.val J.val) = normalMatrix R L S I J := by
  rw [normalList_kernel_coefficient]
  have hs : (dualSign J.val : R) * (dualSign J.val : R) = 1 := by
    have h := congrArg (fun z : ℤ => (z : R)) (dualSign_mul_self J.val)
    simpa only [Int.cast_mul, Int.cast_one] using h
  change (dualSign J.val : R) * ((dualSign J.val : R) * _) = _
  rw [← mul_assoc, hs, one_mul]
  rfl

theorem normalLists_kernel_coefficient {L : ℕ}
    (S T : List ((Fin L → R) × (Fin L → R))) (I J : Index L) :
    (colourBasis R).repr
        (Fock.normalList R (TwoColour.colouredList R L S)
          (Fock.normalList R (TwoColour.colouredList R L T) (TwoColour.kernel R L)))
        (colourIndex I.val J.val) =
      (dualSign J.val : R) * (normalMatrix R L S * normalMatrix R L T) I J := by
  rw [normalList_kernel_coevaluation, normalMatrix_mul]
  simp only [map_sum, map_smul, normalList_leftInclusion_mul_right,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    leftInclusion_right_coefficient]
  simp [Finset.mem_powerset.mp J.property]

theorem normalMatrix_scaled {L : ℕ} (A I J : Index L) :
    normalMatrix (LaurentPolynomial R) L
        ((A.val.sort.map Sum.inl).map (sourceCoefficients R L)) I J =
      scaledMatrix R L A I J := by
  rw [← kernel_normalMatrix, normal_remainder_kernel]
  simp only [List.map_map, Function.comp_def, sourceSymbol, scaledMatrix]

theorem normalMatrix_unscaled {L : ℕ} (B I J : Index L) :
    normalMatrix (LaurentPolynomial R) L
        ((B.val.sort.map Sum.inr).map (sourceCoefficients R L)) I J =
      LaurentPolynomial.C (matrix R L (Pi.single B 1) I J) := by
  rw [← kernel_normalMatrix, normal_remainder_kernel]
  simpa only [List.map_map, Function.comp_def, sourceSymbol] using
    unscaledMatrix_eq_constant R L B I J

theorem sourceEnergy_sort (I : Finset ℕ) : sourceEnergy I.sort = doubledEnergy I := by
  simpa only [sourceEnergy, Matching.weight, doubledEnergy, id_eq, Finset.sort_toFinset] using
    (List.sum_toFinset (fun m : ℕ => 2 * m + 1) (I.sort_nodup (· ≤ ·))).symm

theorem blockSign_smul (A B : List ℕ)
    (hparity : sourceEnergy A % 2 = sourceEnergy B % 2) (c : R) :
    ((-1 : ℤˣ) ^ (A.length * B.length)) • c = (sigma (sourceEnergy B) : R) * c := by
  have hA := sourceEnergy_mod_two A
  have hB := sourceEnergy_mod_two B
  have hlen : A.length % 2 = B.length % 2 := by omega
  have hmod : (A.length * B.length) % 2 = sourceEnergy B % 2 := by
    rw [hB, Nat.mul_mod, hlen]
    have h01 : B.length % 2 = 0 ∨ B.length % 2 = 1 := by omega
    rcases h01 with h0 | h1
    · simp [h0]
    · simp [h1]
  have hp : (-1 : R) ^ (A.length * B.length) = (-1 : R) ^ sourceEnergy B := by
    calc
      _ = (-1 : R) ^ ((A.length * B.length) % 2) := neg_one_pow_eq_pow_mod_two _
      _ = (-1 : R) ^ (sourceEnergy B % 2) := by rw [hmod]
      _ = _ := (neg_one_pow_eq_pow_mod_two _).symm
  have hu : (((-1 : ℤˣ) ^ (A.length * B.length) : ℤˣ) : ℤ) =
      (-1 : ℤ) ^ (A.length * B.length) := by simp
  simp only [Units.smul_def, zsmul_eq_mul, hu, sigma, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [hp]

noncomputable def constantMatrix (L : ℕ) (B : Index L) :
    Matrix (Index L) (Index L) (LaurentPolynomial R) :=
  fun I J => LaurentPolynomial.C (matrix R L (Pi.single B 1) I J)

theorem productPolynomial_normalMatrix (L d : ℕ) (A B : List SourceIndex) (I J : Index L) :
    productPolynomial R L d A B I.val J.val =
      (dualSign J.val : LaurentPolynomial R) *
        ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
          (normalMatrix (LaurentPolynomial R) L (A.map (sourceCoefficients R L)) *
            normalMatrix (LaurentPolynomial R) L (B.map (sourceCoefficients R L))) I J) := by
  change (LaurentPolynomial.T (R := R) 2 - 1) ^ d *
    (colourBasis (LaurentPolynomial R)).repr
      (Fock.normalList (LaurentPolynomial R) (A.map (normalSource R L))
        (Fock.normalList (LaurentPolynomial R) (B.map (normalSource R L))
          (TwoColour.kernel (LaurentPolynomial R) L))) (colourIndex I.val J.val) = _
  rw [normalSource_list, normalSource_list, normalLists_kernel_coefficient]
  ring

theorem forward_productPolynomial_matrix (L d : ℕ) (A B I J : Index L) :
    productPolynomial R L d (A.val.sort.map Sum.inl) (B.val.sort.map Sum.inr) I.val J.val =
      (dualSign J.val : LaurentPolynomial R) *
        ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
          (scaledMatrix R L A * constantMatrix R L B) I J) := by
  rw [productPolynomial_normalMatrix]
  simp only [Matrix.mul_apply, normalMatrix_scaled, normalMatrix_unscaled, constantMatrix]

theorem reverse_productPolynomial_matrix (L d : ℕ) (A B I J : Index L) :
    productPolynomial R L d (B.val.sort.map Sum.inr) (A.val.sort.map Sum.inl) I.val J.val =
      (dualSign J.val : LaurentPolynomial R) *
        ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
          (constantMatrix R L B * scaledMatrix R L A) I J) := by
  rw [productPolynomial_normalMatrix]
  simp only [Matrix.mul_apply, normalMatrix_scaled, normalMatrix_unscaled, constantMatrix]

theorem kernel_coefficient_identity {L : ℕ} (I J : Index L) :
    (dualSign J.val : R) * (colourBasis R).repr (TwoColour.kernel R L) (colourIndex I.val J.val) =
      if I = J then 1 else 0 := by
  have h := kernel_normalMatrix R (L := L) [] I J
  simp only [TwoColour.colouredList, List.map_nil, Fock.normalList_nil,
    LinearMap.id_apply, normalMatrix, plainList, Module.Basis.repr_self_apply] at h
  have he : J.val = I.val ↔ I = J := by
    constructor
    · intro h
      exact Subtype.ext h.symm
    · intro h
      subst J
      rfl
  simpa only [he] using h

theorem weighted_matrix_residue (L : ℕ) (A B I J : Index L) (d : ℕ)
    (hdegree : 2 * d + 2 = sourceEnergy A.val.sort + sourceEnergy B.val.sort)
    (hw : sourceEnergy A.val.sort ≤ sourceEnergy B.val.sort)
    (hIJ : doubledEnergy I.val = doubledEnergy J.val)
    (hcut : doubledEnergy I.val + sourceEnergy B.val.sort ≤ 2 * L) :
    ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
        (scaledMatrix R L A * constantMatrix R L B) I J).coeff 0 -
      ((-1 : ℤˣ) ^ (A.val.sort.length * B.val.sort.length)) •
        ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
          (constantMatrix R L B * scaledMatrix R L A) I J).coeff 0 =
      (if I = J then (1 : R) else 0) * matrix R L (Pi.single A 1) ⟨∅, by simp⟩ B := by
  let a := ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
    (scaledMatrix R L A * constantMatrix R L B) I J).coeff 0
  let b := ((LaurentPolynomial.T (R := R) 2 - 1) ^ d *
    (constantMatrix R L B * scaledMatrix R L A) I J).coeff 0
  let ε : R := (dualSign J.val : R)
  let u : ℤˣ := (-1) ^ (A.val.sort.length * B.val.sort.length)
  let k : R := (colourBasis R).repr (TwoColour.kernel R L) (colourIndex I.val J.val)
  let l : R := matrix R L (Pi.single A 1) ⟨∅, by simp⟩ B
  have h := product_residue_scalar R L A B d hdegree hw I.val J.val hIJ hcut
  rw [forward_productPolynomial_matrix, reverse_productPolynomial_matrix] at h
  have hC : (dualSign J.val : LaurentPolynomial R) = LaurentPolynomial.C (dualSign J.val : R) := by simp
  rw [hC, constantTerm_C_mul, constantTerm_C_mul] at h
  change ε * a - u • (ε * b) = k * l at h
  have he := congrArg (fun z : R => ε * z) h
  have hs : ε * ε = 1 := by
    simpa only [ε, Int.cast_mul, Int.cast_one] using
      congrArg (fun z : ℤ => (z : R)) (dualSign_mul_self J.val)
  have hk : ε * k = if I = J then 1 else 0 := kernel_coefficient_identity R I J
  change a - u • b = (if I = J then (1 : R) else 0) * l
  simp only [Units.smul_def, zsmul_eq_mul] at he ⊢
  have hleft : ε * (ε * a - (((u : ℤ) : R) * (ε * b))) =
      (ε * ε) * (a - ((u : ℤ) : R) * b) := by ring
  have hright : ε * (k * l) = (ε * k) * l := by ring
  rw [hleft, hs, one_mul, hright, hk] at he
  exact he

end Lemmata.FockCircuits.FiniteIdentity
