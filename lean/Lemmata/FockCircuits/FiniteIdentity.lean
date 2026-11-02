module

public import Lemmata.FockCircuits.Kernel
public import Lemmata.FockCircuits.BasisAction
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.PowerSeries.WellKnown

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.FiniteIdentity

abbrev Index (L : ℕ) := ↥((Finset.range L).powerset)

abbrev State (R : Type*) (L : ℕ) := Index L → R

def colourIndex (I J : Finset ℕ) : Finset (ℕ ⊕ₗ ℕ) :=
  I.image (fun i => toLex (Sum.inl i)) ∪ J.image (fun j => toLex (Sum.inr j))

def dualSign (I : Finset ℕ) : ℤ := (-1) ^ (I.card * (I.card - 1) / 2)

theorem dualSign_mul_self (I : Finset ℕ) : dualSign I * dualSign I = 1 := by
  simp only [dualSign, ← mul_pow]
  simp

theorem dualSign_insert {i : ℕ} {I : Finset ℕ} (hi : i ∉ I) :
    dualSign (insert i I) = (-1 : ℤ) ^ I.card * dualSign I := by
  simp only [dualSign, Finset.card_insert_of_notMem hi, ← Nat.choose_two_right]
  rw [Nat.choose_succ_succ, Nat.choose_one_right, pow_add]

def sigma (W : ℕ) : ℤ := (-1) ^ W

def shift (W : ℕ) (k : Fin W) : ℤ := 2 * (k : ℕ) + 2 - W

def markCoefficient (W w : ℕ) (k : Fin W) : ℤ :=
  (-1) ^ (W + (k : ℕ) + 1) * (((W + w) / 2 - 1).choose k : ℤ)

def weightCoefficient (W w : ℕ) (k : Fin W) : ℤ :=
  (-1) ^ (k : ℕ) * (((W + w) / 2 - 1).choose k : ℤ)

theorem shift_bounds (W : ℕ) (k : Fin W) :
    2 - (W : ℤ) ≤ shift W k ∧ shift W k ≤ W := by
  have hk := k.isLt
  simp only [shift]
  omega

theorem shift_parity (W : ℕ) (k : Fin W) : (shift W k + W) % 2 = 0 := by
  simp only [shift]
  omega

theorem sigma_mul_self (W : ℕ) : sigma W * sigma W = 1 := by
  simp only [sigma, ← mul_pow]
  simp

theorem markCoefficient_eq_neg_sigma (W w : ℕ) (k : Fin W) :
    markCoefficient W w k =
      -sigma W * ((-1 : ℤ) ^ (k : ℕ) * (((W + w) / 2 - 1).choose k : ℤ)) := by
  simp [markCoefficient, sigma, pow_add, mul_assoc]

theorem marked_supercommutator (W w : ℕ) (k : Fin W) (x y : ℤ) :
    markCoefficient W w k * (y - sigma W * x) =
      ((-1 : ℤ) ^ (k : ℕ) * (((W + w) / 2 - 1).choose k : ℤ)) *
        (x - sigma W * y) := by
  rw [markCoefficient_eq_neg_sigma]
  calc
    _ = (sigma W * sigma W) *
          ((-1 : ℤ) ^ (k : ℕ) * (((W + w) / 2 - 1).choose k : ℤ)) * x -
        sigma W *
          ((-1 : ℤ) ^ (k : ℕ) * (((W + w) / 2 - 1).choose k : ℤ)) * y := by ring
    _ = _ := by rw [sigma_mul_self]; ring

theorem source_sum_two_le {W w : ℕ} (hW : 0 < W)
    (hparity : w % 2 = W % 2) : 2 ≤ W + w := by omega

theorem binomial_upper_lt {W w : ℕ} (hW : 0 < W) (hw : w ≤ W) :
    (W + w) / 2 - 1 < W := by omega

theorem forward_tail_negative (L e W otherB : ℕ)
    (hcut : e + W ≤ 2 * L) :
    (e : ℤ) + W - 2 * L - 3 - otherB < 0 := by omega

theorem reverse_tail_positive (L e W w : ℕ)
    (hcut : e + W ≤ 2 * L) (hw : w ≤ W) :
    0 < 2 * (L : ℤ) + 1 - e - w := by omega

theorem contraction_reversal_sign (m n : ℕ) :
    Fock.contractionCoefficient n m * (-1 : ℤ) ^ (m + n + 1) =
      -Fock.contractionCoefficient m n := by
  have hc : (n + m).choose n = (m + n).choose m := by
    rw [Nat.choose_symm_add (a := n) (b := m), Nat.add_comm n m]
  have hs : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by
    rw [← mul_pow]
    simp
  unfold Fock.contractionCoefficient
  rw [hc]
  simp only [pow_add, pow_one]
  calc
    _ = -(((-1 : ℤ) ^ n * (-1 : ℤ) ^ n) *
          ((-1 : ℤ) ^ m * ((m + n).choose m : ℤ))) := by ring
    _ = _ := by rw [hs]; ring

variable (R : Type*) [CommRing R]

noncomputable def colourBasis :
    Module.Basis (Finset (ℕ ⊕ₗ ℕ)) R (Fock R) :=
  ((Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).reindex
    (Equiv.natSumNatEquivNat.symm.trans toLex)).ExteriorAlgebra

noncomputable def substitution (L : ℕ) : OneParticle R →ₗ[R] OneParticle R :=
  Finsupp.linearCombination R fun m : ℕ =>
    TwoColour.leftVector R L (fun k => (positiveCoefficient m k : R)) +
      TwoColour.rightVector R L (fun k => (negativeCoefficient m k : R))

@[simp] theorem substitution_single (L m : ℕ) :
    substitution R L (Finsupp.single m 1) =
      TwoColour.leftVector R L (fun k => (positiveCoefficient m k : R)) +
        TwoColour.rightVector R L (fun k => (negativeCoefficient m k : R)) := by
  simp [substitution]

noncomputable def sourceWord (L : ℕ) (I : Index L) :
    List ((Fin L → R) × (Fin L → R)) :=
  I.val.sort.map fun m =>
    ((fun k => (positiveCoefficient m k : R)), (fun k => (negativeCoefficient m k : R)))

theorem substitution_basis (L : ℕ) (I : Index L) :
    ExteriorAlgebra.map (substitution R L) (Fock.basis R I.val) =
      TwoColour.colouredProduct R L (sourceWord R L I) := by
  rw [Fock.basis_eq_sorted_prod, map_list_prod]
  unfold sourceWord TwoColour.colouredProduct
  rw [List.map_map, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro m hm
  simp [Fock.generator, substitution_single]

noncomputable def realize (L : ℕ) : State R L →ₗ[R] Fock R where
  toFun v := ∑ I, v I • Fock.basis R I.val
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, RingHom.id_apply]

@[simp] theorem realize_single (L : ℕ) (I : Index L) (c : R) :
    realize R L (Pi.single I c) = c • Fock.basis R I.val := by
  classical
  simp [realize, Pi.single_apply, eq_comm]

noncomputable def kernel (L : ℕ) (v : State R L) : Fock R :=
  ExteriorAlgebra.map (substitution R L) (realize R L v) * TwoColour.kernel R L

theorem kernel_single (L : ℕ) (I : Index L) (c : R) :
    kernel R L (Pi.single I c) = c •
      Fock.normalList R (TwoColour.colouredList R L (sourceWord R L I))
        (TwoColour.kernel R L) := by
  rw [kernel, realize_single, map_smul, smul_mul_assoc, substitution_basis]
  rw [TwoColour.normalList_kernel]

noncomputable def matrix (L : ℕ) (v : State R L) : Matrix (Index L) (Index L) R :=
  fun I J => (dualSign J.val : R) *
    (colourBasis R).repr (kernel R L v) (colourIndex I.val J.val)

noncomputable def diagonal (L : ℕ) (r : ℤ) (v : State R L) :
    Matrix (Index L) (Index L) R :=
  fun I J => if (doubledEnergy I.val : ℤ) - doubledEnergy J.val = r then
    matrix R L v I J else 0

noncomputable def mark (L W : ℕ) (k : Fin W) : State R L →ₗ[R] State R L where
  toFun v I := (markCoefficient W (doubledEnergy I.val) k : R) * v I
  map_add' v w := by ext I; simp [mul_add]
  map_smul' c v := by ext I; simp [smul_eq_mul, mul_left_comm]

@[simp] theorem mark_apply (L W : ℕ) (k : Fin W) (v : State R L) (I : Index L) :
    mark R L W k v I = (markCoefficient W (doubledEnergy I.val) k : R) * v I := rfl

@[simp] theorem kernel_add (L : ℕ) (v w : State R L) :
    kernel R L (v + w) = kernel R L v + kernel R L w := by
  simp [kernel, add_mul]

@[simp] theorem matrix_add (L : ℕ) (v w : State R L) :
    matrix R L (v + w) = matrix R L v + matrix R L w := by
  ext I J
  simp [matrix, mul_add]

noncomputable def weightPolynomial (W w : ℕ) : LaurentPolynomial R :=
  ∑ k : Fin W,
    LaurentPolynomial.C (weightCoefficient W w k : R) *
      LaurentPolynomial.T ((W : ℤ) + w - 2 - 2 * (k : ℕ))

theorem weightPolynomial_constantTerm (W w : ℕ) (r : ℤ) (c : R) :
    (weightPolynomial R W w *
        (LaurentPolynomial.C c * LaurentPolynomial.T (r - w))).coeff 0 =
      ∑ k : Fin W, if r = shift W k then (weightCoefficient W w k : R) * c else 0 := by
  classical
  rw [weightPolynomial, Finset.sum_mul, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have he : ((W : ℤ) + w - 2 - 2 * (k : ℕ)) + (r - w) = 0 ↔ r = shift W k := by
    simp only [shift]
    omega
  simp only [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, he]

theorem binomial_sum_padded (d W : ℕ) (hdW : d < W) (x y : LaurentPolynomial R) :
    (x + y) ^ d = ∑ k : Fin W, x ^ (k : ℕ) * y ^ (d - (k : ℕ)) * (d.choose k : ℕ) := by
  classical
  rw [← Finset.sum_range (fun k : ℕ => x ^ k * y ^ (d - k) * (d.choose k : ℕ)), add_pow]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hkW hk
  have hk' : d + 1 ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
  have hdk : d < k := by omega
  simp [Nat.choose_eq_zero_of_lt hdk]

theorem weightPolynomial_eq_power (W w : ℕ) (hW : 0 < W) (hw : w ≤ W)
    (hparity : w % 2 = W % 2) :
    weightPolynomial R W w =
      (LaurentPolynomial.T 2 - 1) ^ ((W + w) / 2 - 1) := by
  classical
  let d := (W + w) / 2 - 1
  have hsum := source_sum_two_le hW hparity
  have hd : 2 * d + 2 = W + w := by dsimp [d]; omega
  have hdW : d < W := binomial_upper_lt hW hw
  have hbin := binomial_sum_padded R d W hdW (-1) (LaurentPolynomial.T 2)
  have hbase : (-1 : LaurentPolynomial R) + LaurentPolynomial.T 2 =
      LaurentPolynomial.T 2 - 1 := by ring
  rw [hbase] at hbin
  rw [hbin]
  unfold weightPolynomial
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkd : (k : ℕ) ≤ d
  · have hexp : (W : ℤ) + w - 2 - 2 * (k : ℕ) = ((d - (k : ℕ) : ℕ) : ℤ) * 2 := by omega
    rw [hexp]
    simp only [weightCoefficient, map_mul, map_pow, map_neg, map_one,
      map_natCast, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast, LaurentPolynomial.T_pow]
    ring
  · have hdk : d < (k : ℕ) := by omega
    have hz : ((W + w) / 2 - 1).choose k = 0 := Nat.choose_eq_zero_of_lt hdk
    simp [weightCoefficient, hz, Nat.choose_eq_zero_of_lt hdk]

noncomputable def inversePrefix (d M : ℕ) : Polynomial R :=
  ∑ j ∈ Finset.range M, Polynomial.monomial j (((d + j).choose d : ℕ) : R)

@[simp] theorem inversePrefix_coeff (d M n : ℕ) :
    (inversePrefix R d M).coeff n = if n < M then ((d + n).choose d : R) else 0 := by
  classical
  simp [inversePrefix, Polynomial.coeff_monomial, eq_comm]

theorem inversePrefix_eq_trunc (d M : ℕ) :
    inversePrefix R d M =
      PowerSeries.trunc M (PowerSeries.mk fun j => ((d + j).choose d : R)) := by
  ext n
  simp [inversePrefix_coeff, PowerSeries.coeff_trunc]

theorem inversePrefix_mul_coeff (d M n : ℕ) (hn : n < M) :
    (inversePrefix R d M * (1 - Polynomial.X) ^ (d + 1)).coeff n =
      if n = 0 then 1 else 0 := by
  let f : PowerSeries R := PowerSeries.mk fun j => ((d + j).choose d : R)
  have h := congrArg (fun p : Polynomial R => p.coeff n)
    (PowerSeries.trunc_trunc_mul (n := M) f ((1 - PowerSeries.X) ^ (d + 1)))
  simp only [PowerSeries.coeff_trunc, hn, ite_true] at h
  have hf : f * (1 - PowerSeries.X) ^ (d + 1) = 1 :=
    PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one R d
  rw [hf] at h
  rw [← Polynomial.coeff_coe]
  simpa only [f, inversePrefix_eq_trunc, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X, PowerSeries.coeff_one] using h

theorem inversePrefix_boundary_dvd (d M : ℕ) :
    Polynomial.X ^ M ∣ inversePrefix R d M * (1 - Polynomial.X) ^ (d + 1) - 1 := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro n hn
  rw [Polynomial.coeff_sub, inversePrefix_mul_coeff R d M n hn, Polynomial.coeff_one]
  simp

def UpperBound (p : LaurentPolynomial R) (a : ℤ) : Prop :=
  ∀ i ∈ p.coeff.support, i ≤ a

def LowerBound (p : LaurentPolynomial R) (a : ℤ) : Prop :=
  ∀ i ∈ p.coeff.support, a ≤ i

theorem constantTerm_eq_zero_of_upperBound {p : LaurentPolynomial R} {a : ℤ}
    (hp : UpperBound R p a) (ha : a < 0) : p.coeff 0 = 0 := by
  by_contra h
  have := hp 0 (Finsupp.mem_support_iff.mpr h)
  omega

theorem constantTerm_eq_zero_of_lowerBound {p : LaurentPolynomial R} {a : ℤ}
    (hp : LowerBound R p a) (ha : 0 < a) : p.coeff 0 = 0 := by
  by_contra h
  have := hp 0 (Finsupp.mem_support_iff.mpr h)
  omega

theorem upperBound_mul {p q : LaurentPolynomial R} {a b : ℤ}
    (hp : UpperBound R p a) (hq : UpperBound R q b) :
    UpperBound R (p * q) (a + b) := by
  classical
  intro n hn
  by_contra h
  have hz : (p * q).coeff n = 0 := by
    rw [AddMonoidAlgebra.coeff_mul]
    unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hi' := hp i hi
    have hj' := hq j hj
    have hij : i + j ≠ n := by omega
    simp [hij]
  exact (Finsupp.mem_support_iff.mp hn) hz

theorem lowerBound_mul {p q : LaurentPolynomial R} {a b : ℤ}
    (hp : LowerBound R p a) (hq : LowerBound R q b) :
    LowerBound R (p * q) (a + b) := by
  classical
  intro n hn
  by_contra h
  have hz : (p * q).coeff n = 0 := by
    rw [AddMonoidAlgebra.coeff_mul]
    unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hi' := hp i hi
    have hj' := hq j hj
    have hij : i + j ≠ n := by omega
    simp [hij]
  exact (Finsupp.mem_support_iff.mp hn) hz

@[simp] theorem upperBound_zero (a : ℤ) : UpperBound R 0 a := by
  simp [UpperBound]

@[simp] theorem lowerBound_zero (a : ℤ) : LowerBound R 0 a := by
  simp [LowerBound]

theorem upperBound_monomial (c : R) (n a : ℤ) (hn : n ≤ a) :
    UpperBound R (LaurentPolynomial.C c * LaurentPolynomial.T n) a := by
  intro i hi
  have hi' : i = n := Finset.mem_singleton.mp (LaurentPolynomial.support_C_mul_T c n hi)
  omega

theorem lowerBound_monomial (c : R) (n a : ℤ) (hn : a ≤ n) :
    LowerBound R (LaurentPolynomial.C c * LaurentPolynomial.T n) a := by
  intro i hi
  have hi' : i = n := Finset.mem_singleton.mp (LaurentPolynomial.support_C_mul_T c n hi)
  omega

theorem upperBound_sum {ι : Type*} (s : Finset ι) (f : ι → LaurentPolynomial R) (a : ℤ)
    (hf : ∀ i ∈ s, UpperBound R (f i) a) : UpperBound R (∑ i ∈ s, f i) a := by
  classical
  intro n hn
  by_contra h
  have hz : (∑ i ∈ s, f i).coeff n = 0 := by
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    by_contra hni
    have := hf i hi n (Finsupp.mem_support_iff.mpr hni)
    omega
  exact (Finsupp.mem_support_iff.mp hn) hz

theorem lowerBound_sum {ι : Type*} (s : Finset ι) (f : ι → LaurentPolynomial R) (a : ℤ)
    (hf : ∀ i ∈ s, LowerBound R (f i) a) : LowerBound R (∑ i ∈ s, f i) a := by
  classical
  intro n hn
  by_contra h
  have hz : (∑ i ∈ s, f i).coeff n = 0 := by
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    by_contra hni
    have := hf i hi n (Finsupp.mem_support_iff.mpr hni)
    omega
  exact (Finsupp.mem_support_iff.mp hn) hz

noncomputable def forwardMonomial (m n k : ℕ) : LaurentPolynomial R :=
  LaurentPolynomial.C ((negativeCoefficient m k * positiveCoefficient n k : ℤ) : R) *
    LaurentPolynomial.T (-2 * ((k : ℤ) + m + 1))

noncomputable def reverseMonomial (m n k : ℕ) : LaurentPolynomial R :=
  LaurentPolynomial.C ((negativeCoefficient n k * positiveCoefficient m k : ℤ) : R) *
    LaurentPolynomial.T (2 * ((k : ℤ) - m))

noncomputable def forwardTail (L M m n : ℕ) : LaurentPolynomial R :=
  ∑ k ∈ Finset.Ico L M, forwardMonomial R m n k

noncomputable def reverseTail (L M m n : ℕ) : LaurentPolynomial R :=
  ∑ k ∈ Finset.Ico L M, reverseMonomial R m n k

theorem forwardTail_upperBound (L M m n : ℕ) :
    UpperBound R (forwardTail R L M m n) (-2 * ((L : ℤ) + m + 1)) := by
  apply upperBound_sum
  intro k hk
  have hLk := (Finset.mem_Ico.mp hk).1
  apply upperBound_monomial
  omega

theorem reverseTail_lowerBound (L M m n : ℕ) :
    LowerBound R (reverseTail R L M m n) (2 * ((L : ℤ) - m)) := by
  apply lowerBound_sum
  intro k hk
  have hLk := (Finset.mem_Ico.mp hk).1
  apply lowerBound_monomial
  omega

theorem forwardContraction_upperBound (L m n : ℕ) :
    UpperBound R (forwardTail R 0 L m n) (-2 * ((m : ℤ) + n + 1)) := by
  apply upperBound_sum
  intro k hk
  by_cases hnk : n ≤ k
  · apply upperBound_monomial
    omega
  · have hkn : k < n := by omega
    have hz : forwardMonomial R m n k = 0 := by
      simp [forwardMonomial, positiveCoefficient, Nat.choose_eq_zero_of_lt hkn]
    rw [hz]
    exact upperBound_zero R _

theorem reverseContraction_lowerBound (L m n : ℕ) :
    LowerBound R (reverseTail R 0 L m n) 0 := by
  apply lowerBound_sum
  intro k hk
  by_cases hmk : m ≤ k
  · apply lowerBound_monomial
    omega
  · have hkm : k < m := by omega
    have hz : reverseMonomial R m n k = 0 := by
      simp [reverseMonomial, positiveCoefficient, Nat.choose_eq_zero_of_lt hkm]
    rw [hz]
    exact lowerBound_zero R _

theorem sum_range_shift (f : ℕ → LaurentPolynomial R) (n L : ℕ) (hnL : n ≤ L)
    (hf : ∀ k < n, f k = 0) :
    (∑ k ∈ Finset.range L, f k) = ∑ j ∈ Finset.range (L - n), f (n + j) := by
  have hz : ∑ k ∈ Finset.range n, f k = 0 :=
    Finset.sum_eq_zero fun k hk => hf k (Finset.mem_range.mp hk)
  have hL : n + (L - n) = L := Nat.add_sub_of_le hnL
  calc
    _ = ∑ k ∈ Finset.range (n + (L - n)), f k := by rw [hL]
    _ = (∑ k ∈ Finset.range n, f k) +
        ∑ j ∈ Finset.range (L - n), f (n + j) := by rw [Finset.sum_range_add]
    _ = _ := by rw [hz, zero_add]

theorem forwardContraction_prefix (L m n : ℕ) (hnL : n ≤ L) :
    forwardTail R 0 L m n =
      LaurentPolynomial.C (Fock.contractionCoefficient m n : R) *
        LaurentPolynomial.T (-2 * ((m : ℤ) + n + 1)) *
          (inversePrefix R (m + n) (L - n)).eval₂
            LaurentPolynomial.C (LaurentPolynomial.T (-2)) := by
  classical
  simp only [forwardTail, Nat.Ico_zero_eq_range]
  rw [sum_range_shift R _ n L hnL (by
    intro k hk
    simp [forwardMonomial, positiveCoefficient, Nat.choose_eq_zero_of_lt hk])]
  simp only [inversePrefix, Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial,
    LaurentPolynomial.T_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hN : n + j + m = (m + n) + j := by omega
  have he : -2 * (((n + j : ℕ) : ℤ) + m + 1) =
      -2 * ((m : ℤ) + n + 1) + (j : ℤ) * (-2) := by push_cast; ring
  simp only [forwardMonomial, Fock.negative_mul_positive, hN, Int.cast_mul,
    Int.cast_natCast, map_mul]
  rw [he, LaurentPolynomial.T_add]
  ring

theorem reverseContraction_prefix (L m n : ℕ) (hmL : m ≤ L) :
    reverseTail R 0 L m n =
      LaurentPolynomial.C (Fock.contractionCoefficient n m : R) *
        (inversePrefix R (m + n) (L - m)).eval₂
          LaurentPolynomial.C (LaurentPolynomial.T 2) := by
  classical
  simp only [reverseTail, Nat.Ico_zero_eq_range]
  rw [sum_range_shift R _ m L hmL (by
    intro k hk
    simp [reverseMonomial, positiveCoefficient, Nat.choose_eq_zero_of_lt hk])]
  simp only [inversePrefix, Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial,
    LaurentPolynomial.T_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hN : m + j + n = (m + n) + j := by omega
  have hD : n + m = m + n := by omega
  have he : 2 * (((m + j : ℕ) : ℤ) - m) = (j : ℤ) * 2 := by push_cast; ring
  simp only [reverseMonomial, Fock.negative_mul_positive, hN, hD, Int.cast_mul,
    Int.cast_natCast, map_mul]
  rw [he]
  ring

theorem forwardTail_constantTerm (L M m n : ℕ) (p : LaurentPolynomial R) (a : ℤ)
    (hp : UpperBound R p a) (ha : -2 * ((L : ℤ) + m + 1) + a < 0) :
    (forwardTail R L M m n * p).coeff 0 = 0 :=
  constantTerm_eq_zero_of_upperBound R
    (upperBound_mul R (forwardTail_upperBound R L M m n) hp) ha

theorem reverseTail_constantTerm (L M m n : ℕ) (p : LaurentPolynomial R) (a : ℤ)
    (hp : LowerBound R p a) (ha : 0 < 2 * ((L : ℤ) - m) + a) :
    (reverseTail R L M m n * p).coeff 0 = 0 :=
  constantTerm_eq_zero_of_lowerBound R
    (lowerBound_mul R (reverseTail_lowerBound R L M m n) hp) ha

theorem polynomial_eval_upperBound (p : Polynomial R) (a : ℤ) (ha : a ≤ 0) :
    UpperBound R (p.eval₂ LaurentPolynomial.C (LaurentPolynomial.T a)) 0 := by
  classical
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply upperBound_sum
  intro k hk
  rw [LaurentPolynomial.T_pow]
  apply upperBound_monomial
  exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg k) ha

theorem polynomial_eval_lowerBound (p : Polynomial R) (a : ℤ) (ha : 0 ≤ a) :
    LowerBound R (p.eval₂ LaurentPolynomial.C (LaurentPolynomial.T a)) 0 := by
  classical
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  apply lowerBound_sum
  intro k hk
  rw [LaurentPolynomial.T_pow]
  apply lowerBound_monomial
  exact mul_nonneg (Int.natCast_nonneg k) ha

theorem polynomial_eval_upperBound_of_dvd (p : Polynomial R) (M : ℕ)
    (hp : Polynomial.X ^ M ∣ p) (a : ℤ) (ha : a ≤ 0) :
    UpperBound R (p.eval₂ LaurentPolynomial.C (LaurentPolynomial.T a)) ((M : ℤ) * a) := by
  obtain ⟨q, rfl⟩ := hp
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    LaurentPolynomial.T_pow]
  have hT : UpperBound R (LaurentPolynomial.T ((M : ℤ) * a)) ((M : ℤ) * a) := by
    simpa using upperBound_monomial R 1 ((M : ℤ) * a) ((M : ℤ) * a) le_rfl
  simpa only [add_zero] using upperBound_mul R hT (polynomial_eval_upperBound R q a ha)

theorem polynomial_eval_lowerBound_of_dvd (p : Polynomial R) (M : ℕ)
    (hp : Polynomial.X ^ M ∣ p) (a : ℤ) (ha : 0 ≤ a) :
    LowerBound R (p.eval₂ LaurentPolynomial.C (LaurentPolynomial.T a)) ((M : ℤ) * a) := by
  obtain ⟨q, rfl⟩ := hp
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    LaurentPolynomial.T_pow]
  have hT : LowerBound R (LaurentPolynomial.T ((M : ℤ) * a)) ((M : ℤ) * a) := by
    simpa using lowerBound_monomial R 1 ((M : ℤ) * a) ((M : ℤ) * a) le_rfl
  simpa only [add_zero] using lowerBound_mul R hT (polynomial_eval_lowerBound R q a ha)

theorem inversePrefix_cleared_upperBound (d M : ℕ) :
    UpperBound R
      ((inversePrefix R d M).eval₂ LaurentPolynomial.C (LaurentPolynomial.T (-2)) *
        (1 - LaurentPolynomial.T (-2)) ^ (d + 1) - 1) (-2 * (M : ℤ)) := by
  simpa [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, mul_comm] using
    polynomial_eval_upperBound_of_dvd R _ M (inversePrefix_boundary_dvd R d M) (-2) (by omega)

theorem inversePrefix_cleared_lowerBound (d M : ℕ) :
    LowerBound R
      ((inversePrefix R d M).eval₂ LaurentPolynomial.C (LaurentPolynomial.T 2) *
        (1 - LaurentPolynomial.T 2) ^ (d + 1) - 1) (2 * (M : ℤ)) := by
  simpa [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, mul_comm] using
    polynomial_eval_lowerBound_of_dvd R _ M (inversePrefix_boundary_dvd R d M) 2 (by omega)

theorem forwardContraction_cleared (L m n : ℕ) (hnL : n ≤ L) :
    UpperBound R
      ((LaurentPolynomial.T 2 - 1) ^ (m + n + 1) * forwardTail R 0 L m n -
        LaurentPolynomial.C (Fock.contractionCoefficient m n : R))
      (-2 * ((L - n : ℕ) : ℤ)) := by
  rw [forwardContraction_prefix R L m n hnL]
  let γ : LaurentPolynomial R := LaurentPolynomial.C (Fock.contractionCoefficient m n : R)
  let P := (inversePrefix R (m + n) (L - n)).eval₂
    LaurentPolynomial.C (LaurentPolynomial.T (-2))
  have hs : (LaurentPolynomial.T 2 - 1) *
      (LaurentPolynomial.T (-2) : LaurentPolynomial R) =
        1 - LaurentPolynomial.T (-2) := by
    rw [sub_mul, ← LaurentPolynomial.T_add]
    norm_num
  have hT : (LaurentPolynomial.T (-2 * ((m : ℤ) + n + 1)) : LaurentPolynomial R) =
      LaurentPolynomial.T (-2) ^ (m + n + 1) := by
    rw [LaurentPolynomial.T_pow]
    congr 1
    push_cast
    ring
  have hp : (LaurentPolynomial.T 2 - 1) ^ (m + n + 1) *
      (LaurentPolynomial.T (-2 * ((m : ℤ) + n + 1)) : LaurentPolynomial R) =
        (1 - LaurentPolynomial.T (-2)) ^ (m + n + 1) := by
    rw [hT, ← mul_pow, hs]
  have he : (LaurentPolynomial.T 2 - 1) ^ (m + n + 1) *
        (γ * LaurentPolynomial.T (-2 * ((m : ℤ) + n + 1)) * P) - γ =
      γ * (P * (1 - LaurentPolynomial.T (-2)) ^ (m + n + 1) - 1) := by
    calc
      _ = γ * (((LaurentPolynomial.T 2 - 1) ^ (m + n + 1) *
          LaurentPolynomial.T (-2 * ((m : ℤ) + n + 1))) * P - 1) := by ring
      _ = _ := by rw [hp]; ring
  rw [he]
  have hγ : UpperBound R γ 0 := by
    simpa [γ] using upperBound_monomial R (Fock.contractionCoefficient m n : R) 0 0 le_rfl
  simpa only [zero_add] using
    upperBound_mul R hγ (inversePrefix_cleared_upperBound R (m + n) (L - n))

theorem reverseContraction_cleared (L m n : ℕ) (hmL : m ≤ L) :
    LowerBound R
      ((LaurentPolynomial.T 2 - 1) ^ (m + n + 1) * reverseTail R 0 L m n +
        LaurentPolynomial.C (Fock.contractionCoefficient m n : R))
      (2 * ((L - m : ℕ) : ℤ)) := by
  rw [reverseContraction_prefix R L m n hmL]
  let γ : LaurentPolynomial R := LaurentPolynomial.C (Fock.contractionCoefficient n m : R)
  let P := (inversePrefix R (m + n) (L - m)).eval₂
    LaurentPolynomial.C (LaurentPolynomial.T 2)
  have hsign : γ * (-1 : LaurentPolynomial R) ^ (m + n + 1) =
      -LaurentPolynomial.C (Fock.contractionCoefficient m n : R) := by
    simpa only [γ, map_intCast, Int.coe_castRingHom, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one] using
      congrArg (Int.castRingHom (LaurentPolynomial R)) (contraction_reversal_sign m n)
  have hγ : LowerBound R (γ * (-1 : LaurentPolynomial R) ^ (m + n + 1)) 0 := by
    rw [hsign]
    simpa using lowerBound_monomial R (-(Fock.contractionCoefficient m n : R)) 0 0 le_rfl
  have hs : (LaurentPolynomial.T 2 - 1 : LaurentPolynomial R) =
      (-1) * (1 - LaurentPolynomial.T 2) := by ring
  have hΓ : (LaurentPolynomial.C (Fock.contractionCoefficient m n : R) : LaurentPolynomial R) =
      -(γ * (-1) ^ (m + n + 1)) := by rw [hsign]; simp
  have he : (LaurentPolynomial.T 2 - 1) ^ (m + n + 1) * (γ * P) +
        LaurentPolynomial.C (Fock.contractionCoefficient m n : R) =
      (γ * (-1) ^ (m + n + 1)) * (P * (1 - LaurentPolynomial.T 2) ^ (m + n + 1) - 1) := by
    rw [hΓ, hs, mul_pow]
    ring
  rw [he]
  simpa only [zero_add] using
    lowerBound_mul R hγ (inversePrefix_cleared_lowerBound R (m + n) (L - m))

end Lemmata.FockCircuits.FiniteIdentity
