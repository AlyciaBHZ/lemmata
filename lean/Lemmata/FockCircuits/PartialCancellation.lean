module

public import Lemmata.FockCircuits.FiniteIdentity
public import Mathlib.Algebra.BigOperators.Ring.List

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.FiniteIdentity

variable (R : Type*) [CommRing R]

theorem upperBound_mono {p : LaurentPolynomial R} {a b : ℤ}
    (hp : UpperBound R p a) (hab : a ≤ b) : UpperBound R p b :=
  fun i hi => (hp i hi).trans hab

theorem lowerBound_mono {p : LaurentPolynomial R} {a b : ℤ}
    (hp : LowerBound R p a) (hab : b ≤ a) : LowerBound R p b :=
  fun i hi => hab.trans (hp i hi)

theorem upperBound_add {p q : LaurentPolynomial R} {a : ℤ}
    (hp : UpperBound R p a) (hq : UpperBound R q a) : UpperBound R (p + q) a := by
  intro i hi
  have h : i ∈ p.coeff.support ∪ q.coeff.support :=
    Finsupp.support_add (by simpa only [AddMonoidAlgebra.coeff_add] using hi)
  rcases Finset.mem_union.mp h with hi | hi
  · exact hp i hi
  · exact hq i hi

theorem lowerBound_add {p q : LaurentPolynomial R} {a : ℤ}
    (hp : LowerBound R p a) (hq : LowerBound R q a) : LowerBound R (p + q) a := by
  intro i hi
  have h : i ∈ p.coeff.support ∪ q.coeff.support :=
    Finsupp.support_add (by simpa only [AddMonoidAlgebra.coeff_add] using hi)
  rcases Finset.mem_union.mp h with hi | hi
  · exact hp i hi
  · exact hq i hi

theorem multiplier_upperBound (d : ℕ) :
    UpperBound R (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ d) (2 * (d : ℤ)) := by
  have hT : UpperBound R (LaurentPolynomial.T 2) 2 := by
    simpa using upperBound_monomial R 1 2 2 le_rfl
  have hC : UpperBound R (-1) 2 := by
    simpa using upperBound_monomial R (-1) 0 2 (by omega)
  have hs : UpperBound R ((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) 2 := by
    simpa only [sub_eq_add_neg] using upperBound_add R hT hC
  induction d with
  | zero => simpa using upperBound_monomial R 1 0 0 le_rfl
  | succ d ih =>
    simpa only [pow_succ, Nat.cast_succ, Nat.cast_add, Nat.cast_one, mul_add, mul_one] using
      upperBound_mul R ih hs

theorem multiplier_lowerBound (d : ℕ) :
    LowerBound R (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ d) 0 := by
  have hT : LowerBound R (LaurentPolynomial.T 2) 0 := by
    simpa using lowerBound_monomial R 1 2 0 (by omega)
  have hC : LowerBound R (-1) 0 := by
    simpa using lowerBound_monomial R (-1) 0 0 le_rfl
  have hs : LowerBound R ((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) 0 := by
    simpa only [sub_eq_add_neg] using lowerBound_add R hT hC
  induction d with
  | zero => simpa using lowerBound_monomial R 1 0 0 le_rfl
  | succ d ih =>
    rw [pow_succ]
    simpa only [zero_add] using lowerBound_mul R ih hs

theorem list_prod_power_factors {α : Type*} (P : List α) (s : LaurentPolynomial R)
    (p : α → ℕ) (f : α → LaurentPolynomial R) :
    (P.map fun x => s ^ p x * f x).prod =
      s ^ (P.map p).sum * (P.map f).prod := by
  induction P with
  | nil => simp
  | cons x P ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih, pow_add]
    ring

theorem weighted_product_factor {α : Type*} (P : List α) (s : LaurentPolynomial R)
    (p : α → ℕ) (f : α → LaurentPolynomial R) (d : ℕ) (hp : (P.map p).sum ≤ d) :
    s ^ d * (P.map f).prod =
      s ^ (d - (P.map p).sum) * (P.map fun x => s ^ p x * f x).prod := by
  rw [list_prod_power_factors R P s p f, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hp]

def poleSum (P : List (ℕ × ℕ)) : ℕ := (P.map fun p => p.1 + p.2 + 1).sum

@[simp] theorem poleSum_cons (p : ℕ × ℕ) (P : List (ℕ × ℕ)) :
    poleSum (p :: P) = p.1 + p.2 + 1 + poleSum P := rfl

theorem upperBound_list_prod {α : Type*} (P : List α) (f : α → LaurentPolynomial R)
    (hf : ∀ p ∈ P, UpperBound R (f p) 0) : UpperBound R (P.map f).prod 0 := by
  induction P with
  | nil => simpa using upperBound_monomial R 1 0 0 le_rfl
  | cons p P ih =>
    have hP : ∀ q ∈ P, UpperBound R (f q) 0 :=
      fun q hq => hf q (List.mem_cons_of_mem _ hq)
    simpa using upperBound_mul R (hf p (by simp)) (ih hP)

theorem lowerBound_list_prod {α : Type*} (P : List α) (f : α → LaurentPolynomial R)
    (hf : ∀ p ∈ P, LowerBound R (f p) 0) : LowerBound R (P.map f).prod 0 := by
  induction P with
  | nil => simpa using lowerBound_monomial R 1 0 0 le_rfl
  | cons p P ih =>
    have hP : ∀ q ∈ P, LowerBound R (f q) 0 :=
      fun q hq => hf q (List.mem_cons_of_mem _ hq)
    simpa using lowerBound_mul R (hf p (by simp)) (ih hP)

theorem product_difference_upperBound {α : Type*} (P : List α)
    (f g : α → LaurentPolynomial R) (a : ℤ)
    (hf : ∀ p ∈ P, UpperBound R (f p) 0)
    (hg : ∀ p ∈ P, UpperBound R (g p) 0)
    (he : ∀ p ∈ P, UpperBound R (f p - g p) a) :
    UpperBound R ((P.map f).prod - (P.map g).prod) a := by
  induction P with
  | nil => simp
  | cons p P ih =>
    have hfP : ∀ q ∈ P, UpperBound R (f q) 0 :=
      fun q hq => hf q (List.mem_cons_of_mem _ hq)
    have hgP : ∀ q ∈ P, UpperBound R (g q) 0 :=
      fun q hq => hg q (List.mem_cons_of_mem _ hq)
    have heP : ∀ q ∈ P, UpperBound R (f q - g q) a :=
      fun q hq => he q (List.mem_cons_of_mem _ hq)
    have h₁ := upperBound_mul R (he p (by simp)) (upperBound_list_prod R P f hfP)
    have h₂ := upperBound_mul R (hg p (by simp)) (ih hfP hgP heP)
    simp only [List.map_cons, List.prod_cons]
    have hsplit : f p * (P.map f).prod - g p * (P.map g).prod =
        (f p - g p) * (P.map f).prod + g p * ((P.map f).prod - (P.map g).prod) := by ring
    rw [hsplit]
    exact upperBound_add R (by simpa using h₁) (by simpa using h₂)

theorem product_difference_lowerBound {α : Type*} (P : List α)
    (f g : α → LaurentPolynomial R) (a : ℤ)
    (hf : ∀ p ∈ P, LowerBound R (f p) 0)
    (hg : ∀ p ∈ P, LowerBound R (g p) 0)
    (he : ∀ p ∈ P, LowerBound R (f p - g p) a) :
    LowerBound R ((P.map f).prod - (P.map g).prod) a := by
  induction P with
  | nil => simp
  | cons p P ih =>
    have hfP : ∀ q ∈ P, LowerBound R (f q) 0 :=
      fun q hq => hf q (List.mem_cons_of_mem _ hq)
    have hgP : ∀ q ∈ P, LowerBound R (g q) 0 :=
      fun q hq => hg q (List.mem_cons_of_mem _ hq)
    have heP : ∀ q ∈ P, LowerBound R (f q - g q) a :=
      fun q hq => he q (List.mem_cons_of_mem _ hq)
    have h₁ := lowerBound_mul R (he p (by simp)) (lowerBound_list_prod R P f hfP)
    have h₂ := lowerBound_mul R (hg p (by simp)) (ih hfP hgP heP)
    simp only [List.map_cons, List.prod_cons]
    have hsplit : f p * (P.map f).prod - g p * (P.map g).prod =
        (f p - g p) * (P.map f).prod + g p * ((P.map f).prod - (P.map g).prod) := by ring
    rw [hsplit]
    exact lowerBound_add R (by simpa using h₁) (by simpa using h₂)

noncomputable def pairConstant (p : ℕ × ℕ) : LaurentPolynomial R :=
  LaurentPolynomial.C (Fock.contractionCoefficient p.1 p.2 : R)

noncomputable def clearedForward (L : ℕ) (p : ℕ × ℕ) : LaurentPolynomial R :=
  ((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ (p.1 + p.2 + 1) * forwardTail R 0 L p.1 p.2

noncomputable def clearedReverse (L : ℕ) (p : ℕ × ℕ) : LaurentPolynomial R :=
  ((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ (p.1 + p.2 + 1) * reverseTail R 0 L p.1 p.2

theorem pairConstant_upperBound (p : ℕ × ℕ) : UpperBound R (pairConstant R p) 0 := by
  simpa [pairConstant] using upperBound_monomial R (Fock.contractionCoefficient p.1 p.2 : R) 0 0 le_rfl

theorem neg_pairConstant_lowerBound (p : ℕ × ℕ) : LowerBound R (-pairConstant R p) 0 := by
  simpa [pairConstant] using lowerBound_monomial R (-(Fock.contractionCoefficient p.1 p.2 : R)) 0 0 le_rfl

theorem forward_products_difference (L N : ℕ) (P : List (ℕ × ℕ)) (hN : N < L)
    (hP : ∀ p ∈ P, p.2 ≤ N) :
    UpperBound R ((P.map (clearedForward R L)).prod - (P.map (pairConstant R)).prod)
      (-2 * ((L - N : ℕ) : ℤ)) := by
  have he : ∀ p ∈ P, UpperBound R (clearedForward R L p - pairConstant R p)
      (-2 * ((L - N : ℕ) : ℤ)) := by
    intro p hp
    have hn := hP p hp
    exact upperBound_mono R (forwardContraction_cleared R L p.1 p.2 (by omega)) (by omega)
  apply product_difference_upperBound R P (clearedForward R L) (pairConstant R) _
  · intro p hp
    have he0 := upperBound_mono R (he p hp) (show -2 * ((L - N : ℕ) : ℤ) ≤ 0 by omega)
    simpa using upperBound_add R he0 (pairConstant_upperBound R p)
  · intro p hp
    exact pairConstant_upperBound R p
  · exact he

theorem reverse_products_difference (L N : ℕ) (P : List (ℕ × ℕ)) (hN : N < L)
    (hP : ∀ p ∈ P, p.1 ≤ N) :
    LowerBound R ((P.map (clearedReverse R L)).prod - (P.map fun p => -pairConstant R p).prod)
      (2 * ((L - N : ℕ) : ℤ)) := by
  have he : ∀ p ∈ P, LowerBound R (clearedReverse R L p - (-pairConstant R p))
      (2 * ((L - N : ℕ) : ℤ)) := by
    intro p hp
    have hm := hP p hp
    have h := reverseContraction_cleared R L p.1 p.2 (by omega)
    exact lowerBound_mono R (by simpa only [clearedReverse, pairConstant, sub_neg_eq_add] using h)
      (by omega)
  apply product_difference_lowerBound R P (clearedReverse R L) (fun p => -pairConstant R p) _
  · intro p hp
    have he0 := lowerBound_mono R (he p hp) (show 0 ≤ 2 * ((L - N : ℕ) : ℤ) by omega)
    simpa using lowerBound_add R he0 (neg_pairConstant_lowerBound R p)
  · intro p hp
    exact neg_pairConstant_lowerBound R p
  · exact he

theorem forward_products_constantTerm (L N : ℕ) (P : List (ℕ × ℕ)) (hN : N < L)
    (hP : ∀ p ∈ P, p.2 ≤ N) (u v : LaurentPolynomial R) (a b : ℤ)
    (hu : UpperBound R u a) (hv : UpperBound R v b)
    (hmargin : a - 2 * ((L - N : ℕ) : ℤ) + b < 0) :
    (u * (P.map (clearedForward R L)).prod * v).coeff 0 =
      (u * (P.map (pairConstant R)).prod * v).coeff 0 := by
  have he := forward_products_difference R L N P hN hP
  have hz := constantTerm_eq_zero_of_upperBound R
    (upperBound_mul R (upperBound_mul R hu he) hv) hmargin
  have hsplit : u * (P.map (clearedForward R L)).prod * v -
        u * (P.map (pairConstant R)).prod * v =
      u * ((P.map (clearedForward R L)).prod - (P.map (pairConstant R)).prod) * v := by ring
  have h : (u * (P.map (clearedForward R L)).prod * v -
      u * (P.map (pairConstant R)).prod * v).coeff 0 = 0 := by rw [hsplit]; exact hz
  simpa only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, sub_eq_zero] using h

theorem reverse_products_constantTerm (L N : ℕ) (P : List (ℕ × ℕ)) (hN : N < L)
    (hP : ∀ p ∈ P, p.1 ≤ N) (u v : LaurentPolynomial R) (a b : ℤ)
    (hu : LowerBound R u a) (hv : LowerBound R v b)
    (hmargin : 0 < a + 2 * ((L - N : ℕ) : ℤ) + b) :
    (u * (P.map (clearedReverse R L)).prod * v).coeff 0 =
      (u * (P.map fun p => -pairConstant R p).prod * v).coeff 0 := by
  have he := reverse_products_difference R L N P hN hP
  have hz := constantTerm_eq_zero_of_lowerBound R
    (lowerBound_mul R (lowerBound_mul R hu he) hv) hmargin
  have hsplit : u * (P.map (clearedReverse R L)).prod * v -
        u * (P.map fun p => -pairConstant R p).prod * v =
      u * ((P.map (clearedReverse R L)).prod - (P.map fun p => -pairConstant R p).prod) * v := by ring
  have h : (u * (P.map (clearedReverse R L)).prod * v -
      u * (P.map fun p => -pairConstant R p).prod * v).coeff 0 = 0 := by rw [hsplit]; exact hz
  simpa only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, sub_eq_zero] using h

theorem neg_pairConstants_constantTerm (P : List (ℕ × ℕ)) (u v : LaurentPolynomial R) :
    (u * (P.map fun p => -pairConstant R p).prod * v).coeff 0 =
      (-1 : R) ^ P.length * (u * (P.map (pairConstant R)).prod * v).coeff 0 := by
  have hp : (P.map fun p => -pairConstant R p).prod =
      (-1 : LaurentPolynomial R) ^ P.length * (P.map (pairConstant R)).prod := by
    simpa only [List.map_map, Function.comp_def, List.length_map] using
      List.prod_map_neg (P.map (pairConstant R))
  rw [hp]
  have hc : (-1 : LaurentPolynomial R) ^ P.length =
      LaurentPolynomial.C ((-1 : R) ^ P.length) := by simp
  have hmove : u * ((-1 : LaurentPolynomial R) ^ P.length * (P.map (pairConstant R)).prod) * v =
      LaurentPolynomial.C ((-1 : R) ^ P.length) * (u * (P.map (pairConstant R)).prod * v) := by
    rw [hc]
    ring
  rw [hmove]
  simp only [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single_mul_apply,
    neg_zero, zero_add]

theorem partial_pairing_cancellation (L A B : ℕ) (P : List (ℕ × ℕ))
    (hA : A < L) (hB : B < L) (hPA : ∀ p ∈ P, p.1 ≤ A) (hPB : ∀ p ∈ P, p.2 ≤ B)
    (u v : LaurentPolynomial R) (a b c d : ℤ)
    (huUpper : UpperBound R u a) (hvUpper : UpperBound R v b)
    (huLower : LowerBound R u c) (hvLower : LowerBound R v d)
    (hforward : a - 2 * ((L - B : ℕ) : ℤ) + b < 0)
    (hreverse : 0 < c + 2 * ((L - A : ℕ) : ℤ) + d) :
    (u * (P.map (clearedForward R L)).prod * v).coeff 0 -
      (-1 : R) ^ P.length * (u * (P.map (clearedReverse R L)).prod * v).coeff 0 = 0 := by
  rw [forward_products_constantTerm R L B P hB hPB u v a b huUpper hvUpper hforward,
    reverse_products_constantTerm R L A P hA hPA u v c d huLower hvLower hreverse,
    neg_pairConstants_constantTerm]
  have hs : (-1 : R) ^ P.length * (-1 : R) ^ P.length = 1 := by
    rw [← mul_pow]
    simp
  rw [← mul_assoc, hs, one_mul, sub_self]

theorem partial_contraction_cancellation (L A B : ℕ) (P : List (ℕ × ℕ)) (d : ℕ)
    (hpole : poleSum P ≤ d) (hA : A < L) (hB : B < L)
    (hPA : ∀ p ∈ P, p.1 ≤ A) (hPB : ∀ p ∈ P, p.2 ≤ B)
    (v : LaurentPolynomial R) (a b : ℤ) (hvUpper : UpperBound R v a) (hvLower : LowerBound R v b)
    (hforward : 2 * ((d - poleSum P : ℕ) : ℤ) - 2 * ((L - B : ℕ) : ℤ) + a < 0)
    (hreverse : 0 < 2 * ((L - A : ℕ) : ℤ) + b) :
    (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ d *
        (P.map fun p => forwardTail R 0 L p.1 p.2).prod * v).coeff 0 -
      (-1 : R) ^ P.length *
        (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ d *
          (P.map fun p => reverseTail R 0 L p.1 p.2).prod * v).coeff 0 = 0 := by
  rw [weighted_product_factor R P ((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1)
      (fun p => p.1 + p.2 + 1) (fun p => forwardTail R 0 L p.1 p.2) d hpole,
    weighted_product_factor R P ((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1)
      (fun p => p.1 + p.2 + 1) (fun p => reverseTail R 0 L p.1 p.2) d hpole]
  exact partial_pairing_cancellation R L A B P hA hB hPA hPB
    (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ (d - poleSum P)) v
    (2 * ((d - poleSum P : ℕ) : ℤ)) a 0 b
    (multiplier_upperBound R _) hvUpper (multiplier_lowerBound R _) hvLower
    hforward (by simpa using hreverse)

theorem constantTerm_mul_of_nonnegative {p q : LaurentPolynomial R}
    (hp : LowerBound R p 0) (hq : LowerBound R q 0) :
    (p * q).coeff 0 = p.coeff 0 * q.coeff 0 := by
  classical
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  unfold Finsupp.sum
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    have hpi := hp i hi
    have hz : q.coeff (-i + 0) = 0 := by
      by_contra h
      have := hq (-i + 0) (Finsupp.mem_support_iff.mpr h)
      omega
    change p.coeff i * q.coeff (-i + 0) = 0
    rw [hz, mul_zero]
  · intro h
    have hp0 := Finsupp.notMem_support_iff.mp h
    simp [hp0]

theorem constantTerm_list_prod_of_nonnegative {α : Type*} (P : List α)
    (f : α → LaurentPolynomial R) (hf : ∀ p ∈ P, LowerBound R (f p) 0) :
    (P.map f).prod.coeff 0 = (P.map fun p => (f p).coeff 0).prod := by
  induction P with
  | nil => simp
  | cons p P ih =>
    have hP : ∀ q ∈ P, LowerBound R (f q) 0 :=
      fun q hq => hf q (List.mem_cons_of_mem _ hq)
    simp only [List.map_cons, List.prod_cons]
    rw [constantTerm_mul_of_nonnegative R (hf p (by simp)) (lowerBound_list_prod R P f hP), ih hP]

theorem multiplier_constantTerm (d : ℕ) :
    (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1 : LaurentPolynomial R) ^ d).coeff 0 = (-1 : R) ^ d := by
  have hs : LowerBound R ((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) 0 := by
    simpa using multiplier_lowerBound R 1
  have hc : ((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1 : LaurentPolynomial R).coeff 0 = -1 := by simp
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, constantTerm_mul_of_nonnegative R (multiplier_lowerBound R d) hs, ih, hc, pow_succ]

theorem reverseMonomial_constantTerm (m n k : ℕ) :
    (reverseMonomial R m n k).coeff 0 =
      if k = m then ((negativeCoefficient n k * positiveCoefficient m k : ℤ) : R) else 0 := by
  have he : 2 * ((k : ℤ) - m) = 0 ↔ k = m := by omega
  simp only [reverseMonomial, ← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, he]

theorem reverseContraction_constantTerm (L m n : ℕ) (hmL : m < L) :
    (reverseTail R 0 L m n).coeff 0 = (Fock.contractionCoefficient n m : R) := by
  classical
  simp only [reverseTail, Nat.Ico_zero_eq_range, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, reverseMonomial_constantTerm]
  rw [Finset.sum_eq_single m]
  · simp [positiveCoefficient, negativeCoefficient, Fock.contractionCoefficient, Nat.add_comm]
  · intro k hk hkm
    simp [hkm]
  · intro h
    exact (h (Finset.mem_range.mpr hmL)).elim

theorem forward_product_upperBound (L : ℕ) (P : List (ℕ × ℕ)) :
    UpperBound R (P.map fun p => forwardTail R 0 L p.1 p.2).prod
      (-2 * (poleSum P : ℤ)) := by
  induction P with
  | nil => simpa [poleSum] using upperBound_monomial R 1 0 0 le_rfl
  | cons p P ih =>
    simp only [List.map_cons, List.prod_cons]
    have he : -2 * ((p.1 : ℤ) + p.2 + 1) + -2 * (poleSum P : ℤ) =
        -2 * (poleSum (p :: P) : ℤ) := by rw [poleSum_cons]; push_cast; ring
    rw [← he]
    exact upperBound_mul R (forwardContraction_upperBound R L p.1 p.2) ih

theorem full_forward_constantTerm (L : ℕ) (P : List (ℕ × ℕ)) (d : ℕ)
    (hpole : poleSum P = d + 1) :
    (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ d *
      (P.map fun p => forwardTail R 0 L p.1 p.2).prod).coeff 0 = 0 := by
  apply constantTerm_eq_zero_of_upperBound R
    (upperBound_mul R (multiplier_upperBound R d) (forward_product_upperBound R L P))
  omega

theorem full_reverse_constantTerm (L : ℕ) (P : List (ℕ × ℕ)) (d : ℕ)
    (hP : ∀ p ∈ P, p.1 < L) :
    (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ d *
      (P.map fun p => reverseTail R 0 L p.1 p.2).prod).coeff 0 =
      (-1 : R) ^ d * (P.map fun p => (Fock.contractionCoefficient p.2 p.1 : R)).prod := by
  have hnonneg : ∀ p ∈ P, LowerBound R (reverseTail R 0 L p.1 p.2) 0 :=
    fun p hp => reverseContraction_lowerBound R L p.1 p.2
  rw [constantTerm_mul_of_nonnegative R (multiplier_lowerBound R d)
    (lowerBound_list_prod R P _ hnonneg), multiplier_constantTerm,
    constantTerm_list_prod_of_nonnegative R P _ hnonneg]
  congr 1
  congr 1
  apply List.map_congr_left
  intro p hp
  exact reverseContraction_constantTerm R L p.1 p.2 (hP p hp)

theorem contraction_product_reversal (P : List (ℕ × ℕ)) :
    (P.map fun p => (Fock.contractionCoefficient p.2 p.1 : R)).prod *
        (-1 : R) ^ poleSum P =
      (-1 : R) ^ P.length * (P.map fun p => (Fock.contractionCoefficient p.1 p.2 : R)).prod := by
  induction P with
  | nil => simp [poleSum]
  | cons p P ih =>
    have hp : (Fock.contractionCoefficient p.2 p.1 : R) * (-1 : R) ^ (p.1 + p.2 + 1) =
        -(Fock.contractionCoefficient p.1 p.2 : R) := by
      simpa only [Int.coe_castRingHom, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using
        congrArg (Int.castRingHom R) (contraction_reversal_sign p.1 p.2)
    simp only [List.map_cons, List.prod_cons, poleSum_cons, List.length_cons]
    rw [pow_add]
    calc
      _ = ((Fock.contractionCoefficient p.2 p.1 : R) * (-1 : R) ^ (p.1 + p.2 + 1)) *
          ((P.map fun q => (Fock.contractionCoefficient q.2 q.1 : R)).prod * (-1 : R) ^ poleSum P) := by ring
      _ = _ := by rw [hp, ih, pow_succ]; ring

theorem full_pairing_constantTerm (L : ℕ) (P : List (ℕ × ℕ)) (d : ℕ)
    (hpole : poleSum P = d + 1) (hP : ∀ p ∈ P, p.1 < L) :
    (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ d *
        (P.map fun p => forwardTail R 0 L p.1 p.2).prod).coeff 0 -
      (-1 : R) ^ P.length *
        (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ d *
          (P.map fun p => reverseTail R 0 L p.1 p.2).prod).coeff 0 =
      (P.map fun p => (Fock.contractionCoefficient p.1 p.2 : R)).prod := by
  rw [full_forward_constantTerm R L P d hpole, full_reverse_constantTerm R L P d hP]
  have hp := contraction_product_reversal R P
  rw [hpole] at hp
  have hs : (-1 : R) ^ P.length * (-1 : R) ^ P.length = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = (-1 : R) ^ P.length *
        ((P.map fun p => (Fock.contractionCoefficient p.2 p.1 : R)).prod * (-1 : R) ^ (d + 1)) := by
      rw [pow_succ]
      ring
    _ = _ := by rw [hp, ← mul_assoc, hs, one_mul]

def pairedLeftWeight (P : List (ℕ × ℕ)) : ℕ := (P.map fun p => 2 * p.1 + 1).sum

def pairedRightWeight (P : List (ℕ × ℕ)) : ℕ := (P.map fun p => 2 * p.2 + 1).sum

theorem two_poleSum (P : List (ℕ × ℕ)) :
    2 * poleSum P = pairedLeftWeight P + pairedRightWeight P := by
  induction P with
  | nil => simp [poleSum, pairedLeftWeight, pairedRightWeight]
  | cons p P ih =>
    simp only [poleSum_cons, pairedLeftWeight, pairedRightWeight,
      List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem pairedLeftWeight_positive {P : List (ℕ × ℕ)} (hP : P ≠ []) :
    0 < pairedLeftWeight P := by
  cases P with
  | nil => exact (hP rfl).elim
  | cons p P => simp only [pairedLeftWeight, List.map_cons, List.sum_cons]; omega

theorem pairedRightWeight_positive {P : List (ℕ × ℕ)} (hP : P ≠ []) :
    0 < pairedRightWeight P := by
  cases P with
  | nil => exact (hP rfl).elim
  | cons p P => simp only [pairedRightWeight, List.map_cons, List.sum_cons]; omega

theorem pairedLeftWeight_mem {P : List (ℕ × ℕ)} {p : ℕ × ℕ} (hp : p ∈ P) :
    2 * p.1 + 1 ≤ pairedLeftWeight P := by
  change 2 * p.1 + 1 ≤ (P.map fun q => 2 * q.1 + 1).sum
  apply List.single_le_sum (fun x _ => Nat.zero_le x)
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

theorem pairedRightWeight_mem {P : List (ℕ × ℕ)} {p : ℕ × ℕ} (hp : p ∈ P) :
    2 * p.2 + 1 ≤ pairedRightWeight P := by
  change 2 * p.2 + 1 ≤ (P.map fun q => 2 * q.2 + 1).sum
  apply List.single_le_sum (fun x _ => Nat.zero_le x)
  exact List.mem_map.mpr ⟨p, hp, rfl⟩

theorem cutoff_partial_contraction_cancellation (L e W w d : ℕ) (P : List (ℕ × ℕ))
    (hpole : poleSum P ≤ d) (hdegree : 2 * d + 2 = W + w)
    (hleft : pairedLeftWeight P ≤ w) (hright : pairedRightWeight P ≤ W)
    (hw : w ≤ W) (hcut : e + W ≤ 2 * L)
    (v : LaurentPolynomial R)
    (hvUpper : UpperBound R v ((e : ℤ) - (w - pairedLeftWeight P : ℕ)))
    (hvLower : LowerBound R v (-(e : ℤ) - (w - pairedLeftWeight P : ℕ))) :
    (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ d *
        (P.map fun p => forwardTail R 0 L p.1 p.2).prod * v).coeff 0 -
      (-1 : R) ^ P.length *
        (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ d *
          (P.map fun p => reverseTail R 0 L p.1 p.2).prod * v).coeff 0 = 0 := by
  classical
  by_cases hP : P = []
  · subst P
    simp
  have hleftPos := pairedLeftWeight_positive hP
  have hrightPos := pairedRightWeight_positive hP
  have hpoles := two_poleSum P
  let A := (pairedLeftWeight P - 1) / 2
  let B := (pairedRightWeight P - 1) / 2
  have hA : A < L := by dsimp [A]; omega
  have hB : B < L := by dsimp [B]; omega
  have hPA : ∀ p ∈ P, p.1 ≤ A := by
    intro p hp
    have h := pairedLeftWeight_mem hp
    dsimp [A]
    omega
  have hPB : ∀ p ∈ P, p.2 ≤ B := by
    intro p hp
    have h := pairedRightWeight_mem hp
    dsimp [B]
    omega
  apply partial_contraction_cancellation R L A B P d hpole hA hB hPA hPB v
    ((e : ℤ) - (w - pairedLeftWeight P : ℕ))
    (-(e : ℤ) - (w - pairedLeftWeight P : ℕ)) hvUpper hvLower
  · dsimp [A, B] at *
    omega
  · dsimp [A, B] at *
    omega

theorem cutoff_partial_replacements (L e W w d : ℕ) (P : List (ℕ × ℕ))
    (hpole : poleSum P ≤ d) (hdegree : 2 * d + 2 = W + w)
    (hleft : pairedLeftWeight P ≤ w) (hright : pairedRightWeight P ≤ W)
    (hw : w ≤ W) (hcut : e + W ≤ 2 * L)
    (v : LaurentPolynomial R)
    (hvUpper : UpperBound R v ((e : ℤ) - (w - pairedLeftWeight P : ℕ)))
    (hvLower : LowerBound R v (-(e : ℤ) - (w - pairedLeftWeight P : ℕ))) :
    ((((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ d *
        (P.map fun p => forwardTail R 0 L p.1 p.2).prod * v).coeff 0 =
      (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ (d - poleSum P) *
        (P.map (pairConstant R)).prod * v).coeff 0) ∧
    ((((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ d *
        (P.map fun p => reverseTail R 0 L p.1 p.2).prod * v).coeff 0 =
      (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ (d - poleSum P) *
        (P.map fun p => -pairConstant R p).prod * v).coeff 0) := by
  classical
  by_cases hP : P = []
  · subst P
    simp [poleSum]
  have hleftPos := pairedLeftWeight_positive hP
  have hrightPos := pairedRightWeight_positive hP
  have hpoles := two_poleSum P
  let A := (pairedLeftWeight P - 1) / 2
  let B := (pairedRightWeight P - 1) / 2
  have hA : A < L := by dsimp [A]; omega
  have hB : B < L := by dsimp [B]; omega
  have hPA : ∀ p ∈ P, p.1 ≤ A := by
    intro p hp
    have h := pairedLeftWeight_mem hp
    dsimp [A]
    omega
  have hPB : ∀ p ∈ P, p.2 ≤ B := by
    intro p hp
    have h := pairedRightWeight_mem hp
    dsimp [B]
    omega
  constructor
  · rw [weighted_product_factor R P ((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1)
      (fun p => p.1 + p.2 + 1) (fun p => forwardTail R 0 L p.1 p.2) d hpole]
    apply forward_products_constantTerm R L B P hB hPB
      (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ (d - poleSum P)) v
      (2 * ((d - poleSum P : ℕ) : ℤ)) ((e : ℤ) - (w - pairedLeftWeight P : ℕ))
      (multiplier_upperBound R _) hvUpper
    dsimp [A, B] at *
    omega
  · rw [weighted_product_factor R P ((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1)
      (fun p => p.1 + p.2 + 1) (fun p => reverseTail R 0 L p.1 p.2) d hpole]
    apply reverse_products_constantTerm R L A P hA hPA
      (((LaurentPolynomial.T 2 : LaurentPolynomial R) - 1) ^ (d - poleSum P)) v
      0 (-(e : ℤ) - (w - pairedLeftWeight P : ℕ)) (multiplier_lowerBound R _) hvLower
    dsimp [A, B] at *
    omega

end Lemmata.FockCircuits.FiniteIdentity
