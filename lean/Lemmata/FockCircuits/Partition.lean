module

public import Lemmata.FockCircuits.Exterior
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits

def fullCutoff (H : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (H + 1)).powerset.filter fun I => doubledEnergy I ≤ 2 * H

@[simp] theorem mem_fullCutoff {H : ℕ} {I : Finset ℕ} :
    I ∈ fullCutoff H ↔ doubledEnergy I ≤ 2 * H := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, h⟩
    intro i hi
    have hb := Finset.single_le_sum (f := fun j : ℕ => 2 * j + 1)
      (fun j _ => Nat.zero_le _) hi
    change 2 * i + 1 ≤ doubledEnergy I at hb
    exact Finset.mem_range.mpr (by omega)


def partitionSlice (k : ℕ) : Finset (Finset ℕ) :=
  (Finset.range k).powerset.filter fun I => doubledEnergy I = k

def partitionDimension (k : ℕ) : ℕ := (partitionSlice k).card

def stateCount (H : ℕ) : ℕ := (fullCutoff H).card

theorem stateCount_mono : Monotone stateCount := by
  intro H K hHK
  apply Finset.card_le_card
  intro I hI
  apply mem_fullCutoff.mpr
  have h := mem_fullCutoff.mp hI
  omega

@[simp] theorem partitionDimension_zero : partitionDimension 0 = 1 := by
  rfl

@[simp] theorem mem_partitionSlice {k : ℕ} {I : Finset ℕ} :
    I ∈ partitionSlice k ↔ doubledEnergy I = k := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, h⟩
    intro i hi
    have hb := Finset.single_le_sum (f := fun j : ℕ => 2 * j + 1)
      (fun j _ => Nat.zero_le _) hi
    change 2 * i + 1 ≤ doubledEnergy I at hb
    exact Finset.mem_range.mpr (by omega)

noncomputable def partitionProduct (M : ℕ) (t : ℝ) : ℝ :=
  ∏ i ∈ Finset.range M, (1 + Real.exp (-t * (2 * i + 1 : ℕ)))

theorem partitionProduct_expansion (M : ℕ) (t : ℝ) :
    partitionProduct M t =
      ∑ I ∈ (Finset.range M).powerset, Real.exp (-t * doubledEnergy I) := by
  unfold partitionProduct
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro I hI
  rw [← Real.exp_sum]
  congr 1
  simp [doubledEnergy, Finset.mul_sum]

theorem card_fullCutoff_eq_sum (H : ℕ) :
    (fullCutoff H).card = ∑ k ∈ Finset.range (2 * H + 1), partitionDimension k := by
  have heq : fullCutoff H =
      (Finset.range (2 * H + 1)).biUnion partitionSlice := by
    ext I
    simp only [mem_fullCutoff, Finset.mem_biUnion, Finset.mem_range,
      mem_partitionSlice]
    constructor
    · intro hI
      exact ⟨doubledEnergy I, by omega, rfl⟩
    · rintro ⟨k, hk, hI⟩
      omega
  rw [heq]
  apply Finset.card_biUnion
  intro a ha b hb hab
  apply Finset.disjoint_left.mpr
  intro I hIa hIb
  exact hab ((mem_partitionSlice.mp hIa).symm.trans (mem_partitionSlice.mp hIb))

theorem exists_large_partitionSlice (H n : ℕ) (hH : 0 < H)
    (hcapacity : 2 * H * n ≤ stateCount H - 1) :
    ∃ W ∈ Finset.Icc 1 (2 * H), n ≤ partitionDimension W := by
  let s := (fullCutoff H).erase ∅
  let t := Finset.Icc 1 (2 * H)
  have hmap : ∀ I ∈ s, doubledEnergy I ∈ t := by
    intro I hI
    obtain ⟨hne, hI⟩ := Finset.mem_erase.mp hI
    have hbound := mem_fullCutoff.mp hI
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hpos := Finset.single_le_sum (f := fun j : ℕ => 2 * j + 1)
      (fun j _ => Nat.zero_le _) hi
    change 2 * i + 1 ≤ doubledEnergy I at hpos
    exact Finset.mem_Icc.mpr ⟨by omega, hbound⟩
  have ht : t.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have hempty : ∅ ∈ fullCutoff H := by simp [doubledEnergy]
  have hcard : t.card * n ≤ s.card := by
    simpa only [t, s, Nat.card_Icc, Nat.add_sub_cancel,
      Finset.card_erase_of_mem hempty, stateCount] using hcapacity
  obtain ⟨W, hW, hn⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmap ht hcard
  refine ⟨W, hW, hn.trans ?_⟩
  apply Finset.card_le_card
  intro I hI
  exact mem_partitionSlice.mpr (Finset.mem_filter.mp hI).2

theorem exists_homogeneous_family (H n : ℕ) (hH : 0 < H)
    (hcapacity : 2 * H * n ≤ stateCount H - 1) :
    ∃ (W : ℕ) (S : Finset (Finset ℕ)),
      0 < W ∧ W ≤ 2 * H ∧ S.card = n ∧ ∀ I ∈ S, doubledEnergy I = W := by
  obtain ⟨W, hW, hn⟩ := exists_large_partitionSlice H n hH hcapacity
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hn
  refine ⟨W, S, (Finset.mem_Icc.mp hW).1, (Finset.mem_Icc.mp hW).2,
    hcard, ?_⟩
  intro I hI
  exact mem_partitionSlice.mp (hS hI)

end Lemmata.FockCircuits
