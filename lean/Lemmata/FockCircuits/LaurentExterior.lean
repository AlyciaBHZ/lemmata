module

public import Lemmata.FockCircuits.PartialCancellation

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.FiniteIdentity

variable (R : Type*) [CommRing R]

def DegreeBound (dir : ℤ) (p : LaurentPolynomial R) (a : ℤ) : Prop :=
  ∀ n ∈ p.coeff.support, dir * n ≤ a

@[simp] theorem degreeBound_zero (dir a : ℤ) : DegreeBound R dir 0 a := by
  simp [DegreeBound]

theorem degreeBound_mono {dir a b : ℤ} {p : LaurentPolynomial R}
    (hp : DegreeBound R dir p a) (hab : a ≤ b) : DegreeBound R dir p b :=
  fun n hn => (hp n hn).trans hab

theorem degreeBound_add {dir a : ℤ} {p q : LaurentPolynomial R}
    (hp : DegreeBound R dir p a) (hq : DegreeBound R dir q a) :
    DegreeBound R dir (p + q) a := by
  intro n hn
  have h : n ∈ p.coeff.support ∪ q.coeff.support :=
    Finsupp.support_add (by simpa only [AddMonoidAlgebra.coeff_add] using hn)
  rcases Finset.mem_union.mp h with hn | hn
  · exact hp n hn
  · exact hq n hn

theorem degreeBound_mul {dir a b : ℤ} {p q : LaurentPolynomial R}
    (hp : DegreeBound R dir p a) (hq : DegreeBound R dir q b) :
    DegreeBound R dir (p * q) (a + b) := by
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
    have hij : i + j ≠ n := by
      intro he
      subst n
      rw [mul_add] at h
      omega
    simp [hij]
  exact (Finsupp.mem_support_iff.mp hn) hz

theorem degreeBound_sum {ι : Type*} (s : Finset ι) (f : ι → LaurentPolynomial R)
    (dir a : ℤ) (hf : ∀ i ∈ s, DegreeBound R dir (f i) a) :
    DegreeBound R dir (∑ i ∈ s, f i) a := by
  classical
  intro n hn
  by_contra h
  have hz : (∑ i ∈ s, f i).coeff n = 0 := by
    rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    by_contra hni
    exact h (hf i hi n (Finsupp.mem_support_iff.mpr hni))
  exact (Finsupp.mem_support_iff.mp hn) hz

theorem degreeBound_zsmul {dir a : ℤ} {p : LaurentPolynomial R}
    (hp : DegreeBound R dir p a) (z : ℤ) : DegreeBound R dir (z • p) a := by
  intro n hn
  apply hp n
  apply Finsupp.mem_support_iff.mpr
  intro hz
  have h : (z • p).coeff n = 0 := by
    change z • p.coeff n = 0
    rw [hz, smul_zero]
  exact (Finsupp.mem_support_iff.mp hn) h

theorem degreeBound_monomial (dir : ℤ) (c : R) (n a : ℤ) (hn : dir * n ≤ a) :
    DegreeBound R dir (LaurentPolynomial.C c * LaurentPolynomial.T n) a := by
  intro i hi
  have he : i = n := Finset.mem_singleton.mp (LaurentPolynomial.support_C_mul_T c n hi)
  simpa only [he] using hn

variable {ι M : Type*} [LinearOrder ι] [AddCommGroup M] [Module (LaurentPolynomial R) M]

def exteriorWeight (ω : ι → ℤ) (I : Finset ι) : ℤ := ∑ i ∈ I, ω i

theorem exteriorWeight_union (ω : ι → ℤ) {I J : Finset ι} (hIJ : Disjoint I J) :
    exteriorWeight ω (I ∪ J) = exteriorWeight ω I + exteriorWeight ω J := by
  exact Finset.sum_union hIJ

def ExteriorBound (b : Module.Basis ι (LaurentPolynomial R) M) (dir : ℤ)
    (ω : ι → ℤ) (a : ℤ) (x : ExteriorAlgebra (LaurentPolynomial R) M) : Prop :=
  ∀ I, DegreeBound R dir (b.ExteriorAlgebra.repr x I) (exteriorWeight ω I + a)

@[simp] theorem exteriorBound_zero (b : Module.Basis ι (LaurentPolynomial R) M)
    (dir : ℤ) (ω : ι → ℤ) (a : ℤ) : ExteriorBound R b dir ω a 0 := by
  intro I
  simp

theorem exteriorBound_add (b : Module.Basis ι (LaurentPolynomial R) M)
    (dir : ℤ) (ω : ι → ℤ) (a : ℤ) {x y : ExteriorAlgebra (LaurentPolynomial R) M}
    (hx : ExteriorBound R b dir ω a x) (hy : ExteriorBound R b dir ω a y) :
    ExteriorBound R b dir ω a (x + y) := by
  intro I
  simp only [map_add, Finsupp.add_apply]
  exact degreeBound_add R (hx I) (hy I)

theorem exteriorBound_sum (b : Module.Basis ι (LaurentPolynomial R) M)
    (dir : ℤ) (ω : ι → ℤ) (a : ℤ) {κ : Type*} (s : Finset κ)
    (f : κ → ExteriorAlgebra (LaurentPolynomial R) M)
    (hf : ∀ k ∈ s, ExteriorBound R b dir ω a (f k)) :
    ExteriorBound R b dir ω a (∑ k ∈ s, f k) := by
  intro I
  simp only [map_sum, Finsupp.finsetSum_apply]
  exact degreeBound_sum R s (fun k => b.ExteriorAlgebra.repr (f k) I) dir _
    (fun k hk => hf k hk I)

theorem exteriorBound_zsmul (b : Module.Basis ι (LaurentPolynomial R) M)
    (dir : ℤ) (ω : ι → ℤ) (a : ℤ) {x : ExteriorAlgebra (LaurentPolynomial R) M}
    (hx : ExteriorBound R b dir ω a x) (z : ℤ) : ExteriorBound R b dir ω a (z • x) := by
  intro I
  simp only [map_zsmul, Finsupp.smul_apply]
  exact degreeBound_zsmul R (hx I) z

theorem exteriorBound_scalar_basis (b : Module.Basis ι (LaurentPolynomial R) M)
    (dir : ℤ) (ω : ι → ℤ) (a : ℤ) (I : Finset ι) (c : LaurentPolynomial R)
    (hc : DegreeBound R dir c (exteriorWeight ω I + a)) :
    ExteriorBound R b dir ω a (c • b.ExteriorAlgebra I) := by
  classical
  intro J
  by_cases hIJ : I = J
  · subst J
    simpa only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply,
      ite_true, smul_eq_mul, mul_one] using hc
  · simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply,
      hIJ, ite_false, smul_eq_mul, mul_zero]
    exact degreeBound_zero R dir _

theorem exteriorBasis_product (b : Module.Basis ι (LaurentPolynomial R) M)
    {I J : Finset ι} (hIJ : Disjoint I J) :
    ∃ ε : ℤˣ, b.ExteriorAlgebra I * b.ExteriorAlgebra J = ε • b.ExteriorAlgebra (I ∪ J) := by
  have hd : Disjoint (Set.powersetCard.ofCard (s := I) rfl).val
      (Set.powersetCard.ofCard (s := J) rfl).val := hIJ
  refine ⟨(Set.powersetCard.permOfDisjoint hd).sign, ?_⟩
  simpa only [Set.powersetCard.coe_disjUnion, Finset.disjUnion_eq_union,
    Set.powersetCard.val_ofCard] using ExteriorAlgebra.basis_mul_of_disjoint b
      (Set.powersetCard.ofCard (s := I) rfl) (Set.powersetCard.ofCard (s := J) rfl) hd

theorem exteriorBound_scalar_basis_mul (b : Module.Basis ι (LaurentPolynomial R) M)
    (dir : ℤ) (ω : ι → ℤ) (a a' : ℤ) (I J : Finset ι)
    (c d : LaurentPolynomial R)
    (hc : DegreeBound R dir c (exteriorWeight ω I + a))
    (hd : DegreeBound R dir d (exteriorWeight ω J + a')) :
    ExteriorBound R b dir ω (a + a')
      ((c • b.ExteriorAlgebra I) * (d • b.ExteriorAlgebra J)) := by
  classical
  by_cases hIJ : Disjoint I J
  · obtain ⟨ε, hε⟩ := exteriorBasis_product R b hIJ
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hε, Units.smul_def, smul_comm]
    apply exteriorBound_zsmul R b dir ω (a + a') _ (ε : ℤ)
    apply exteriorBound_scalar_basis R b dir ω (a + a') (I ∪ J) (c * d)
    have hp := degreeBound_mul R hc hd
    have he : exteriorWeight ω I + a + (exteriorWeight ω J + a') =
        exteriorWeight ω (I ∪ J) + (a + a') := by
      rw [exteriorWeight_union ω hIJ]
      ring
    simpa only [he] using hp
  · have hz : b.ExteriorAlgebra I * b.ExteriorAlgebra J = 0 := by
      exact ExteriorAlgebra.basis_mul_of_not_disjoint b
        (Set.powersetCard.ofCard (s := I) rfl) (Set.powersetCard.ofCard (s := J) rfl) hIJ
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hz, smul_zero]
    exact exteriorBound_zero R b dir ω (a + a')

theorem exteriorBound_mul (b : Module.Basis ι (LaurentPolynomial R) M)
    (dir : ℤ) (ω : ι → ℤ) {a a' : ℤ} {x y : ExteriorAlgebra (LaurentPolynomial R) M}
    (hx : ExteriorBound R b dir ω a x) (hy : ExteriorBound R b dir ω a' y) :
    ExteriorBound R b dir ω (a + a') (x * y) := by
  classical
  have hex (z : ExteriorAlgebra (LaurentPolynomial R) M) : z =
      ∑ I ∈ (b.ExteriorAlgebra.repr z).support,
        b.ExteriorAlgebra.repr z I • b.ExteriorAlgebra I := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using
      (b.ExteriorAlgebra.linearCombination_repr z).symm
  rw [hex x, hex y, Finset.sum_mul]
  apply exteriorBound_sum R b dir ω (a + a')
  intro I hI
  rw [Finset.mul_sum]
  apply exteriorBound_sum R b dir ω (a + a')
  intro J hJ
  exact exteriorBound_scalar_basis_mul R b dir ω a a' I J _ _ (hx I) (hy J)

noncomputable def colourParticleBasis :
    Module.Basis (ℕ ⊕ₗ ℕ) (LaurentPolynomial R) (OneParticle (LaurentPolynomial R)) :=
  (Finsupp.basisSingleOne : Module.Basis ℕ (LaurentPolynomial R)
    (OneParticle (LaurentPolynomial R))).reindex
      (Equiv.natSumNatEquivNat.symm.trans toLex)

def leftGrade (i : ℕ ⊕ₗ ℕ) : ℤ :=
  match ofLex i with
  | Sum.inl n => 2 * (n : ℤ) + 1
  | Sum.inr _ => 0

def rightGrade (i : ℕ ⊕ₗ ℕ) : ℤ :=
  match ofLex i with
  | Sum.inl _ => 0
  | Sum.inr n => 2 * (n : ℤ) + 1

def SourceBound (a : ℤ) (x : Fock (LaurentPolynomial R)) : Prop :=
  ExteriorBound R (colourParticleBasis R) 1 leftGrade (-a) x ∧
    ExteriorBound R (colourParticleBasis R) (-1) rightGrade a x

theorem sourceBound_add {a : ℤ} {x y : Fock (LaurentPolynomial R)}
    (hx : SourceBound R a x) (hy : SourceBound R a y) : SourceBound R a (x + y) :=
  ⟨exteriorBound_add R _ _ _ _ hx.1 hy.1, exteriorBound_add R _ _ _ _ hx.2 hy.2⟩

theorem sourceBound_sum {κ : Type*} (s : Finset κ) (f : κ → Fock (LaurentPolynomial R))
    (a : ℤ) (hf : ∀ i ∈ s, SourceBound R a (f i)) : SourceBound R a (∑ i ∈ s, f i) :=
  ⟨exteriorBound_sum R _ _ _ _ s f (fun i hi => (hf i hi).1),
    exteriorBound_sum R _ _ _ _ s f (fun i hi => (hf i hi).2)⟩

theorem sourceBound_mul {a b : ℤ} {x y : Fock (LaurentPolynomial R)}
    (hx : SourceBound R a x) (hy : SourceBound R b y) : SourceBound R (a + b) (x * y) := by
  refine ⟨?_, exteriorBound_mul R _ _ _ hx.2 hy.2⟩
  simpa only [neg_add] using exteriorBound_mul R _ _ _ hx.1 hy.1

theorem sourceBound_one : SourceBound R 0 1 := by
  have he : (colourParticleBasis R).ExteriorAlgebra ∅ = 1 := by
    exact (Fock.exteriorBasis_eq_sorted_prod (LaurentPolynomial R) _ ∅).trans (by simp)
  have hbound (dir : ℤ) (ω : (ℕ ⊕ₗ ℕ) → ℤ) :
      ExteriorBound R (colourParticleBasis R) dir ω 0 1 := by
    have hc : DegreeBound R dir (1 : LaurentPolynomial R) (exteriorWeight ω ∅ + 0) := by
      simpa only [exteriorWeight, Finset.sum_empty, zero_add,
        map_one, LaurentPolynomial.T_zero, one_mul] using
          degreeBound_monomial R dir 1 0 0 (by simp)
    simpa only [one_smul, he] using
      exteriorBound_scalar_basis R (colourParticleBasis R) dir ω 0 ∅ 1 hc
  exact ⟨by simpa only [neg_zero] using hbound 1 leftGrade, hbound (-1) rightGrade⟩

theorem colourBasis_left_singleton (k : ℕ) :
    (colourParticleBasis R).ExteriorAlgebra {toLex (Sum.inl k)} =
      TwoColour.left (LaurentPolynomial R) k := by
  rw [ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton _)]
  simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, colourParticleBasis,
    Module.Basis.reindex_apply, Finsupp.coe_basisSingleOne,
    Equiv.natSumNatEquivNat_apply, TwoColour.left, Fock.generator]

theorem colourBasis_right_singleton (k : ℕ) :
    (colourParticleBasis R).ExteriorAlgebra {toLex (Sum.inr k)} =
      TwoColour.right (LaurentPolynomial R) k := by
  rw [ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton _)]
  simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, colourParticleBasis,
    Module.Basis.reindex_apply, Finsupp.coe_basisSingleOne,
    Equiv.natSumNatEquivNat_apply, TwoColour.right, Fock.generator]

theorem sourceBound_left_monomial (k : ℕ) (a : ℤ) (c : R) (e : ℤ)
    (he : -a ≤ e ∧ e ≤ 2 * (k : ℤ) + 1 - a) :
    SourceBound R a
      ((LaurentPolynomial.C c * LaurentPolynomial.T e) • TwoColour.left (LaurentPolynomial R) k) := by
  rw [← colourBasis_left_singleton]
  constructor
  · apply exteriorBound_scalar_basis R (colourParticleBasis R) 1 leftGrade (-a)
    apply degreeBound_monomial
    simp only [exteriorWeight, Finset.sum_singleton, leftGrade, ofLex_toLex, one_mul]
    omega
  · apply exteriorBound_scalar_basis R (colourParticleBasis R) (-1) rightGrade a
    apply degreeBound_monomial
    simp only [exteriorWeight, Finset.sum_singleton, rightGrade, ofLex_toLex, zero_add]
    omega

theorem sourceBound_right_monomial (k : ℕ) (a : ℤ) (c : R) (e : ℤ)
    (he : -(2 * (k : ℤ) + 1) - a ≤ e ∧ e ≤ -a) :
    SourceBound R a
      ((LaurentPolynomial.C c * LaurentPolynomial.T e) • TwoColour.right (LaurentPolynomial R) k) := by
  rw [← colourBasis_right_singleton]
  constructor
  · apply exteriorBound_scalar_basis R (colourParticleBasis R) 1 leftGrade (-a)
    apply degreeBound_monomial
    simp only [exteriorWeight, Finset.sum_singleton, leftGrade, ofLex_toLex, zero_add, one_mul]
    exact he.2
  · apply exteriorBound_scalar_basis R (colourParticleBasis R) (-1) rightGrade a
    apply degreeBound_monomial
    simp only [exteriorWeight, Finset.sum_singleton, rightGrade, ofLex_toLex]
    omega

theorem sourceBound_left (k : ℕ) : SourceBound R 0 (TwoColour.left (LaurentPolynomial R) k) := by
  simpa using sourceBound_left_monomial R k 0 1 0 (by omega)

theorem sourceBound_right (k : ℕ) : SourceBound R 0 (TwoColour.right (LaurentPolynomial R) k) := by
  simpa using sourceBound_right_monomial R k 0 1 0 (by omega)

theorem sourceBound_kernel (L : ℕ) : SourceBound R 0 (TwoColour.kernel (LaurentPolynomial R) L) := by
  induction L with
  | zero => simpa using sourceBound_one R
  | succ L ih =>
    rw [TwoColour.kernel_succ]
    have hp : SourceBound R 0
        (TwoColour.left (LaurentPolynomial R) L * TwoColour.right (LaurentPolynomial R) L) := by
      simpa only [zero_add] using sourceBound_mul R (sourceBound_left R L) (sourceBound_right R L)
    simpa only [zero_add, TwoColour.factor] using
      sourceBound_mul R (sourceBound_add R (sourceBound_one R) hp) ih

noncomputable def scaledPositive (m k : ℕ) : LaurentPolynomial R :=
  LaurentPolynomial.C (positiveCoefficient m k : R) * LaurentPolynomial.T (2 * ((k : ℤ) - m))

noncomputable def scaledNegative (m k : ℕ) : LaurentPolynomial R :=
  LaurentPolynomial.C (negativeCoefficient m k : R) * LaurentPolynomial.T (-2 * ((k : ℤ) + m + 1))

noncomputable def scaledSymbol (L m : ℕ) : Fock (LaurentPolynomial R) :=
  ExteriorAlgebra.ι (LaurentPolynomial R)
      (TwoColour.leftVector (LaurentPolynomial R) L (fun k => scaledPositive R m k)) +
    ExteriorAlgebra.ι (LaurentPolynomial R)
      (TwoColour.rightVector (LaurentPolynomial R) L (fun k => scaledNegative R m k))

noncomputable def unscaledSymbol (L m : ℕ) : Fock (LaurentPolynomial R) :=
  ExteriorAlgebra.ι (LaurentPolynomial R)
      (TwoColour.leftVector (LaurentPolynomial R) L
        (fun k => LaurentPolynomial.C (positiveCoefficient m k : R))) +
    ExteriorAlgebra.ι (LaurentPolynomial R)
      (TwoColour.rightVector (LaurentPolynomial R) L
        (fun k => LaurentPolynomial.C (negativeCoefficient m k : R)))

theorem sourceBound_scaledSymbol (L m : ℕ) :
    SourceBound R (2 * (m : ℤ) + 1) (scaledSymbol R L m) := by
  unfold scaledSymbol
  rw [TwoColour.createVector_left, TwoColour.createVector_right]
  apply sourceBound_add R
  · apply sourceBound_sum R Finset.univ _ (2 * (m : ℤ) + 1)
    intro k hk
    exact sourceBound_left_monomial R k (2 * (m : ℤ) + 1) _ _ (by omega)
  · apply sourceBound_sum R Finset.univ _ (2 * (m : ℤ) + 1)
    intro k hk
    exact sourceBound_right_monomial R k (2 * (m : ℤ) + 1) _ _ (by omega)

theorem sourceBound_unscaledSymbol (L m : ℕ) : SourceBound R 0 (unscaledSymbol R L m) := by
  unfold unscaledSymbol
  rw [TwoColour.createVector_left, TwoColour.createVector_right]
  apply sourceBound_add R
  · apply sourceBound_sum R Finset.univ _ 0
    intro k hk
    simpa using sourceBound_left_monomial R k 0 (positiveCoefficient m k : R) 0 (by omega)
  · apply sourceBound_sum R Finset.univ _ 0
    intro k hk
    simpa using sourceBound_right_monomial R k 0 (negativeCoefficient m k : R) 0 (by omega)

def sourceWeight (i : ℕ ⊕ ℕ) : ℤ :=
  match i with
  | Sum.inl m => 2 * (m : ℤ) + 1
  | Sum.inr _ => 0

noncomputable def sourceSymbol (L : ℕ) (i : ℕ ⊕ ℕ) : Fock (LaurentPolynomial R) :=
  match i with
  | Sum.inl m => scaledSymbol R L m
  | Sum.inr m => unscaledSymbol R L m

theorem sourceBound_sourceSymbol (L : ℕ) (i : ℕ ⊕ ℕ) :
    SourceBound R (sourceWeight i) (sourceSymbol R L i) := by
  cases i with
  | inl m => exact sourceBound_scaledSymbol R L m
  | inr m => exact sourceBound_unscaledSymbol R L m

theorem sourceBound_product (L : ℕ) (A : List (ℕ ⊕ ℕ)) :
    SourceBound R (A.map sourceWeight).sum (A.map (sourceSymbol R L)).prod := by
  induction A with
  | nil => simpa using sourceBound_one R
  | cons a A ih =>
    simpa only [List.map_cons, List.sum_cons, List.prod_cons] using
      sourceBound_mul R (sourceBound_sourceSymbol R L a) ih

theorem sourceBound_remainder (L : ℕ) (A : List (ℕ ⊕ ℕ)) :
    SourceBound R (A.map sourceWeight).sum
      ((A.map (sourceSymbol R L)).prod * TwoColour.kernel (LaurentPolynomial R) L) := by
  simpa only [add_zero] using
    sourceBound_mul R (sourceBound_product R L A) (sourceBound_kernel R L)

theorem colour_images_disjoint (I J : Finset ℕ) :
    Disjoint (I.image fun i => toLex (Sum.inl i : ℕ ⊕ ℕ))
      (J.image fun j => toLex (Sum.inr j : ℕ ⊕ ℕ)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hx'
  have h := congrArg ofLex he
  cases h

theorem exteriorWeight_left_colourIndex (I J : Finset ℕ) :
    exteriorWeight leftGrade (colourIndex I J) = (doubledEnergy I : ℤ) := by
  have hL : Function.Injective (fun i : ℕ => toLex (Sum.inl i : ℕ ⊕ ℕ)) := by
    intro i j h
    exact Sum.inl.inj (congrArg ofLex h)
  have hR : Function.Injective (fun i : ℕ => toLex (Sum.inr i : ℕ ⊕ ℕ)) := by
    intro i j h
    exact Sum.inr.inj (congrArg ofLex h)
  unfold exteriorWeight colourIndex
  rw [Finset.sum_union (colour_images_disjoint I J),
    Finset.sum_image (fun _ _ _ _ h => hL h), Finset.sum_image (fun _ _ _ _ h => hR h)]
  simp only [leftGrade, ofLex_toLex, Finset.sum_const_zero, add_zero,
    doubledEnergy, Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  simp only [Nat.cast_one]

theorem exteriorWeight_right_colourIndex (I J : Finset ℕ) :
    exteriorWeight rightGrade (colourIndex I J) = (doubledEnergy J : ℤ) := by
  have hL : Function.Injective (fun i : ℕ => toLex (Sum.inl i : ℕ ⊕ ℕ)) := by
    intro i j h
    exact Sum.inl.inj (congrArg ofLex h)
  have hR : Function.Injective (fun i : ℕ => toLex (Sum.inr i : ℕ ⊕ ℕ)) := by
    intro i j h
    exact Sum.inr.inj (congrArg ofLex h)
  unfold exteriorWeight colourIndex
  rw [Finset.sum_union (colour_images_disjoint I J),
    Finset.sum_image (fun _ _ _ _ h => hL h), Finset.sum_image (fun _ _ _ _ h => hR h)]
  simp only [rightGrade, ofLex_toLex, Finset.sum_const_zero, zero_add,
    doubledEnergy, Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  simp only [Nat.cast_one]

theorem remainder_coefficient_bounds (L : ℕ) (A : List (ℕ ⊕ ℕ)) (I J : Finset ℕ) :
    UpperBound R
      ((colourBasis (LaurentPolynomial R)).repr
        ((A.map (sourceSymbol R L)).prod * TwoColour.kernel (LaurentPolynomial R) L)
        (colourIndex I J))
      ((doubledEnergy I : ℤ) - (A.map sourceWeight).sum) ∧
    LowerBound R
      ((colourBasis (LaurentPolynomial R)).repr
        ((A.map (sourceSymbol R L)).prod * TwoColour.kernel (LaurentPolynomial R) L)
        (colourIndex I J))
      (-(doubledEnergy J : ℤ) - (A.map sourceWeight).sum) := by
  have h := sourceBound_remainder R L A
  constructor
  · intro n hn
    have hn' : n ∈ ((colourParticleBasis R).ExteriorAlgebra.repr
        ((A.map (sourceSymbol R L)).prod * TwoColour.kernel (LaurentPolynomial R) L)
        (colourIndex I J)).coeff.support := hn
    have he := h.1 (colourIndex I J) n hn'
    rw [exteriorWeight_left_colourIndex] at he
    simpa only [one_mul, sub_eq_add_neg] using he
  · intro n hn
    have hn' : n ∈ ((colourParticleBasis R).ExteriorAlgebra.repr
        ((A.map (sourceSymbol R L)).prod * TwoColour.kernel (LaurentPolynomial R) L)
        (colourIndex I J)).coeff.support := hn
    have he := h.2 (colourIndex I J) n hn'
    rw [exteriorWeight_right_colourIndex] at he
    omega

noncomputable def sourceCoefficients (L : ℕ) (i : ℕ ⊕ ℕ) :
    (Fin L → LaurentPolynomial R) × (Fin L → LaurentPolynomial R) :=
  match i with
  | Sum.inl m => (fun k => scaledPositive R m k, fun k => scaledNegative R m k)
  | Sum.inr m => (fun k => LaurentPolynomial.C (positiveCoefficient m k : R),
      fun k => LaurentPolynomial.C (negativeCoefficient m k : R))

theorem normal_remainder_kernel (L : ℕ) (A : List (ℕ ⊕ ℕ)) :
    Fock.normalList (LaurentPolynomial R)
        (TwoColour.colouredList (LaurentPolynomial R) L (A.map (sourceCoefficients R L)))
        (TwoColour.kernel (LaurentPolynomial R) L) =
      (A.map (sourceSymbol R L)).prod * TwoColour.kernel (LaurentPolynomial R) L := by
  rw [TwoColour.normalList_kernel]
  congr 1
  unfold TwoColour.colouredProduct
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  cases i <;> rfl

theorem normal_remainder_coefficient_bounds (L : ℕ) (A : List (ℕ ⊕ ℕ)) (I J : Finset ℕ) :
    let p := (colourBasis (LaurentPolynomial R)).repr
      (Fock.normalList (LaurentPolynomial R)
        (TwoColour.colouredList (LaurentPolynomial R) L (A.map (sourceCoefficients R L)))
        (TwoColour.kernel (LaurentPolynomial R) L)) (colourIndex I J)
    UpperBound R p ((doubledEnergy I : ℤ) - (A.map sourceWeight).sum) ∧
      LowerBound R p (-(doubledEnergy J : ℤ) - (A.map sourceWeight).sum) := by
  dsimp only
  rw [normal_remainder_kernel]
  exact remainder_coefficient_bounds R L A I J

end Lemmata.FockCircuits.FiniteIdentity
