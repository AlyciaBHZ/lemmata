module

public import Lemmata.FockCircuits.LaurentExterior

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Lemmata.FockCircuits.FiniteIdentity

variable (R : Type*) [CommRing R]

noncomputable def colourParticles : Module.Basis (ℕ ⊕ₗ ℕ) R (OneParticle R) :=
  (Finsupp.basisSingleOne : Module.Basis ℕ R (OneParticle R)).reindex
    (Equiv.natSumNatEquivNat.symm.trans toLex)

def balanceGrade (i : ℕ ⊕ₗ ℕ) : ℤ := leftGrade i - rightGrade i

noncomputable def dilationParticleBy (ω : (ℕ ⊕ₗ ℕ) → ℤ) :
    OneParticle R →ₗ[R] OneParticle (LaurentPolynomial R) :=
  (colourParticles R).constr R
    (fun i => LaurentPolynomial.T (R := R) (ω i) • colourParticles (LaurentPolynomial R) i)

noncomputable def dilationBy (ω : (ℕ ⊕ₗ ℕ) → ℤ) :
    Fock R →ₐ[R] Fock (LaurentPolynomial R) :=
  ExteriorAlgebra.lift R
    ⟨((ExteriorAlgebra.ι (LaurentPolynomial R)).restrictScalars R).comp (dilationParticleBy R ω),
      fun m => ExteriorAlgebra.ι_sq_zero (R := LaurentPolynomial R) (dilationParticleBy R ω m)⟩

theorem dilationBy_colour_generator (ω : (ℕ ⊕ₗ ℕ) → ℤ) (i : ℕ ⊕ₗ ℕ) :
    dilationBy R ω (ExteriorAlgebra.ι R (colourParticles R i)) =
      LaurentPolynomial.T (R := R) (ω i) •
        ExteriorAlgebra.ι (LaurentPolynomial R) (colourParticles (LaurentPolynomial R) i) := by
  simp only [dilationBy, ExteriorAlgebra.lift_ι_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, dilationParticleBy, Module.Basis.constr_basis, map_smul]

theorem dilationBy_colour_word (ω : (ℕ ⊕ₗ ℕ) → ℤ) (A : List (ℕ ⊕ₗ ℕ)) :
    dilationBy R ω (A.map fun i => ExteriorAlgebra.ι R (colourParticles R i)).prod =
      LaurentPolynomial.T (R := R) (A.map ω).sum •
        (A.map fun i => ExteriorAlgebra.ι (LaurentPolynomial R)
          (colourParticles (LaurentPolynomial R) i)).prod := by
  induction A with
  | nil => simp
  | cons i A ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, map_mul,
      dilationBy_colour_generator, ih, smul_mul_assoc, mul_smul_comm,
      smul_smul, LaurentPolynomial.T_add]
    congr 1
    ring

theorem dilationBy_colourBasis (ω : (ℕ ⊕ₗ ℕ) → ℤ) (I : Finset (ℕ ⊕ₗ ℕ)) :
    dilationBy R ω (colourBasis R I) =
      LaurentPolynomial.T (R := R) (exteriorWeight ω I) •
        colourBasis (LaurentPolynomial R) I := by
  change dilationBy R ω ((colourParticles R).ExteriorAlgebra I) =
    LaurentPolynomial.T (R := R) (exteriorWeight ω I) •
      (colourParticles (LaurentPolynomial R)).ExteriorAlgebra I
  rw [Fock.exteriorBasis_eq_sorted_prod R,
    Fock.exteriorBasis_eq_sorted_prod (LaurentPolynomial R), dilationBy_colour_word]
  have hs : exteriorWeight ω I = (I.sort.map ω).sum := by
    simpa only [exteriorWeight, Finset.sort_toFinset] using
      List.sum_toFinset ω (I.sort_nodup (· ≤ ·))
  rw [← hs]

theorem dilationBy_coefficient (ω : (ℕ ⊕ₗ ℕ) → ℤ) (x : Fock R) (I : Finset (ℕ ⊕ₗ ℕ)) :
    (colourBasis (LaurentPolynomial R)).repr (dilationBy R ω x) I =
      LaurentPolynomial.C ((colourBasis R).repr x I) *
        LaurentPolynomial.T (R := R) (exteriorWeight ω I) := by
  let f : Fock R →ₗ[R] LaurentPolynomial R :=
    (Finsupp.lapply I).comp
      (((colourBasis (LaurentPolynomial R)).repr.toLinearMap.restrictScalars R).comp
        (dilationBy R ω).toLinearMap)
  let g : Fock R →ₗ[R] LaurentPolynomial R :=
    (LinearMap.mulRight R (LaurentPolynomial.T (R := R) (exteriorWeight ω I))).comp
      ((Algebra.linearMap R (LaurentPolynomial R)).comp ((colourBasis R).coord I))
  have hfg : f = g := by
    apply (colourBasis R).ext
    intro J
    change (colourBasis (LaurentPolynomial R)).repr (dilationBy R ω (colourBasis R J)) I =
      algebraMap R (LaurentPolynomial R) ((colourBasis R).repr (colourBasis R J) I) *
        LaurentPolynomial.T (R := R) (exteriorWeight ω I)
    rw [dilationBy_colourBasis]
    simp only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply, smul_eq_mul]
    by_cases hJI : J = I
    · subst J
      simp
    · simp [hJI]
  have he := LinearMap.congr_fun hfg x
  change (colourBasis (LaurentPolynomial R)).repr (dilationBy R ω x) I =
    algebraMap R (LaurentPolynomial R) ((colourBasis R).repr x I) *
      LaurentPolynomial.T (R := R) (exteriorWeight ω I) at he
  simpa only [LaurentPolynomial.C_eq_algebraMap] using he

noncomputable abbrev dilation := dilationBy R balanceGrade

theorem dilation_colour_generator (i : ℕ ⊕ₗ ℕ) :
    dilation R (ExteriorAlgebra.ι R (colourParticles R i)) =
      LaurentPolynomial.T (R := R) (balanceGrade i) •
        ExteriorAlgebra.ι (LaurentPolynomial R) (colourParticles (LaurentPolynomial R) i) :=
  dilationBy_colour_generator R balanceGrade i

theorem dilation_coefficient (x : Fock R) (I : Finset (ℕ ⊕ₗ ℕ)) :
    (colourBasis (LaurentPolynomial R)).repr (dilation R x) I =
      LaurentPolynomial.C ((colourBasis R).repr x I) *
        LaurentPolynomial.T (R := R) (exteriorWeight balanceGrade I) :=
  dilationBy_coefficient R balanceGrade x I

theorem shifted_dilation_generator (i : ℕ ⊕ₗ ℕ) (a : ℤ) (c : R) :
    LaurentPolynomial.T (R := R) (-a) •
        dilation R (c • ExteriorAlgebra.ι R (colourParticles R i)) =
      (LaurentPolynomial.C c * LaurentPolynomial.T (R := R) (balanceGrade i - a)) •
        ExteriorAlgebra.ι (LaurentPolynomial R) (colourParticles (LaurentPolynomial R) i) := by
  rw [map_smul, dilation_colour_generator]
  have htower (u : LaurentPolynomial R) (z : Fock (LaurentPolynomial R)) :
      c • (u • z) = (LaurentPolynomial.C c * u) • z := by
    have hc : c • u = LaurentPolynomial.C c * u := by
      rw [Algebra.smul_def, LaurentPolynomial.C_eq_algebraMap]
    calc
      _ = (c • u) • z := (smul_assoc c u z).symm
      _ = _ := by rw [hc]
  rw [htower, smul_smul]
  have hs : LaurentPolynomial.T (R := R) (-a) *
      (LaurentPolynomial.C c * LaurentPolynomial.T (R := R) (balanceGrade i)) =
      LaurentPolynomial.C c * LaurentPolynomial.T (R := R) (balanceGrade i - a) := by
    calc
      _ = LaurentPolynomial.C c *
          (LaurentPolynomial.T (R := R) (-a) * LaurentPolynomial.T (R := R) (balanceGrade i)) := by ring
      _ = _ := by rw [← LaurentPolynomial.T_add]; congr 2; omega
  rw [hs]

theorem shifted_dilation_left (k : ℕ) (a : ℤ) (c : R) :
    LaurentPolynomial.T (R := R) (-a) • dilation R (c • TwoColour.left R k) =
      (LaurentPolynomial.C c * LaurentPolynomial.T (R := R) (2 * (k : ℤ) + 1 - a)) •
        TwoColour.left (LaurentPolynomial R) k := by
  simpa [colourParticles, balanceGrade, leftGrade, rightGrade,
    Module.Basis.reindex_apply, Finsupp.coe_basisSingleOne,
    Equiv.natSumNatEquivNat_apply, TwoColour.left, Fock.generator] using
      shifted_dilation_generator R (toLex (Sum.inl k)) a c

theorem shifted_dilation_right (k : ℕ) (a : ℤ) (c : R) :
    LaurentPolynomial.T (R := R) (-a) • dilation R (c • TwoColour.right R k) =
      (LaurentPolynomial.C c * LaurentPolynomial.T (R := R) (-(2 * (k : ℤ) + 1) - a)) •
        TwoColour.right (LaurentPolynomial R) k := by
  simpa [colourParticles, balanceGrade, leftGrade, rightGrade,
    Module.Basis.reindex_apply, Finsupp.coe_basisSingleOne,
    Equiv.natSumNatEquivNat_apply, TwoColour.right, Fock.generator] using
      shifted_dilation_generator R (toLex (Sum.inr k)) a c

theorem dilation_left (k : ℕ) :
    dilation R (TwoColour.left R k) =
      LaurentPolynomial.T (R := R) (2 * (k : ℤ) + 1) • TwoColour.left (LaurentPolynomial R) k := by
  simpa using shifted_dilation_left R k 0 1

theorem dilation_right (k : ℕ) :
    dilation R (TwoColour.right R k) =
      LaurentPolynomial.T (R := R) (-(2 * (k : ℤ) + 1)) • TwoColour.right (LaurentPolynomial R) k := by
  simpa using shifted_dilation_right R k 0 1

theorem dilation_kernel (L : ℕ) :
    dilation R (TwoColour.kernel R L) = TwoColour.kernel (LaurentPolynomial R) L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [TwoColour.kernel_succ, map_mul, ih, TwoColour.kernel_succ]
    congr 1
    simp only [TwoColour.factor, map_add, map_one, map_mul, dilation_left, dilation_right,
      smul_mul_assoc, mul_smul_comm, smul_smul, ← LaurentPolynomial.T_add,
      add_neg_cancel, neg_add_cancel, LaurentPolynomial.T_zero, one_smul]

noncomputable def plainSymbol (L m : ℕ) : Fock R :=
  ExteriorAlgebra.ι R (TwoColour.leftVector R L (fun k => (positiveCoefficient m k : R))) +
    ExteriorAlgebra.ι R (TwoColour.rightVector R L (fun k => (negativeCoefficient m k : R)))

theorem scaledSymbol_eq_dilation (L m : ℕ) :
    scaledSymbol R L m = LaurentPolynomial.T (R := R) (-(2 * (m : ℤ) + 1)) •
      dilation R (plainSymbol R L m) := by
  unfold scaledSymbol plainSymbol
  simp only [TwoColour.createVector_left, TwoColour.createVector_right,
    map_add, map_sum, smul_add, Finset.smul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have he : 2 * ((k : ℤ) - m) = 2 * (k : ℤ) + 1 - (2 * (m : ℤ) + 1) := by ring
    simpa only [scaledPositive, he] using
      (shifted_dilation_left R k (2 * (m : ℤ) + 1) (positiveCoefficient m k : R)).symm
  · apply Finset.sum_congr rfl
    intro k hk
    have he : -2 * ((k : ℤ) + m + 1) = -(2 * (k : ℤ) + 1) - (2 * (m : ℤ) + 1) := by ring
    simpa only [scaledNegative, he] using
      (shifted_dilation_right R k (2 * (m : ℤ) + 1) (negativeCoefficient m k : R)).symm

def wordWeight (A : List ℕ) : ℤ := (A.map fun m : ℕ => 2 * (m : ℤ) + 1).sum

@[simp] theorem wordWeight_cons (m : ℕ) (A : List ℕ) :
    wordWeight (m :: A) = 2 * (m : ℤ) + 1 + wordWeight A := rfl

theorem scaledProduct_eq_dilation (L : ℕ) (A : List ℕ) :
    (A.map (scaledSymbol R L)).prod = LaurentPolynomial.T (R := R) (-wordWeight A) •
      dilation R (A.map (plainSymbol R L)).prod := by
  induction A with
  | nil => simp [wordWeight]
  | cons m A ih =>
    simp only [List.map_cons, List.prod_cons, scaledSymbol_eq_dilation, ih, map_mul,
      smul_mul_assoc, mul_smul_comm, smul_smul, ← LaurentPolynomial.T_add,
      wordWeight_cons]
    congr 2
    ring

theorem scaledKernelWord_eq_dilation (L : ℕ) (A : List ℕ) :
    (A.map (scaledSymbol R L)).prod * TwoColour.kernel (LaurentPolynomial R) L =
      LaurentPolynomial.T (R := R) (-wordWeight A) •
        dilation R ((A.map (plainSymbol R L)).prod * TwoColour.kernel R L) := by
  rw [scaledProduct_eq_dilation, smul_mul_assoc, map_mul, dilation_kernel]

theorem balanceGrade_colourIndex (I J : Finset ℕ) :
    exteriorWeight balanceGrade (colourIndex I J) =
      (doubledEnergy I : ℤ) - (doubledEnergy J : ℤ) := by
  simp only [exteriorWeight, balanceGrade, Finset.sum_sub_distrib]
  exact congrArg₂ (· - ·) (exteriorWeight_left_colourIndex I J)
    (exteriorWeight_right_colourIndex I J)

theorem scaledKernelWord_coefficient (L : ℕ) (A : List ℕ) (I J : Finset ℕ) :
    (colourBasis (LaurentPolynomial R)).repr
        ((A.map (scaledSymbol R L)).prod * TwoColour.kernel (LaurentPolynomial R) L)
        (colourIndex I J) =
      LaurentPolynomial.C
          ((colourBasis R).repr ((A.map (plainSymbol R L)).prod * TwoColour.kernel R L)
            (colourIndex I J)) *
        LaurentPolynomial.T (R := R) ((doubledEnergy I : ℤ) - doubledEnergy J - wordWeight A) := by
  rw [scaledKernelWord_eq_dilation, map_smul, Finsupp.smul_apply, smul_eq_mul,
    dilation_coefficient, balanceGrade_colourIndex]
  calc
    _ = LaurentPolynomial.C _ *
        (LaurentPolynomial.T (R := R) (-wordWeight A) *
          LaurentPolynomial.T (R := R) ((doubledEnergy I : ℤ) - doubledEnergy J)) := by ring
    _ = _ := by rw [← LaurentPolynomial.T_add]; congr 2; omega

noncomputable abbrev constantEmbedding := dilationBy R (fun _ => 0)

theorem constantEmbedding_coefficient (x : Fock R) (I : Finset (ℕ ⊕ₗ ℕ)) :
    (colourBasis (LaurentPolynomial R)).repr (constantEmbedding R x) I =
      LaurentPolynomial.C ((colourBasis R).repr x I) := by
  simpa only [exteriorWeight, Finset.sum_const_zero, LaurentPolynomial.T_zero, mul_one] using
    dilationBy_coefficient R (fun _ => 0) x I

theorem constantEmbedding_left (k : ℕ) :
    constantEmbedding R (TwoColour.left R k) = TwoColour.left (LaurentPolynomial R) k := by
  simpa [colourParticles, Module.Basis.reindex_apply, Finsupp.coe_basisSingleOne,
    Equiv.natSumNatEquivNat_apply, TwoColour.left, Fock.generator] using
      dilationBy_colour_generator R (fun _ => 0) (toLex (Sum.inl k))

theorem constantEmbedding_right (k : ℕ) :
    constantEmbedding R (TwoColour.right R k) = TwoColour.right (LaurentPolynomial R) k := by
  simpa [colourParticles, Module.Basis.reindex_apply, Finsupp.coe_basisSingleOne,
    Equiv.natSumNatEquivNat_apply, TwoColour.right, Fock.generator] using
      dilationBy_colour_generator R (fun _ => 0) (toLex (Sum.inr k))

theorem constantEmbedding_kernel (L : ℕ) :
    constantEmbedding R (TwoColour.kernel R L) = TwoColour.kernel (LaurentPolynomial R) L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [TwoColour.kernel_succ, map_mul, ih, TwoColour.kernel_succ]
    simp only [TwoColour.factor, map_add, map_one, map_mul,
      constantEmbedding_left, constantEmbedding_right]

theorem constantEmbedding_plainSymbol (L m : ℕ) :
    constantEmbedding R (plainSymbol R L m) = unscaledSymbol R L m := by
  have hc (c : R) (z : Fock (LaurentPolynomial R)) :
      LaurentPolynomial.C c • z = c • z := by
    simpa only [LaurentPolynomial.C_eq_algebraMap] using
      IsScalarTower.algebraMap_smul (LaurentPolynomial R) c z
  simp only [plainSymbol, unscaledSymbol, TwoColour.createVector_left,
    TwoColour.createVector_right, map_add, map_sum, map_smul,
    constantEmbedding_left, constantEmbedding_right, hc]

theorem constantKernelWord_coefficient (L : ℕ) (A : List ℕ) (I J : Finset ℕ) :
    (colourBasis (LaurentPolynomial R)).repr
        ((A.map (unscaledSymbol R L)).prod * TwoColour.kernel (LaurentPolynomial R) L)
        (colourIndex I J) =
      LaurentPolynomial.C
        ((colourBasis R).repr ((A.map (plainSymbol R L)).prod * TwoColour.kernel R L)
          (colourIndex I J)) := by
  have he : (A.map (unscaledSymbol R L)).prod * TwoColour.kernel (LaurentPolynomial R) L =
      constantEmbedding R ((A.map (plainSymbol R L)).prod * TwoColour.kernel R L) := by
    simp only [map_mul, map_list_prod, List.map_map, Function.comp_def,
      constantEmbedding_plainSymbol, constantEmbedding_kernel]
  rw [he, constantEmbedding_coefficient]

theorem plainProduct_kernel (L : ℕ) (A : Index L) :
    kernel R L (Pi.single A 1) =
      (A.val.sort.map (plainSymbol R L)).prod * TwoColour.kernel R L := by
  rw [kernel, realize_single, one_smul, substitution_basis]
  congr 1
  unfold TwoColour.colouredProduct sourceWord
  rw [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro m hm
  rfl

theorem wordWeight_eq_natSum (A : List ℕ) :
    wordWeight A = ((A.map fun m : ℕ => 2 * m + 1).sum : ℤ) := by
  induction A with
  | nil => simp [wordWeight]
  | cons m A ih =>
    simp only [wordWeight_cons, List.map_cons, List.sum_cons, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, ih]

theorem wordWeight_sort (I : Finset ℕ) : wordWeight I.sort = (doubledEnergy I : ℤ) := by
  rw [wordWeight_eq_natSum]
  apply congrArg (fun n : ℕ => (n : ℤ))
  simpa only [Finset.sort_toFinset, doubledEnergy] using
    (List.sum_toFinset (fun m : ℕ => 2 * m + 1) (I.sort_nodup (· ≤ ·))).symm

noncomputable def scaledMatrix (L : ℕ) (A : Index L) :
    Matrix (Index L) (Index L) (LaurentPolynomial R) :=
  fun I J => (dualSign J.val : LaurentPolynomial R) *
    (colourBasis (LaurentPolynomial R)).repr
      ((A.val.sort.map (scaledSymbol R L)).prod * TwoColour.kernel (LaurentPolynomial R) L)
      (colourIndex I.val J.val)

theorem scaledMatrix_eq_monomial (L : ℕ) (A I J : Index L) :
    scaledMatrix R L A I J =
      LaurentPolynomial.C (matrix R L (Pi.single A 1) I J) *
        LaurentPolynomial.T (R := R)
          ((doubledEnergy I.val : ℤ) - doubledEnergy J.val - doubledEnergy A.val) := by
  rw [scaledMatrix, scaledKernelWord_coefficient, wordWeight_sort, ← plainProduct_kernel]
  simp only [matrix, map_mul, map_intCast, mul_assoc]

theorem unscaledMatrix_eq_constant (L : ℕ) (A I J : Index L) :
    (dualSign J.val : LaurentPolynomial R) *
        (colourBasis (LaurentPolynomial R)).repr
          ((A.val.sort.map (unscaledSymbol R L)).prod * TwoColour.kernel (LaurentPolynomial R) L)
          (colourIndex I.val J.val) =
      LaurentPolynomial.C (matrix R L (Pi.single A 1) I J) := by
  rw [constantKernelWord_coefficient, ← plainProduct_kernel]
  simp only [matrix, map_mul, map_intCast]

end Lemmata.FockCircuits.FiniteIdentity
