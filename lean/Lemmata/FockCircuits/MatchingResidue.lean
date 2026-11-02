module

public import Lemmata.FockCircuits.ExteriorMatching
public import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Algebra.Polynomial.Coeff

@[expose] public section

set_option autoImplicit false

open scoped BigOperators TensorProduct

namespace Lemmata.FockCircuits.Matching

variable (R : Type*) [CommRing R]

noncomputable def poleSelector (s : R) (d : ℕ) : Polynomial R →ₗ[R] R :=
  ∑ j ∈ Finset.range (d + 1), s ^ (d - j) • Polynomial.lcoeff R j

theorem poleSelector_monomial (s c : R) (d j : ℕ) :
    poleSelector R s d (Polynomial.monomial j c) =
      if j ≤ d then s ^ (d - j) * c else 0 := by
  classical
  simp [poleSelector, Polynomial.lcoeff_apply, Polynomial.coeff_monomial,
    Finset.mem_range, Nat.lt_succ_iff, smul_eq_mul]

variable {α : Type*}

noncomputable def sourceNormalMap (x : α → OneParticle R × OneParticle R) :
    ExteriorAlgebra R (α →₀ R) →ₗ[R] Module.End R (Fock R) :=
  (Fock.normalSymbol R).comp
    (ExteriorAlgebra.map (Finsupp.linearCombination R x)).toLinearMap

theorem sourceNormalMap_word (x : α → OneParticle R × OneParticle R) (A : List α) :
    sourceNormalMap R x (word R (fun i => Finsupp.single i 1) A) =
      Fock.normalList R (A.map x) := by
  change Fock.normalSymbol R
    (ExteriorAlgebra.map (Finsupp.linearCombination R x)
      (word R (fun i => Finsupp.single i 1) A)) = _
  have he : ExteriorAlgebra.map (Finsupp.linearCombination R x)
      (word R (fun i => Finsupp.single i 1) A) =
      ((A.map x).map (ExteriorAlgebra.ι R)).prod := by
    unfold word
    simp only [map_list_prod, List.map_map, Function.comp_def,
      ExteriorAlgebra.map_apply_ι, Finsupp.linearCombination_single, one_smul]
  rw [he, Fock.normalSymbol_word]

noncomputable def residueMap (s : R) (d : ℕ) (x : α → OneParticle R × OneParticle R) :
    ExteriorAlgebra (Polynomial R) (Polynomial R ⊗[R] (α →₀ R)) →ₗ[R]
      Module.End R (Fock R) :=
  (TensorProduct.lid R (Module.End R (Fock R))).toLinearMap.comp
    ((TensorProduct.map (poleSelector R s d) (sourceNormalMap R x)).comp
      (LinearMap.restrictScalars R
        (ExteriorAlgebra.baseChangeEquiv R (α →₀ R) (Polynomial R)).symm.toLinearMap))

noncomputable def extendedSource (i : α) : Polynomial R ⊗[R] (α →₀ R) :=
  (1 : Polynomial R) ⊗ₜ[R] Finsupp.single i 1

theorem baseChange_generator (i : α) :
    (ExteriorAlgebra.baseChangeEquiv R (α →₀ R) (Polynomial R)).symm
        (ExteriorAlgebra.ι (Polynomial R) (extendedSource R i)) =
      (1 : Polynomial R) ⊗ₜ[R] ExteriorAlgebra.ι R (Finsupp.single i 1) := by
  simpa only [extendedSource] using
    ExteriorAlgebra.baseChangeEquiv_symm_apply R (α →₀ R) (Polynomial R)
      (1 : Polynomial R) (Finsupp.single i 1)

theorem baseChange_word (A : List α) :
    (ExteriorAlgebra.baseChangeEquiv R (α →₀ R) (Polynomial R)).symm
        (word (Polynomial R) (extendedSource R) A) =
      (1 : Polynomial R) ⊗ₜ[R] word R (fun i => Finsupp.single i 1) A := by
  induction A with
  | nil => simp [Algebra.TensorProduct.one_def]
  | cons a A ih =>
    rw [word_cons, map_mul, baseChange_generator, ih,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, word_cons]

theorem residueMap_smul_word (s : R) (d : ℕ)
    (x : α → OneParticle R × OneParticle R) (p : Polynomial R) (A : List α) :
    residueMap R s d x (p • word (Polynomial R) (extendedSource R) A) =
      poleSelector R s d p • Fock.normalList R (A.map x) := by
  unfold residueMap
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    AlgEquiv.toLinearMap_apply, map_smul, baseChange_word,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.map_tmul,
    sourceNormalMap_word]
  rfl

noncomputable def extendedBasis :
    Module.Basis α (Polynomial R) (Polynomial R ⊗[R] (α →₀ R)) :=
  (Finsupp.basisSingleOne : Module.Basis α R (α →₀ R)).baseChange (Polynomial R)

@[simp] theorem extendedBasis_apply (i : α) :
    extendedBasis R i = extendedSource R i := by
  simp [extendedBasis, Module.Basis.baseChange_apply, extendedSource]

noncomputable def sourceForm (κ : α → α → Polynomial R) :
    LinearMap.BilinForm (Polynomial R) (Polynomial R ⊗[R] (α →₀ R)) :=
  (extendedBasis R).constr (Polynomial R)
    (fun i => (extendedBasis R).constr (Polynomial R) (κ i))

@[simp] theorem sourceForm_apply (κ : α → α → Polynomial R) (i j : α) :
    sourceForm R κ (extendedSource R i) (extendedSource R j) = κ i j := by
  rw [← extendedBasis_apply, ← extendedBasis_apply]
  simp only [sourceForm, Module.Basis.constr_basis]

def crossGamma (γ : ℕ → ℕ → R) (i j : ℕ ⊕ ℕ) : R :=
  match i, j with
  | Sum.inl m, Sum.inr n => γ m n
  | Sum.inr n, Sum.inl m => -γ m n
  | _, _ => 0

def crossPole (i j : ℕ ⊕ ℕ) : ℕ :=
  Sum.elim id id i + Sum.elim id id j + 1

noncomputable def forwardPolynomial (γ : ℕ → ℕ → R) (i j : ℕ ⊕ ℕ) : Polynomial R :=
  match i, j with
  | Sum.inl m, Sum.inr n => Polynomial.monomial (m + n + 1) (γ m n)
  | _, _ => 0

noncomputable def commonForm (γ : ℕ → ℕ → R) :
    LinearMap.BilinForm (Polynomial R) (Polynomial R ⊗[R] ((ℕ ⊕ ℕ) →₀ R)) :=
  alternatingPart (Polynomial R) (sourceForm R (forwardPolynomial R γ))

theorem commonForm_isAlt (γ : ℕ → ℕ → R) : (commonForm R γ).IsAlt :=
  alternatingPart_isAlt (Polynomial R) _

theorem commonForm_apply (γ : ℕ → ℕ → R) (i j : ℕ ⊕ ℕ) :
    commonForm R γ (extendedSource R i) (extendedSource R j) =
      Polynomial.monomial (crossPole i j) (crossGamma R γ i j) := by
  simp only [commonForm, alternatingPart_apply, sourceForm_apply]
  cases i <;> cases j <;>
    simp [forwardPolynomial, crossGamma, crossPole, Nat.add_comm]

theorem prod_monomials {β : Type*} (P : List β) (p : β → ℕ) (c : β → R) :
    (P.map fun x => Polynomial.monomial (p x) (c x)).prod =
      Polynomial.monomial (P.map p).sum (P.map c).prod := by
  induction P with
  | nil => simp
  | cons x P ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih,
      Polynomial.monomial_mul_monomial]

theorem coefficient_monomial (γ : α → α → R) (p : α → α → ℕ) (t : Term α) :
    coefficient (Polynomial R) (fun i j => Polynomial.monomial (p i j) (γ i j)) t =
      Polynomial.monomial (t.pairs.map fun q => p q.1 q.2).sum (coefficient R γ t) := by
  have hs : (t.sign : Polynomial R) = Polynomial.C (t.sign : R) := by simp
  unfold coefficient
  rw [hs, prod_monomials, ← Polynomial.monomial_zero_left,
    Polynomial.monomial_mul_monomial, zero_add]

theorem selected_coefficient (s : R) (d : ℕ) (γ : α → α → R)
    (p : α → α → ℕ) (t : Term α) :
    poleSelector R s d
        (coefficient (Polynomial R) (fun i j => Polynomial.monomial (p i j) (γ i j)) t) =
      if (t.pairs.map fun q => p q.1 q.2).sum ≤ d then
        s ^ (d - (t.pairs.map fun q => p q.1 q.2).sum) * coefficient R γ t else 0 := by
  rw [coefficient_monomial, poleSelector_monomial]

theorem residueMap_exteriorEvaluate (s : R) (d : ℕ)
    (x : α → OneParticle R × OneParticle R) (κ : α → α → Polynomial R)
    (T : List (Term α)) :
    residueMap R s d x (exteriorEvaluate (Polynomial R) κ (extendedSource R) T) =
      (T.map fun t => poleSelector R s d (coefficient (Polynomial R) κ t) •
        Fock.normalList R (t.remaining.map x)).sum := by
  simp only [exteriorEvaluate, map_list_sum, List.map_map, Function.comp_def,
    residueMap_smul_word]

noncomputable def selectedEvaluate (s : R) (d : ℕ) (γ : α → α → R)
    (p : α → α → ℕ) (x : α → OneParticle R × OneParticle R) (T : List (Term α)) :
    Module.End R (Fock R) :=
  (T.map fun t =>
    (if (t.pairs.map fun q => p q.1 q.2).sum ≤ d then
      s ^ (d - (t.pairs.map fun q => p q.1 q.2).sum) * coefficient R γ t else 0) •
        Fock.normalList R (t.remaining.map x)).sum

theorem residueMap_selectedEvaluate (s : R) (d : ℕ)
    (x : α → OneParticle R × OneParticle R) (γ : α → α → R) (p : α → α → ℕ)
    (T : List (Term α)) :
    residueMap R s d x
        (exteriorEvaluate (Polynomial R)
          (fun i j => Polynomial.monomial (p i j) (γ i j)) (extendedSource R) T) =
      selectedEvaluate R s d γ p x T := by
  rw [residueMap_exteriorEvaluate]
  simp only [selectedEvaluate, selected_coefficient]

theorem selected_matching_exchange (s : R) (d : ℕ) (γ : ℕ → ℕ → R)
    (x : (ℕ ⊕ ℕ) → OneParticle R × OneParticle R) (A C : List ℕ) :
    selectedEvaluate R s d (crossGamma R γ) crossPole x
        (terms (A.map Sum.inl) (C.map Sum.inr)) =
      ((-1 : ℤˣ) ^ (A.length * C.length)) •
        selectedEvaluate R s d (crossGamma R γ) crossPole x
          (terms (C.map Sum.inr) (A.map Sum.inl)) := by
  have hAA : ∀ a ∈ A.map Sum.inl, ∀ b ∈ A.map Sum.inl,
      commonForm R γ (extendedSource R a) (extendedSource R b) = 0 := by
    intro a ha b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    rw [commonForm_apply]
    simp [crossGamma]
  have hCC : ∀ a ∈ C.map Sum.inr, ∀ b ∈ C.map Sum.inr,
      commonForm R γ (extendedSource R a) (extendedSource R b) = 0 := by
    intro a ha b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    rw [commonForm_apply]
    simp [crossGamma]
  have he := exterior_matching_exchange (Polynomial R) (commonForm R γ)
    (commonForm_isAlt R γ) (extendedSource R) (A.map Sum.inl) (C.map Sum.inr) hAA hCC
  have h := congrArg (residueMap R s d x) he
  simpa only [commonForm_apply, residueMap_selectedEvaluate, List.length_map,
    Units.smul_def, map_zsmul] using h

end Lemmata.FockCircuits.Matching
