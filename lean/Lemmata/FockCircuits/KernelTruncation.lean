module

public import Lemmata.FockCircuits.KernelRectangle

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.KernelTruncation

noncomputable section

variable {R E M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def basisFilter (b : Module.Basis E R M) (p : E → Prop) : M →ₗ[R] M := by
  classical
  exact b.constr R fun e => if p e then b e else 0

@[simp] theorem basisFilter_basis (b : Module.Basis E R M) (p : E → Prop) [DecidablePred p] (e : E) :
    basisFilter b p (b e) = if p e then b e else 0 := by
  classical
  by_cases he : p e <;> simp [basisFilter, he]

theorem basisFilter_idempotent (b : Module.Basis E R M) (p : E → Prop) :
    (basisFilter b p).comp (basisFilter b p) = basisFilter b p := by
  classical
  apply b.ext
  intro e
  by_cases he : p e <;> simp [he]

theorem basisFilter_comp (b : Module.Basis E R M) (p q : E → Prop) :
    (basisFilter b p).comp (basisFilter b q) = basisFilter b (fun e => p e ∧ q e) := by
  classical
  apply b.ext
  intro e
  by_cases hp : p e <;> by_cases hq : q e <;> simp [hp, hq]

theorem basisFilter_commute (b : Module.Basis E R M) (p q : E → Prop) :
    (basisFilter b p).comp (basisFilter b q) = (basisFilter b q).comp (basisFilter b p) := by
  classical
  apply b.ext
  intro e
  by_cases hp : p e <;> by_cases hq : q e <;> simp [hp, hq]

theorem projection_eq_basisFilter {D : Type*} [Fintype D]
    (b : Module.Basis E R M) (index : D → E) (hinj : Function.Injective index) :
    KernelRectangle.projection b index = basisFilter b (fun e => ∃ d, index d = e) := by
  classical
  apply b.ext
  intro e
  by_cases he : ∃ d, index d = e
  · obtain ⟨d, rfl⟩ := he
    simp [KernelRectangle.projection_basis b index hinj]
  · have hz : KernelRectangle.projection b index (b e) = 0 := by
      apply KernelRectangle.projection_basis_outside
      intro d hd
      exact he ⟨d, hd.symm⟩
    simp only [hz, basisFilter_basis, ite_eq_right he]

theorem preserves_filter_of_basis (b : Module.Basis E R M) (p : E → Prop) (T : M →ₗ[R] M)
    (hT : ∀ e, p e → basisFilter b p (T (b e)) = T (b e)) :
    (basisFilter b p).comp (T.comp (basisFilter b p)) = T.comp (basisFilter b p) := by
  classical
  apply b.ext
  intro e
  by_cases he : p e
  · simpa only [LinearMap.comp_apply, basisFilter_basis, ite_eq_left he] using hT e he
  · simp [he]

theorem no_return_filter_of_basis (b : Module.Basis E R M) (p : E → Prop) (T : M →ₗ[R] M)
    (hT : ∀ e, ¬ p e → basisFilter b p (T (b e)) = 0) :
    (basisFilter b p).comp (T.comp (basisFilter b p)) = (basisFilter b p).comp T := by
  classical
  apply b.ext
  intro e
  by_cases he : p e
  · simp only [LinearMap.comp_apply, basisFilter_basis, ite_eq_left he]
  · simp only [LinearMap.comp_apply, basisFilter_basis, ite_eq_right he, map_zero, hT e he]

theorem preserves_filter_of_sparse (b : Module.Basis E R M) (p : E → Prop) (T : M →ₗ[R] M)
    (hT : ∀ e, ∃ f : E, ∃ c : R, T (b e) = b e + c • b f ∧ (p e → p f)) :
    (basisFilter b p).comp (T.comp (basisFilter b p)) = T.comp (basisFilter b p) := by
  classical
  apply preserves_filter_of_basis
  intro e he
  obtain ⟨f, c, hf, hpf⟩ := hT e
  simp only [hf, map_add, map_smul, basisFilter_basis, ite_eq_left he, ite_eq_left (hpf he)]

theorem no_return_filter_of_sparse (b : Module.Basis E R M) (p : E → Prop) (T : M →ₗ[R] M)
    (hT : ∀ e, ∃ f : E, ∃ c : R, T (b e) = b e + c • b f ∧ (p f → p e)) :
    (basisFilter b p).comp (T.comp (basisFilter b p)) = (basisFilter b p).comp T := by
  classical
  apply no_return_filter_of_basis
  intro e he
  obtain ⟨f, c, hf, hpf⟩ := hT e
  have hnot : ¬ p f := fun h => he (hpf h)
  simp only [hf, map_add, map_smul, basisFilter_basis, ite_eq_right he, ite_eq_right hnot,
    smul_zero, add_zero]

theorem preserves_comp (P S T : M →ₗ[R] M)
    (hS : P.comp (S.comp P) = S.comp P) (hT : P.comp (T.comp P) = T.comp P) :
    P.comp ((S.comp T).comp P) = (S.comp T).comp P := by
  ext v
  have hs := LinearMap.congr_fun hS (T (P v))
  have ht := LinearMap.congr_fun hT v
  simp only [LinearMap.comp_apply] at hs ht ⊢
  rwa [ht] at hs

theorem no_return_comp (P S T : M →ₗ[R] M)
    (hS : P.comp (S.comp P) = P.comp S) (hT : P.comp (T.comp P) = P.comp T) :
    P.comp ((S.comp T).comp P) = P.comp (S.comp T) := by
  ext v
  have hs₁ := LinearMap.congr_fun hS (T (P v))
  have hs₂ := LinearMap.congr_fun hS (T v)
  have ht := LinearMap.congr_fun hT v
  simp only [LinearMap.comp_apply] at hs₁ hs₂ ht ⊢
  calc
    P (S (T (P v))) = P (S (P (T (P v)))) := hs₁.symm
    _ = P (S (P (T v))) := by rw [ht]
    _ = P (S (T v)) := hs₂

theorem oriented_projection (P Q T : M →ₗ[R] M)
    (hQ : Q.comp Q = Q) (hcomm : P.comp Q = Q.comp P)
    (hsmall : P.comp (T.comp P) = P.comp T)
    (hlarge : Q.comp (T.comp Q) = T.comp Q) :
    (P.comp Q).comp (T.comp (P.comp Q)) = (P.comp Q).comp (T.comp Q) := by
  ext v
  have hqid := LinearMap.congr_fun hQ v
  have hcommv := LinearMap.congr_fun hcomm (Q v)
  have hlarge₁ := LinearMap.congr_fun hlarge (P (Q v))
  have hlarge₂ := LinearMap.congr_fun hlarge v
  have hsmallv := LinearMap.congr_fun hsmall (Q v)
  simp only [LinearMap.comp_apply] at hqid hcommv hlarge₁ hlarge₂ hsmallv ⊢
  rw [hqid] at hcommv
  rw [← hcommv] at hlarge₁
  calc
    P (Q (T (P (Q v)))) = P (T (P (Q v))) := congrArg P hlarge₁
    _ = P (T (Q v)) := hsmallv
    _ = P (Q (T (Q v))) := congrArg P hlarge₂.symm

end

end Lemmata.FockCircuits.KernelTruncation
