module

public import Lemmata.FockCircuits.KernelSupports

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.KernelStages

open KernelRectangle KernelTruncation

noncomputable section

variable {R D E M X : Type*} [CommRing R] [Fintype D]
  [AddCommGroup M] [Module R M]

def actualSteps : List (M →ₗ[R] M) → M →ₗ[R] M
  | [] => LinearMap.id
  | T :: rest => T.comp (actualSteps rest)

def maskedSteps (P : M →ₗ[R] M) : List (M →ₗ[R] M) → M →ₗ[R] M
  | [] => LinearMap.id
  | T :: rest => P.comp (T.comp (P.comp (maskedSteps P rest)))

theorem actualSteps_append (A B : List (M →ₗ[R] M)) :
    actualSteps (A ++ B) = (actualSteps A).comp (actualSteps B) := by
  induction A with
  | nil => rfl
  | cons T A ih => simp only [List.cons_append, actualSteps, ih, LinearMap.comp_assoc]

theorem maskedSteps_append (P : M →ₗ[R] M) (A B : List (M →ₗ[R] M)) :
    maskedSteps P (A ++ B) = (maskedSteps P A).comp (maskedSteps P B) := by
  induction A with
  | nil => rfl
  | cons T A ih => simp only [List.cons_append, maskedSteps, ih, LinearMap.comp_assoc]

theorem actualSteps_no_return (P : M →ₗ[R] M) (hP : P.comp P = P)
    (steps : List (M →ₗ[R] M))
    (hstage : ∀ T ∈ steps, P.comp (T.comp P) = P.comp T) :
    P.comp ((actualSteps steps).comp P) = P.comp (actualSteps steps) := by
  induction steps with
  | nil => simpa only [actualSteps, LinearMap.id_comp, LinearMap.comp_id] using hP
  | cons T rest ih =>
    exact no_return_comp P T (actualSteps rest) (hstage T (by simp))
      (ih (fun S hS => hstage S (by simp [hS])))

theorem exists_stage_circuit (b : Module.Basis E R M) (index : D → E)
    (hinj : Function.Injective index) (steps : List (M →ₗ[R] M))
    (cost : (M →ₗ[R] M) → ℕ)
    (hstage : ∀ T ∈ steps, ∀ bank : CircuitFamily R X D,
      ∃ p : CircuitFamily R X D, p.size = bank.size + cost T ∧
        Represents b index bank p ((projection b index).comp T))
    (bank : CircuitFamily R X D) :
    ∃ p : CircuitFamily R X D,
      p.size = bank.size + (steps.map cost).sum ∧
      Represents b index bank p (maskedSteps (projection b index) steps) := by
  induction steps generalizing bank with
  | nil => exact ⟨bank, by simp, Represents.identity b index hinj bank⟩
  | cons T rest ih =>
    obtain ⟨p, hp, hprep⟩ := ih (fun S hS => hstage S (by simp [hS])) bank
    obtain ⟨q, hq, hqrep⟩ := hstage T (by simp) p
    refine ⟨q, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons, hp, hq]
      omega
    · simpa only [maskedSteps, LinearMap.comp_assoc] using hprep.comp hqrep

theorem actualSteps_preserves (Q : M →ₗ[R] M) (hQ : Q.comp Q = Q)
    (steps : List (M →ₗ[R] M))
    (hstage : ∀ T ∈ steps, Q.comp (T.comp Q) = T.comp Q) :
    Q.comp ((actualSteps steps).comp Q) = (actualSteps steps).comp Q := by
  induction steps with
  | nil => simpa only [actualSteps, LinearMap.id_comp] using hQ
  | cons T rest ih =>
    exact preserves_comp Q T (actualSteps rest) (hstage T (by simp))
      (ih (fun S hS => hstage S (by simp [hS])))

theorem maskedSteps_no_return (P : M →ₗ[R] M) (hP : P.comp P = P)
    (steps : List (M →ₗ[R] M))
    (hstage : ∀ T ∈ steps, P.comp (T.comp P) = P.comp T) :
    (maskedSteps P steps).comp P = P.comp ((actualSteps steps).comp P) := by
  induction steps with
  | nil => simpa only [maskedSteps, actualSteps, LinearMap.id_comp] using hP.symm
  | cons T rest ih =>
    have hi := ih (fun S hS => hstage S (by simp [hS]))
    ext v
    have hiv := LinearMap.congr_fun hi v
    have hpid := LinearMap.congr_fun hP ((actualSteps rest) (P v))
    have ht := LinearMap.congr_fun (hstage T (by simp)) ((actualSteps rest) (P v))
    simp only [maskedSteps, actualSteps, LinearMap.comp_apply] at hiv hpid ht ⊢
    rw [hiv, hpid]
    exact ht

theorem maskedSteps_oriented (P Q : M →ₗ[R] M)
    (hP : P.comp P = P) (hQ : Q.comp Q = Q) (hcomm : P.comp Q = Q.comp P)
    (steps : List (M →ₗ[R] M))
    (hsmall : ∀ T ∈ steps, P.comp (T.comp P) = P.comp T)
    (hlarge : ∀ T ∈ steps, Q.comp (T.comp Q) = T.comp Q) :
    let W := P.comp Q
    (maskedSteps W steps).comp W = W.comp ((actualSteps steps).comp W) := by
  let W := P.comp Q
  have hW : W.comp W = W := by
    ext v
    have hcv := LinearMap.congr_fun hcomm (Q v)
    have hpv := LinearMap.congr_fun hP (Q v)
    have hqv := LinearMap.congr_fun hQ v
    simp only [LinearMap.comp_apply] at hcv hpv hqv
    change P (Q (P (Q v))) = P (Q v)
    rw [← hcv, hqv, hpv]
  have hQW (v : M) : Q (W v) = W v := by
    have hc := LinearMap.congr_fun hcomm (Q v)
    have hq := LinearMap.congr_fun hQ v
    simp only [LinearMap.comp_apply] at hc hq
    change Q (P (Q v)) = P (Q v)
    rw [← hc, hq]
  change (maskedSteps W steps).comp W = W.comp ((actualSteps steps).comp W)
  induction steps with
  | nil => simpa only [maskedSteps, actualSteps, LinearMap.id_comp] using hW.symm
  | cons T rest ih =>
    have hi := ih (fun S hS => hsmall S (by simp [hS]))
      (fun S hS => hlarge S (by simp [hS]))
    have hpres := actualSteps_preserves Q hQ rest (fun S hS => hlarge S (by simp [hS]))
    have ht := oriented_projection P Q T hQ hcomm (hsmall T (by simp)) (hlarge T (by simp))
    ext v
    have hiv := LinearMap.congr_fun hi v
    have hwv := LinearMap.congr_fun hW ((actualSteps rest) (W v))
    have hpresv := LinearMap.congr_fun hpres (W v)
    have htv := LinearMap.congr_fun ht ((actualSteps rest) (W v))
    simp only [LinearMap.comp_apply] at hiv hwv hpresv htv ⊢
    rw [hQW] at hpresv
    change W (T (W ((maskedSteps W rest) (W v)))) = W (T ((actualSteps rest) (W v)))
    rw [hiv, hwv]
    change W (T (W ((actualSteps rest) (W v)))) = W (T (Q ((actualSteps rest) (W v)))) at htv
    rw [hpresv] at htv
    exact htv

theorem coefficientMatrix_of_restriction (b : Module.Basis E R M) (index : D → E)
    (hinj : Function.Injective index) (S T : M →ₗ[R] M)
    (h : S.comp (projection b index) = (projection b index).comp (T.comp (projection b index))) :
    coefficientMatrix b index S = coefficientMatrix b index T := by
  funext i j
  have heq := congrArg (fun v => b.repr v (index i))
    (LinearMap.congr_fun h (b (index j)))
  simpa only [LinearMap.comp_apply, projection_basis b index hinj,
    repr_projection b index hinj, coefficientMatrix] using heq

theorem maskedSteps_two_phases (P Q : M →ₗ[R] M)
    (hP : P.comp P = P) (hQ : Q.comp Q = Q) (hcomm : P.comp Q = Q.comp P)
    (A B : List (M →ₗ[R] M))
    (hraise : ∀ T ∈ A, (P.comp Q).comp (T.comp (P.comp Q)) = (P.comp Q).comp T)
    (hsmall : ∀ T ∈ B, P.comp (T.comp P) = P.comp T)
    (hlarge : ∀ T ∈ B, Q.comp (T.comp Q) = T.comp Q) :
    let W := P.comp Q
    (maskedSteps W (A ++ B)).comp W = W.comp ((actualSteps (A ++ B)).comp W) := by
  let W := P.comp Q
  have hW : W.comp W = W := by
    ext v
    have hcv := LinearMap.congr_fun hcomm (Q v)
    have hpv := LinearMap.congr_fun hP (Q v)
    have hqv := LinearMap.congr_fun hQ v
    simp only [LinearMap.comp_apply] at hcv hpv hqv
    change P (Q (P (Q v))) = P (Q v)
    rw [← hcv, hqv, hpv]
  have hA := maskedSteps_no_return W hW A hraise
  have hB := maskedSteps_oriented P Q hP hQ hcomm B hsmall hlarge
  have hAr := actualSteps_no_return W hW A hraise
  change (maskedSteps W (A ++ B)).comp W = W.comp ((actualSteps (A ++ B)).comp W)
  rw [maskedSteps_append, actualSteps_append]
  ext v
  have ha := LinearMap.congr_fun hA ((actualSteps B) (W v))
  have hb := LinearMap.congr_fun hB v
  have har := LinearMap.congr_fun hAr ((actualSteps B) (W v))
  simp only [LinearMap.comp_apply] at ha hb har ⊢
  change (maskedSteps W B) (W v) = W ((actualSteps B) (W v)) at hb
  rw [hb, ha]
  exact har

theorem represents_of_coefficientMatrix_eq {b : Module.Basis E R M} {index : D → E}
    {bank p : CircuitFamily R X D} {S T : M →ₗ[R] M}
    (hp : Represents b index bank p S)
    (heq : coefficientMatrix b index S = coefficientMatrix b index T) :
    Represents b index bank p T := by
  unfold Represents at hp ⊢
  simpa only [heq] using hp

end

end Lemmata.FockCircuits.KernelStages
