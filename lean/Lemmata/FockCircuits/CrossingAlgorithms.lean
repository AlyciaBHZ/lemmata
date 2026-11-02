module

public import Lemmata.FockCircuits.CrossingCircuit
public import Lemmata.FockCircuits.Matrix.ScaleAdapter
public import Lemmata.FockCircuits.Matrix.CutoffShapes

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Lemmata.FockCircuits.CrossingAlgorithms

open Filter Exponent
open scoped Topology

noncomputable section

/-- The six orders needed by the quartic products and the degree-five contexts. -/
structure AllOrders (R A B C : Type*) [CommSemiring R]
    [Fintype A] [Fintype B] [Fintype C] where
  abc : OrderedMatrixAlgorithm R A B C
  acb : OrderedMatrixAlgorithm R A C B
  bac : OrderedMatrixAlgorithm R B A C
  bca : OrderedMatrixAlgorithm R B C A
  cab : OrderedMatrixAlgorithm R C A B
  cba : OrderedMatrixAlgorithm R C B A

namespace AllOrders

variable {R A B C : Type*} [CommSemiring R] [Fintype A] [Fintype B] [Fintype C]

def Bounded (p : AllOrders R A B C) (t : ℝ) : Prop :=
  (p.abc.size : ℝ) ≤ t ∧ (p.acb.size : ℝ) ≤ t ∧
    (p.bac.size : ℝ) ≤ t ∧ (p.bca.size : ℝ) ≤ t ∧
    (p.cab.size : ℝ) ≤ t ∧ (p.cba.size : ℝ) ≤ t

def reindex {A' B' C' : Type*} [Fintype A'] [Fintype B'] [Fintype C']
    (p : AllOrders R A B C) (a : A' ≃ A) (b : B' ≃ B) (c : C' ≃ C) :
    AllOrders R A' B' C' where
  abc := Matrix.OrderedMatrixAlgorithm.pad p.abc a.toEmbedding b.toEmbedding c.toEmbedding
  acb := Matrix.OrderedMatrixAlgorithm.pad p.acb a.toEmbedding c.toEmbedding b.toEmbedding
  bac := Matrix.OrderedMatrixAlgorithm.pad p.bac b.toEmbedding a.toEmbedding c.toEmbedding
  bca := Matrix.OrderedMatrixAlgorithm.pad p.bca b.toEmbedding c.toEmbedding a.toEmbedding
  cab := Matrix.OrderedMatrixAlgorithm.pad p.cab c.toEmbedding a.toEmbedding b.toEmbedding
  cba := Matrix.OrderedMatrixAlgorithm.pad p.cba c.toEmbedding b.toEmbedding a.toEmbedding

theorem bounded_reindex {A' B' C' : Type*} [Fintype A'] [Fintype B'] [Fintype C']
    (p : AllOrders R A B C) (a : A' ≃ A) (b : B' ≃ B) (c : C' ≃ C) {t : ℝ}
    (hp : p.Bounded t) : (p.reindex a b c).Bounded t := by
  simpa only [Bounded, reindex, Matrix.OrderedMatrixAlgorithm.size_pad] using hp

end AllOrders

theorem eventually_all_orders (R : Type*) [Field R] {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {eta : ℝ} (heta : 0 < eta)
    (scale rows middle columns : ℕ → ℕ) (L : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hfit : ∀ᶠ n : ℕ in atTop,
      rows n ≤ scale n ^ a ∧ middle n ≤ scale n ^ b ∧ columns n ≤ scale n ^ c)
    (hrate : ∀ᶠ n : ℕ in atTop,
      (scale n : ℝ) ^ (Matrix.shapeRate a b c + eta) ≤ (n : ℝ) ^ L) :
    ∀ᶠ n : ℕ in atTop,
      ∃ p : AllOrders R (Fin (rows n)) (Fin (middle n)) (Fin (columns n)),
        p.Bounded ((n : ℝ) ^ L) := by
  have hqACB : Matrix.shapeRate a c b = Matrix.shapeRate a b c := by
    unfold Matrix.shapeRate
    congr 1 <;> ring
  have hqBAC : Matrix.shapeRate b a c = Matrix.shapeRate a b c := by
    unfold Matrix.shapeRate
    congr 1 <;> ring
  have hqBCA : Matrix.shapeRate b c a = Matrix.shapeRate a b c := by
    unfold Matrix.shapeRate
    congr 1 <;> ring
  have hqCAB : Matrix.shapeRate c a b = Matrix.shapeRate a b c := by
    unfold Matrix.shapeRate
    congr 1 <;> ring
  have hqCBA : Matrix.shapeRate c b a = Matrix.shapeRate a b c := by
    unfold Matrix.shapeRate
    congr 1 <;> ring
  have hABC := Matrix.eventually_padded_shape_algorithms R ha hb hc heta
    scale rows middle columns L hscale hfit hrate
  have hACB := Matrix.eventually_padded_shape_algorithms R ha hc hb heta
    scale rows columns middle L hscale
    (hfit.mono fun _ h => ⟨h.1, h.2.2, h.2.1⟩) (by simpa only [hqACB] using hrate)
  have hBAC := Matrix.eventually_padded_shape_algorithms R hb ha hc heta
    scale middle rows columns L hscale
    (hfit.mono fun _ h => ⟨h.2.1, h.1, h.2.2⟩) (by simpa only [hqBAC] using hrate)
  have hBCA := Matrix.eventually_padded_shape_algorithms R hb hc ha heta
    scale middle columns rows L hscale
    (hfit.mono fun _ h => ⟨h.2.1, h.2.2, h.1⟩) (by simpa only [hqBCA] using hrate)
  have hCAB := Matrix.eventually_padded_shape_algorithms R hc ha hb heta
    scale columns rows middle L hscale
    (hfit.mono fun _ h => ⟨h.2.2, h.1, h.2.1⟩) (by simpa only [hqCAB] using hrate)
  have hCBA := Matrix.eventually_padded_shape_algorithms R hc hb ha heta
    scale columns middle rows L hscale
    (hfit.mono fun _ h => ⟨h.2.2, h.2.1, h.1⟩) (by simpa only [hqCBA] using hrate)
  filter_upwards [hABC, hACB, hBAC, hBCA, hCAB, hCBA]
    with n hABCn hACBn hBACn hBCAn hCABn hCBAn
  obtain ⟨pABC, _, hABCn⟩ := hABCn
  obtain ⟨pACB, _, hACBn⟩ := hACBn
  obtain ⟨pBAC, _, hBACn⟩ := hBACn
  obtain ⟨pBCA, _, hBCAn⟩ := hBCAn
  obtain ⟨pCAB, _, hCABn⟩ := hCABn
  obtain ⟨pCBA, _, hCBAn⟩ := hCBAn
  exact ⟨⟨pABC, pACB, pBAC, pBCA, pCAB, pCBA⟩,
    hABCn, hACBn, hBACn, hBCAn, hCABn, hCBAn⟩

/-- The same rectangular rate pays for each matrix's input and output slots. -/
theorem eventually_slot_bounds {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {eta : ℝ} (heta : 0 < eta) (scale rows middle columns : ℕ → ℕ) (L : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hfit : ∀ᶠ n : ℕ in atTop,
      rows n ≤ scale n ^ a ∧ middle n ≤ scale n ^ b ∧ columns n ≤ scale n ^ c)
    (hrate : ∀ᶠ n : ℕ in atTop,
      (scale n : ℝ) ^ (Matrix.shapeRate a b c + eta) ≤ (n : ℝ) ^ L) :
    ∀ᶠ n : ℕ in atTop,
      ((rows n * middle n : ℕ) : ℝ) ≤ (n : ℝ) ^ L ∧
        ((rows n * columns n : ℕ) : ℝ) ≤ (n : ℝ) ^ L ∧
        ((middle n * columns n : ℕ) : ℝ) ≤ (n : ℝ) ^ L := by
  have hslots := realRectangularRate_slot_bounds (a : ℝ) (b : ℝ) (c : ℝ)
    (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hc)
  change (a : ℝ) + b ≤ Matrix.shapeRate a b c ∧
    (a : ℝ) + c ≤ Matrix.shapeRate a b c ∧
    (b : ℝ) + c ≤ Matrix.shapeRate a b c at hslots
  filter_upwards [hscale.eventually_ge_atTop 1, hfit, hrate] with n hscaleN hfitN hrateN
  have hscaleR : (1 : ℝ) ≤ scale n := by exact_mod_cast hscaleN
  have pair (u v d e : ℕ) (hu : u ≤ scale n ^ d) (hv : v ≤ scale n ^ e)
      (hde : (d : ℝ) + e ≤ Matrix.shapeRate a b c) :
      ((u * v : ℕ) : ℝ) ≤ (n : ℝ) ^ L := by
    have hnat : u * v ≤ scale n ^ (d + e) := by
      rw [pow_add]
      exact Nat.mul_le_mul hu hv
    have hexponent : (d : ℝ) + e ≤ Matrix.shapeRate a b c + eta := by linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le hscaleR hexponent
    have hcast : ((scale n ^ (d + e) : ℕ) : ℝ) ≤
        (scale n : ℝ) ^ (Matrix.shapeRate a b c + eta) := by
      rw [Nat.cast_pow]
      have heq : (scale n : ℝ) ^ (d + e) = (scale n : ℝ) ^ ((d : ℝ) + e) := by
        rw [← Nat.cast_add, Real.rpow_natCast]
      rw [heq]
      exact hpow
    exact (Nat.cast_le.mpr hnat).trans (hcast.trans hrateN)
  exact ⟨pair _ _ a b hfitN.1 hfitN.2.1 hslots.1,
    pair _ _ a c hfitN.1 hfitN.2.2 hslots.2.1,
    pair _ _ b c hfitN.2.1 hfitN.2.2 hslots.2.2⟩

/-- Actual all-field circuits for the common stacked cutoff shape, with the optimized exponent. -/
theorem eventually_exterior_algorithms (R : Type*) [Field R] (eps : ℝ) (heps : 0 < eps) :
    ∃ padding : ℝ, 0 < padding ∧
      let H := ceilLogEnergy countingConstant (1 + padding)
      let E := floorLogEnergy countingConstant optimalInput
      (∀ᶠ n : ℕ in atTop, 0 < H n ∧ 2 * H n * n ≤ stateCount (H n) - 1 ∧
        ∃ p : AllOrders R (Fin (2 * H n) × ↥(fullCutoff (H n + E n)))
            ↥(fullCutoff (E n)) (Fin (batchCount n (stateCount (E n)))),
          p.Bounded ((n : ℝ) ^ (gamma + eps)) ∧
          (((2 * H n * stateCount (H n + E n)) * stateCount (E n) : ℕ) : ℝ) ≤
            (n : ℝ) ^ (gamma + eps) ∧
          (((2 * H n * stateCount (H n + E n)) * batchCount n (stateCount (E n)) : ℕ) : ℝ) ≤
            (n : ℝ) ^ (gamma + eps) ∧
          ((stateCount (E n) * batchCount n (stateCount (E n)) : ℕ) : ℝ) ≤
            (n : ℝ) ^ (gamma + eps)) ∧
      Tendsto (fun n : ℕ => Real.log (((H n + E n + 1 : ℕ) : ℝ) ^ 3) / Real.log (n : ℝ))
        atTop (𝓝 0) := by
  obtain ⟨padding, d, a, b, c, eta, hpadding, hd, ha, hb, hc, heta, hparameters, hoverhead⟩ :=
    Matrix.exists_exterior_shape_parameters eps heps
  let H := ceilLogEnergy countingConstant (1 + padding)
  let E := floorLogEnergy countingConstant optimalInput
  let rows := fun n => 2 * H n * stateCount (H n + E n)
  let middle := fun n => stateCount (E n)
  let columns := fun n => batchCount n (stateCount (E n))
  have hfit : ∀ᶠ n : ℕ in atTop,
      rows n ≤ Matrix.rootScale d n ^ a ∧ middle n ≤ Matrix.rootScale d n ^ b ∧
        columns n ≤ Matrix.rootScale d n ^ c :=
    hparameters.mono fun _ h => ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  have hrate : ∀ᶠ n : ℕ in atTop,
      (Matrix.rootScale d n : ℝ) ^ (Matrix.shapeRate a b c + eta) ≤ (n : ℝ) ^ (gamma + eps) :=
    hparameters.mono fun _ h => h.2.2.2.2.2.2
  have halg := eventually_all_orders R ha hb hc heta (Matrix.rootScale d) rows middle columns
    (gamma + eps) (Matrix.rootScale_tendsto d hd) hfit hrate
  have hslots := eventually_slot_bounds ha hb hc heta (Matrix.rootScale d) rows middle columns
    (gamma + eps) (Matrix.rootScale_tendsto d hd) hfit hrate
  refine ⟨padding, hpadding, ?_, hoverhead⟩
  filter_upwards [hparameters, halg, hslots] with n hparametersN halgN hslotsN
  obtain ⟨p, hp⟩ := halgN
  have hrows : Fintype.card (Fin (2 * H n) × ↥(fullCutoff (H n + E n))) = rows n := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, stateCount, rows]
  have hmiddle : Fintype.card ↥(fullCutoff (E n)) = middle n := by
    simp only [Fintype.card_coe, stateCount, middle]
  let erow := Fintype.equivFinOfCardEq hrows
  let emiddle := Fintype.equivFinOfCardEq hmiddle
  refine ⟨hparametersN.1, hparametersN.2.1,
    p.reindex erow emiddle (Equiv.refl _), p.bounded_reindex erow emiddle (Equiv.refl _) hp, ?_⟩
  exact hslotsN

end

end Lemmata.FockCircuits.CrossingAlgorithms
