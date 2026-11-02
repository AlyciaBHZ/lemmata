module

public import Lemmata.FockCircuits.Matrix.ShapeAlgorithms

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix

open Filter BilinearScheme

noncomputable section

/-- Numerical cutoff comparisons turn the proved integer-shape bound into actual requested matrix DAGs. -/
theorem eventually_padded_shape_algorithms (F : Type*) [Field F] {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {δ : ℝ} (hδ : 0 < δ)
    (scale rows middle columns : ℕ → ℕ) (L : ℝ)
    (hscale : Tendsto scale atTop atTop)
    (hfit : ∀ᶠ N : ℕ in atTop,
      rows N ≤ scale N ^ a ∧ middle N ≤ scale N ^ b ∧ columns N ≤ scale N ^ c)
    (hrate : ∀ᶠ N : ℕ in atTop,
      (scale N : ℝ) ^ (shapeRate a b c + δ) ≤ (N : ℝ) ^ L) :
    ∀ᶠ N : ℕ in atTop,
      ∃ p : Lemmata.FockCircuits.OrderedMatrixAlgorithm F
          (Fin (rows N)) (Fin (middle N)) (Fin (columns N)),
        Nonempty (Construction p) ∧ (p.size : ℝ) ≤ (N : ℝ) ^ L := by
  have halg := hscale.eventually (eventually_shape_algorithms F ha hb hc hδ)
  filter_upwards [halg, hfit, hrate] with N hN hfitN hrateN
  obtain ⟨p, ⟨construction⟩, hcost⟩ := hN
  let eA : Fin (rows N) ↪ Fin (scale N ^ a) := Fin.castLEEmb hfitN.1
  let eB : Fin (middle N) ↪ Fin (scale N ^ b) := Fin.castLEEmb hfitN.2.1
  let eC : Fin (columns N) ↪ Fin (scale N ^ c) := Fin.castLEEmb hfitN.2.2
  let result := Lemmata.FockCircuits.Matrix.OrderedMatrixAlgorithm.pad p eA eB eC
  refine ⟨result, ⟨Construction.padding eA eB eC construction⟩, ?_⟩
  have hsize : result.size = p.size :=
    Lemmata.FockCircuits.Matrix.OrderedMatrixAlgorithm.size_pad p eA eB eC
  rw [hsize]
  exact hcost.trans hrateN

end

end Lemmata.FockCircuits.Matrix
