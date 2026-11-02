module

/- Adapted from the pinned OpenAI/selanavot field-generic sources.
Namespace, imports, and selected scope changed; see Matrix/NOTICE.md.
Apache-2.0 license retained in Matrix/Apache-2.0.txt. -/

public import Lemmata.FockCircuits.Matrix.Entropy.TypeEntropy
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.MatrixMultiplication.ConditionalLabels

noncomputable section

open Foundation Filter
open scoped BigOperators Topology Classical

variable {A : Type*} [Fintype A]

theorem exists_rational_law_sequence (p : FiniteLaw A) :
    ∃ q : ℕ → RationalLaw A,
      ∀ a, Tendsto (fun n => (q n).toFiniteLaw.mass a) atTop (𝓝 (p.mass a)) := by
  have hexists (n : ℕ) := p.exists_rational_approximation
    (1 / ((n : ℝ) + 1)) (by positivity)
  choose q _support close using hexists
  refine ⟨q, fun a => ?_⟩
  have hdifference : Tendsto
      (fun n => (q n).toFiniteLaw.mass a - p.mass a) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    simpa only [Real.norm_eq_abs, RationalLaw.toFiniteLaw_mass] using (close n a).le
  simpa only [sub_add_cancel, zero_add] using hdifference.add_const (p.mass a)


end

end Lemmata.FockCircuits.Matrix.MatrixMultiplication.ConditionalLabels
