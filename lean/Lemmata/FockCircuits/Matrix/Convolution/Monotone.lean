module

public import Lemmata.FockCircuits.Matrix.Convolution.Basic
public import Lemmata.FockCircuits.Matrix.Character.Basic

@[expose] public section

set_option autoImplicit false

namespace Lemmata.FockCircuits.Matrix.Spectral.Character

open Foundation

variable {K : Type*} [Field K]

/-- Enlarging either input interval preserves every existing convolution coefficient. -/
theorem value_convolution_mono (χ : Character K) {a b a' b' : ℕ}
    (ha : a ≤ a') (hb : b ≤ b') :
    χ.value (convolution a b) ≤ χ.value (convolution a' b') := by
  have hout : a + b - 1 ≤ a' + b' - 1 := Nat.sub_le_sub_right (Nat.add_le_add ha hb) 1
  have heq : Tensor.pullback (Fin.castLE ha) (Fin.castLE hb) (Fin.castLE hout)
      (convolution (K := K) a' b') = convolution (K := K) a b := by
    funext i j k
    rfl
  rw [← heq]
  exact χ.value_pullback_le _ _ _ _

end Lemmata.FockCircuits.Matrix.Spectral.Character
