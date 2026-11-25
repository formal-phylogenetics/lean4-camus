module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Fin

/-!
# `Fin 3`

Of three distinct elements of `Fin 3`, every element other than the third is one of the first two.
-/

@[expose] public section

namespace Fin

/-- Of three distinct elements of `Fin 3`, every element other than the third is one of the first
two. -/
theorem eq_or_eq_of_ne_of_three {s₁ s₂ s₃ s : Fin 3} (h₁₂ : s₁ ≠ s₂) (h₁₃ : s₁ ≠ s₃)
    (h₂₃ : s₂ ≠ s₃)
    (hs : s ≠ s₃) : s = s₁ ∨ s = s₂ := by
  revert s₁ s₂ s₃ s
  decide

end Fin
