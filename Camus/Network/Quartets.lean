module

public import Camus.Defs
public import Mathlib.Data.Fintype.Prod

/-!
# Quartets as tuples, and the quartets on a set of taxa

A quartet is determined by its four labels and its split (`Complexity.quartetKey_injective`), so
the quartets whose taxa lie in a finite set `X` form a finite set (`Quartet.onTaxa`). Section 2.3
uses the first fact to bound the number of distinct quartets of `Q`
(`Complexity.observedQuartets_bound`), and the site model of Warnow, Tabatabaee and Evans
(`External.WarnowTabatabaeeEvans.SiteHistory.quartets`) the second.
-/

@[expose] public section

namespace Camus

namespace Complexity

/-- A quartet as the tuple of its four labels and its split index. -/
def quartetKey (q : Quartet) : ℕ × (ℕ × (ℕ × (ℕ × Fin 3))) :=
  (q.a,q.b,q.c,q.d,q.split)

/-- A quartet is determined by its four labels and its split. -/
theorem quartetKey_injective : Function.Injective quartetKey := by
  intro q r h
  cases q
  cases r
  simp only [quartetKey,Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl,rfl,rfl⟩
  rfl

end Complexity

namespace Quartet

/-- The quartets whose four taxa lie in `X`. -/
noncomputable def onTaxa (X : Finset ℕ) : Finset Quartet :=
  (X ×ˢ (X ×ˢ (X ×ˢ (X ×ˢ (Finset.univ : Finset (Fin 3)))))).preimage Complexity.quartetKey
    Complexity.quartetKey_injective.injOn

/-- A quartet is in `onTaxa X` if and only if its four taxa lie in `X`. -/
theorem mem_onTaxa {X : Finset ℕ} {q : Quartet} : q ∈ onTaxa X ↔ q.taxa ⊆ X := by
  simp only [onTaxa, Finset.mem_preimage, Complexity.quartetKey, Finset.mem_product,
    Finset.mem_univ, and_true, taxa, Finset.insert_subset_iff, Finset.singleton_subset_iff]

end Quartet

end Camus
