module

public import Camus.Tree.Geometry

/-!
# Lemma 2: one non-tree edge per target

The paper's Lemma 2 in the form used by the dynamic program: for a network given by its family of
added edges, at most one added edge has a given target (`EdgeAbove.target_unique`). The form for
an arbitrary level-1 network built on `T`, `lemma2`, is derived from it.

## Proof (the paper's)

If two distinct added edges had the same target v, each of their cycles would contain v
(`EdgeAbove.target_mem_footprint`), so the two cycles would share a vertex, contradicting
level-1.
-/

@[expose] public section

namespace Camus

namespace EdgeAbove

/-- **Lemma 2** (`mthst4`), for a network given by its family of added edges. Let `E` be a
cycle-separated family of pairs (`EdgeAbove.CycleSeparated`): the cycles γ(u, w) of distinct pairs
of `E` are vertex-disjoint, i.e. `Realization.graph t E` is level-1. If two pairs of `E` have the
same target, they are equal: at most one added edge has a given target.

The proof is the paper's: the common target lies on both cycles
(`EdgeAbove.target_mem_footprint`), so the cycles of two distinct pairs would share it. -/
theorem target_unique (t : PhyloTree) (E : Finset (Address × Address))
    (hE : CycleSeparated t E) {e f : Address × Address}
    (he : e ∈ E) (hf : f ∈ E) (ht : target e = target f) : e = f := by
  -- if e ≠ f, the cycles γ(e) and γ(f) are disjoint, yet both contain the common target
  by_contra hne
  have ha := (Finset.mem_filter.mp (hE.1 he)).2
  have hb := (Finset.mem_filter.mp (hE.1 hf)).2
  have hdis := hE.2 he hf hne
  have hxe := target_mem_footprint t e ha
  have hxf := target_mem_footprint t f hb
  rw [← ht] at hxf
  exact Finset.disjoint_left.mp hdis hxe hxf

end EdgeAbove
end Camus
