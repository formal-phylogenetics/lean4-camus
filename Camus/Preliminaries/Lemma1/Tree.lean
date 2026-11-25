module

public import Camus.Network.Completeness.Admissible
public import Camus.Basic.Combinatorics.SimpleGraph.Paths
public import Camus.Basic.Combinatorics.SimpleGraph.Acyclic

/-!
# Paths in a tree, for the uniqueness part of Lemma 1

Two facts about paths in an acyclic graph, applied in `Preliminaries/Lemma1/Unique.lean` to the
subdivided tree `T` inside a network built on `T`, in the proof of uniqueness in Lemma 1.

## Main results

* `SimpleGraph.IsAcyclic.exists_separating_edge`: if the path from `a` to `b` and the path from `c` to `d` have no
  common vertex, deleting one edge keeps `a, b` connected and `c, d` connected and disconnects `a`
  from `c`. If the two pairs of a quartet had disjoint paths in `T`, `T` would induce the quartet.
* `SimpleGraph.IsAcyclic.reachable_deleteEdges_of_not_mem`: deleting edges inside a connected region does not cut a vertex
  outside the region off from both ends of a path through it.
-/

@[expose] public section

namespace Camus

end Camus
