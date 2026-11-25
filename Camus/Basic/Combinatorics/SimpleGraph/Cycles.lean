module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Set.Card
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Cycles

A vertex of a cycle whose neighbours on the cycle are among two vertices is adjacent to both, and
one with at most one neighbour on it is not on it; in a graph whose vertices have degree `2`, two
cycles through a common vertex have the same edges.
-/

@[expose] public section

namespace SimpleGraph

/-- In a cycle, a vertex whose neighbours on the cycle are among `a ≠ b` is adjacent on the cycle
to both. -/
theorem Walk.IsCycle.adj_of_neighbors_subset {G : SimpleGraph ℕ} {u v a b : ℕ} {c : G.Walk u u}
    (hc : c.IsCycle)
    (hv : v ∈ c.support) (hab : a ≠ b)
    (hsub : ∀ w, c.toSubgraph.Adj v w → w = a ∨ w = b) :
    c.toSubgraph.Adj v a ∧ c.toSubgraph.Adj v b := by
  have h2 := hc.ncard_neighborSet_toSubgraph_eq_two hv
  have hs : c.toSubgraph.neighborSet v ⊆ {a, b} := fun w hw => hsub w hw
  have heq := Set.eq_of_subset_of_ncard_le hs (by rw [Set.ncard_pair hab, h2]) (Set.toFinite _)
  have ha : a ∈ c.toSubgraph.neighborSet v := heq ▸ Set.mem_insert a {b}
  have hb : b ∈ c.toSubgraph.neighborSet v := heq ▸ Set.mem_insert_of_mem a rfl
  exact ⟨ha, hb⟩

/-- A vertex with at most one neighbour on a cycle does not lie on it. -/
theorem Walk.IsCycle.not_mem_support_of_neighbors_subset {G : SimpleGraph ℕ} {u v a : ℕ}
    {c : G.Walk u u}
    (hc : c.IsCycle) (hsub : ∀ w, c.toSubgraph.Adj v w → w = a) : v ∉ c.support := by
  intro hv
  have h2 := hc.ncard_neighborSet_toSubgraph_eq_two hv
  have hs : c.toSubgraph.neighborSet v ⊆ {a} := fun w hw => hsub w hw
  have hle := Set.ncard_le_ncard hs (Set.finite_singleton a)
  rw [Set.ncard_singleton] at hle
  omega

private theorem isCycles_walk_support_subset {G : SimpleGraph ℕ} [G.LocallyFinite]
    (hG : G.IsCycles) {z : ℕ} (d : G.Walk z z) (hd : d.IsCycle)
    {u v : ℕ} (p : G.Walk u v) (hu : u ∈ d.support) : p.support ⊆ d.support := by
  induction p with
  | nil =>
    intro w hw
    exact List.mem_singleton.mp hw ▸ hu
  | cons hadj p ih =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl | htail
    · exact hu
    · have hdadj := (hd.adj_toSubgraph_iff_of_isCycles hG (d.mem_verts_toSubgraph.mpr hu) _).mpr
        hadj
      have hnext := SimpleGraph.Walk.mem_support_of_adj_toSubgraph hdadj.symm
      exact ih hnext htail

private theorem isCycles_walk_edges_subset {G : SimpleGraph ℕ} [G.LocallyFinite]
    (hG : G.IsCycles) {z : ℕ} (d : G.Walk z z) (hd : d.IsCycle)
    {u v : ℕ} (p : G.Walk u v) (hu : u ∈ d.support) : p.edges ⊆ d.edges := by
  intro r hr
  obtain ⟨a,b⟩ := r
  have hamem := p.fst_mem_support_of_mem_edges hr
  have hadj := p.adj_of_mem_edges hr
  have ha := isCycles_walk_support_subset hG d hd p hu hamem
  exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp
    ((hd.adj_toSubgraph_iff_of_isCycles hG (d.mem_verts_toSubgraph.mpr ha) _).mpr hadj)

/-- In a locally finite graph whose non-isolated vertices all have degree `2`, two cycles
through a common vertex have the same edges. -/
theorem IsCycles.edges_toFinset_eq {G : SimpleGraph ℕ} [G.LocallyFinite]
    (hG : G.IsCycles) {u v x : ℕ} (c : G.Walk u u) (d : G.Walk v v)
    (hc : c.IsCycle) (hd : d.IsCycle) (hxc : x ∈ c.support) (hxd : x ∈ d.support) :
    c.edges.toFinset = d.edges.toFinset := by
  have hcsub : c.edges ⊆ d.edges := by
    intro r hr
    apply isCycles_walk_edges_subset hG d hd (c.rotate x hxc) hxd
    exact (c.rotate_edges x hxc).mem_iff.mpr hr
  have hdsub : d.edges ⊆ c.edges := by
    intro r hr
    apply isCycles_walk_edges_subset hG c hc (d.rotate x hxd) hxc
    exact (d.rotate_edges x hxd).mem_iff.mpr hr
  apply Finset.Subset.antisymm
  · intro r hr
    exact List.mem_toFinset.mpr (hcsub (List.mem_toFinset.mp hr))
  · intro r hr
    exact List.mem_toFinset.mpr (hdsub (List.mem_toFinset.mp hr))

end SimpleGraph
