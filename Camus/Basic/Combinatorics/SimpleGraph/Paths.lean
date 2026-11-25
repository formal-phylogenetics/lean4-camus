module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# Paths through a list or out of a set

A path through the members of a list whose consecutive members are adjacent, and the edge by which
a walk leaves a set.
-/

@[expose] public section

namespace SimpleGraph

/-- If consecutive members of the list `l` are adjacent in `G`, any two members of `l` are joined
by a path of `G` through members of `l`. -/
theorem exists_isPath_support_subset_of_isChain {G : SimpleGraph ℕ} {l : List ℕ}
    (hchain : l.IsChain G.Adj) {u v : ℕ} (hu : u ∈ l) (hv : v ∈ l) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.support ⊆ l := by
  classical
  have hne : l ≠ [] := List.ne_nil_of_mem hu
  let w := SimpleGraph.Walk.ofSupport l hne hchain
  have hwu : u ∈ w.support := by simpa only [w, SimpleGraph.Walk.support_ofSupport] using hu
  have hwv : v ∈ w.support := by simpa only [w, SimpleGraph.Walk.support_ofSupport] using hv
  let a := w.takeUntil u hwu
  let b := w.takeUntil v hwv
  let z := a.reverse.append b
  refine ⟨z.toPath, z.toPath.isPath, ?_⟩
  intro x hx
  have hxz := z.support_toPath_subset_support hx
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hxz with ha | hb
  · have hxa : x ∈ a.support := by
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using ha
    have hxw := w.support_takeUntil_subset_support hwu hxa
    simpa only [w, SimpleGraph.Walk.support_ofSupport] using hxw
  · have hxw := w.support_takeUntil_subset_support hwv hb
    simpa only [w, SimpleGraph.Walk.support_ofSupport] using hxw

/-- A walk from a vertex in `C` to a vertex outside `C` uses an edge from `C` to its complement. -/
theorem Walk.exists_boundary_edge {G : SimpleGraph ℕ} (C : Set ℕ) {a b : ℕ}
    (p : G.Walk a b) (ha : a ∈ C) (hb : b ∉ C) :
    ∃ u v, s(u,v) ∈ p.edges ∧ u ∈ C ∧ v ∉ C := by
  induction p with
  | nil => exact False.elim (hb ha)
  | @cons a v b hav p ih =>
    by_cases hv : v ∈ C
    · obtain ⟨x,y,hxy,hx,hy⟩ := ih hv hb
      exact ⟨x,y,List.mem_cons_of_mem _ hxy,hx,hy⟩
    · exact ⟨a,v,List.mem_cons_self,ha,hv⟩

end SimpleGraph
