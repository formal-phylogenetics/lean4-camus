# General mathematics

Lemmas that say nothing about phylogenetics, filed by field as Mathlib files them and named as
Mathlib would name them, in Mathlib's namespaces, so that they can be contributed to Mathlib. They
import only Mathlib.

| File | Contents | Where it could go |
| --- | --- | --- |
| [`Data/List/Foldl.lean`](Data/List/Foldl.lean) | loops over lists: an invariant along a loop, and the value of a loop that sums, takes maxima, counts, prepends, or updates a function at a list of keys | `Mathlib/Data/List/Basic.lean`, `Mathlib/Algebra/BigOperators/Group/List/Basic.lean` |
| [`Data/List/Lattice.lean`](Data/List/Lattice.lean) | a loop that takes suprema in `WithBot ℕ` computes the supremum over the list | `Mathlib/Data/Finset/Lattice/Fold.lean` |
| [`Data/List/Basic.lean`](Data/List/Basic.lean) | the first and last elements of a list against `List.tail` and `List.dropLast`, the pairs of consecutive elements, `List.range` | `Mathlib/Data/List/Basic.lean`, `Mathlib/Data/List/Zip.lean`, `Mathlib/Data/List/Range.lean` |
| [`Data/Finset/Basic.lean`](Data/Finset/Basic.lean) | counting the elements of `insert a s` with a property; a set that contains one set and avoids its complement; a predicate that separates two nonempty sets; the pairs of a set with a given second coordinate | `Mathlib/Data/Finset/Card.lean`, `Mathlib/Data/Fintype/Basic.lean` |
| [`Data/Fin/Basic.lean`](Data/Fin/Basic.lean) | of three distinct elements of `Fin 3`, every element other than the third is one of the first two | `Mathlib/Data/Fin/Basic.lean` |
| [`Algebra/BigOperators/Fintype.lean`](Algebra/BigOperators/Fintype.lean) | regrouping a sum by the fibres of a map; summing out one coordinate of a function; the total probability of a Markov chain on a rooted tree | `Mathlib/Algebra/BigOperators/Fintype.lean` |
| [`Logic/Relation.lean`](Logic/Relation.lean) | the reflexive transitive closure of the relation of a finite set of pairs, when the pairs into a point are known, and after exchanging a pair | `Mathlib/Logic/Relation.lean` |
| [`Combinatorics/SimpleGraph/Paths.lean`](Combinatorics/SimpleGraph/Paths.lean) | a path through the members of a list whose consecutive members are adjacent; the edge by which a walk leaves a set | `Mathlib/Combinatorics/SimpleGraph/Paths.lean` |
| [`Combinatorics/SimpleGraph/Acyclic.lean`](Combinatorics/SimpleGraph/Acyclic.lean) | deleting an edge of a path of an acyclic graph disconnects its ends; an edge that separates two vertex-disjoint walks; a vertex outside a connected region stays connected to an end of a path through it | `Mathlib/Combinatorics/SimpleGraph/Acyclic.lean` |
| [`Combinatorics/SimpleGraph/Cycles.lean`](Combinatorics/SimpleGraph/Cycles.lean) | the neighbours of a vertex on a cycle; in a graph whose vertices have degree `2`, two cycles through a common vertex have the same edges | `Mathlib/Combinatorics/SimpleGraph/Connectivity/Subgraph.lean` |
| [`MeasureTheory/Measure/Tendsto.lean`](MeasureTheory/Measure/Tendsto.lean) | events that hold, almost surely, for all large indices have probability tending to `1` | `Mathlib/MeasureTheory/Measure/Real.lean` |

Some general facts stay where they are used, because they serve one step of the paper's
arguments and read as such: the arithmetic of the running time of backtracking
([`Complexity.budgetNetworks_arith`](../Complexity/BudgetBacktracking.lean#L1228)), and private lemmas inside proofs.

Before adding a lemma, search Mathlib and lean4-phylogenetics (`Phylogenetics/ForMathlib/`): a
lemma that a second repository of the collection needs moves up the tree, to the lowest node above
both (lean4-phylogenetics, docs/CONVENTIONS.md, Section 4).
