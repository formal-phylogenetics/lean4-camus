module

public import Allman2011.FourTaxa.Proposition3
public import Allman2011.Rootings.Statements

/-!
# Allman, Degnan and Rhodes (2011): unrooted gene trees on four taxa

The facts about the multispecies coalescent on four taxa that Section 3.3's description of the
MSC rests on (`Camus.Coalescent.msc_pattern`), in the terms of E. S. Allman, J. H. Degnan and
J. A. Rhodes, *Identifying the rooted species tree from the distribution of unrooted gene trees
under the coalescent*, J. Math. Biol. 62 (2011) 833–862, Section 4.1: species trees
`Phylogenetics.SpeciesTree X` with positive edge lengths, one lineage per taxon, and the
distribution `σ.unrootedDist id` of the unrooted gene tree, a tree being given by the sides of its
splits. Each is proved by the theorem of the same name of lean4-allman2011, the formalization of
that paper, which follows its argument.

* `four_unrootedDist_of_mem`, `four_unrootedDist_of_ne_of_isBinary`: on four taxa, the quartet tree
  of a binary species tree has probability `1 - (2/3) e^{-t}`, and each of the two others
  `(1/3) e^{-t}`, where `t` is the length of the internal edge.
* `unrootedDist_eq_zero_four`: only the three quartet trees have positive probability.
* `f1_exists_split_of_isBinary`, `f1_mem_unroot_iff_of_split`: a binary species tree on four taxa
  has exactly one nontrivial split.
* `four_unrootedLength_pos`: the internal edge has positive length.
-/

@[expose] public section

namespace External.AllmanDegnanRhodes2011

open Phylogenetics Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Section 4.1: on four taxa, the quartet tree with the split `A | Aᶜ` of a binary species tree
has probability `1 - (2/3) e^{-t}`, where `t` is the length of the internal edge. Proved by
`Allman2011.four_unrootedDist_of_mem`. -/
theorem four_unrootedDist_of_mem (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    (hσ : σ.IsBinary) {A : Finset X} (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) :
    σ.unrootedDist id (treeOfClusters {A}) = 1 - 2 / 3 * exp (-σ.unrootedLength A) :=
  Allman2011.four_unrootedDist_of_mem hX σ hσ hA hA2

/-- Section 4.1: on four taxa, each of the two quartet trees other than the one with the split
`A | Aᶜ` of a binary species tree has probability `(1/3) e^{-t}`, where `t` is the length of the
internal edge. Proved by `Allman2011.four_unrootedDist_of_ne_of_isBinary`. -/
theorem four_unrootedDist_of_ne_of_isBinary (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    (hσ : σ.IsBinary) {A B : Finset X} (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2)
    (hB2 : #B = 2) (hBA : B ≠ A) (hBA' : B ≠ Aᶜ) :
    σ.unrootedDist id (treeOfClusters {B}) = 1 / 3 * exp (-σ.unrootedLength A) :=
  Allman2011.four_unrootedDist_of_ne_of_isBinary hX σ hσ hA hA2 hB2 hBA hBA'

/-- On four taxa, only the three quartet trees have positive probability. Proved by
`Allman2011.unrootedDist_eq_zero_four`. -/
theorem unrootedDist_eq_zero_four (τ : SpeciesTree (Fin 4)) (T : Finset (Finset (Fin 4)))
    (hT : T ≠ treeOfClusters {{0, 1}} ∧ T ≠ treeOfClusters {{0, 2}} ∧
      T ≠ treeOfClusters {{0, 3}}) :
    τ.unrootedDist id T = 0 :=
  Allman2011.unrootedDist_eq_zero_four τ T hT

/-- A binary species tree on four taxa has a nontrivial split `A | Aᶜ` with `#A = 2`. Proved by
`Allman2011.f1_exists_split_of_isBinary`. -/
theorem f1_exists_split_of_isBinary (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    (hσ : σ.IsBinary) : ∃ A ∈ unroot σ.clusters, #A = 2 :=
  Allman2011.f1_exists_split_of_isBinary hX σ hσ

/-- On four taxa, a species tree with the nontrivial split `A | Aᶜ` has no other: the sides of its
splits are the single taxa, their complements, `A` and `Aᶜ`. Proved by
`Allman2011.f1_mem_unroot_iff_of_split`. -/
theorem f1_mem_unroot_iff_of_split (hX : Fintype.card X = 4) (σ : SpeciesTree X)
    {A : Finset X} (hA : A ∈ unroot σ.clusters) (hA2 : #A = 2) (B : Finset X) :
    B ∈ unroot σ.clusters ↔ #B = 1 ∨ #B = 3 ∨ B = A ∨ B = Aᶜ :=
  Allman2011.f1_mem_unroot_iff_of_split hX σ hA hA2 B

/-- The edge of the unrooted species tree that induces a split has positive length. Proved by
`Allman2011.four_unrootedLength_pos`. -/
theorem four_unrootedLength_pos (σ : SpeciesTree X) {A : Finset X}
    (hA : A ∈ unroot σ.clusters) : 0 < σ.unrootedLength A :=
  Allman2011.four_unrootedLength_pos σ hA

end External.AllmanDegnanRhodes2011
