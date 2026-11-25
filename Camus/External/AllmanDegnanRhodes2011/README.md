# Allman, Degnan, Rhodes 2011

**Source.** E. S. Allman, J. H. Degnan, J. A. Rhodes, *Identifying the rooted species tree from
the distribution of unrooted gene trees under the coalescent*, J. Math. Biol. 62 (2011) 833–862,
[doi:10.1007/s00285-010-0355-7](https://doi.org/10.1007/s00285-010-0355-7), Section 4.1.

**How the paper uses it.** Section 3.3 motivates Algorithm 1 by "the multi-species coalescent
(MSC) model (Takahata 1989) under which, for every four species, the most probable quartet tree
matches the species tree and the other two quartet trees have the same lower probability". The
formalization proves this description ([`Coalescent.msc_pattern`](../../Pipelines/Coalescent/Quartets.lean#L463)) from the distributions of the unrooted
gene trees on four taxa that Allman, Degnan and Rhodes compute.

**The Lean statements.** Module [`Camus.External.AllmanDegnanRhodes2011.FourTaxa`](FourTaxa.lean), namespace
`External.AllmanDegnanRhodes2011`, in the source's terms: species trees `Phylogenetics.SpeciesTree X`
with positive edge lengths, the multispecies coalescent with one lineage per taxon, and the
distribution `σ.unrootedDist id` of the unrooted gene tree, a tree given by the sides of its splits.

| Declaration | Statement |
| --- | --- |
| [`External.AllmanDegnanRhodes2011.four_unrootedDist_of_mem`](FourTaxa.lean#L38) | on four taxa, the quartet tree with the split `A \| Aᶜ` of a binary species tree has probability `1 − (2/3) e^{−t}`, where `t` is the length of the internal edge |
| [`External.AllmanDegnanRhodes2011.four_unrootedDist_of_ne_of_isBinary`](FourTaxa.lean#L46) | each of the two other quartet trees has probability `(1/3) e^{−t}` |
| [`External.AllmanDegnanRhodes2011.unrootedDist_eq_zero_four`](FourTaxa.lean#L54) | on four taxa, only the three quartet trees have positive probability |
| [`External.AllmanDegnanRhodes2011.f1_exists_split_of_isBinary`](FourTaxa.lean#L62), [`External.AllmanDegnanRhodes2011.f1_mem_unroot_iff_of_split`](FourTaxa.lean#L69) | a binary species tree on four taxa has exactly one nontrivial split |
| [`External.AllmanDegnanRhodes2011.four_unrootedLength_pos`](FourTaxa.lean#L76) | the edge of the unrooted species tree that induces a split has positive length |

**The proof.** Each statement is the theorem of the same name of lean4-allman2011
(<https://github.com/vltanh/lean4-allman2011>, the formalization of Allman, Degnan and Rhodes 2011,
which this repository requires), which proves them by the source's argument of Section 4.1.
