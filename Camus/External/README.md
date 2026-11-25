# The results the paper cites

One directory per source, `Camus/External/<Source>/`, with modules `Camus.External.<Source>.…`,
declarations in the namespace `External.<Source>`, and a README giving the source, the
statement, how the paper uses it, and the argument that proves it. Each result is stated in its
source's terms and proved; none is assumed.

| Source | Directory | What is proved |
| --- | --- | --- |
| Warnow, Tabatabaee, Evans 2025 | [`WarnowTabatabaeeEvans/`](WarnowTabatabaeeEvans) | Observation 2, which the proof of Lemma 1 cites and its source states without proof; the single site model of their Section 4.2, with `p(e, s, s) > 0` on the tree edges, and the convergence of the quartets of SNPs to the quartets displayed by the network (the step of their Theorem 6 that Section 3.2 uses) |
| Allman, Degnan, Rhodes 2011 | [`AllmanDegnanRhodes2011/`](AllmanDegnanRhodes2011) | the distributions of the unrooted gene trees on four taxa (their Section 4.1), from lean4-allman2011 |
| The network multispecies coalescent | [`NMSC/`](NMSC) | the facts about the NMSC of lean4-phylogenetics that Sections 3.3 and 3.4 need: the displayed trees of a network, the anomalous 3-cycle of Ané, Fogg, Allman, Baños, Rhodes 2024 and its region in every network, the pattern of the quartet concordance factors, the exchange of the sides of a cycle, independent gene trees |

The other results that the paper uses come from the libraries this repository requires: the
multispecies coalescent and the network multispecies coalescent, with the quartet concordance
factors of a cycle (Baños 2019), and Steel's determination of a tree by its quartets (Steel 1992),
from lean4-phylogenetics.

## What the sources share with the paper's library

Warnow, Tabatabaee and Evans state their results on the paper's networks. The definitions are in
[`Camus/Defs.lean`](../Defs.lean), which the Challenge copies, and the facts about them that the sources use are in
the modules below, which import nothing of the paper's results: only Mathlib, [`Camus/Basic/`](../Basic),
[`Camus/Defs.lean`](../Defs.lean) and one another. The modules of [`WarnowTabatabaeeEvans/`](WarnowTabatabaeeEvans) import only these,
`Basic/` and Mathlib; those of [`NMSC/`](NMSC) and [`AllmanDegnanRhodes2011/`](AllmanDegnanRhodes2011) import only lean4-phylogenetics,
lean4-allman2011 and one another.

| Module | What it holds |
| --- | --- |
| [`Camus.Defs`](../Defs.lean) | trees, quartets, networks, switchings and display, the cut edges and cycles of Observation 2, and the other definitions of the Challenge |
| [`Camus.Tree.Geometry`](../Tree/Geometry.lean), [`Camus.Tree.Forest`](../Tree/Forest.lean) | the geometry of addresses: ancestors, `lca`, the footprint of an added edge; hanging subtrees |
| [`Camus.Galled.Basic`](../Galled/Basic.lean) | the block grammar of galled networks, which the geometry of addresses uses |
| [`Camus.Network.Code`](../Network/Code.lean) | the vertices of a network as codes of addresses |
| [`Camus.Network.Quartets`](../Network/Quartets.lean) | quartets as tuples, and the quartets on a set of taxa |
| [`Camus.Network.Isomorphism.Rename`](../Network/Isomorphism/Rename.lean) | renaming the vertices of a network; the sides of a quartet |
| [`Camus.Network.Completeness.Anchors`](../Network/Completeness/Anchors.lean), [`Camus.Network.Completeness.Tree`](../Network/Completeness/Tree.lean), [`Camus.Network.Completeness.Cycles`](../Network/Completeness/Cycles.lean) | switchings are spanning trees; the cycle that a left-out edge closes |
| [`Camus.Network.Cuts`](../Network/Cuts.lean) | deleting a cut edge, or two edges of a cycle, from a network and from a switching |
| [`Camus.Network.Clades`](../Network/Clades.lean) | display by the clades of a switching |

The NMSC facts of [`NMSC/`](NMSC), and these modules about rooted networks, are general phylogenetics:
their home is lean4-phylogenetics.

Two declarations are not where their source would put them: the counterexample to the step of the
proof of Theorem 6 of Warnow, Tabatabaee and Evans that needs `p(e, s, s) > 0`
([`Camus.theorem6_step_needs_stay`](../Pipelines/Theorem6Gap.lean#L188)) is built from the paper's networks, and is in the paper's
library, [`Camus/Pipelines/Theorem6Gap.lean`](../Pipelines/Theorem6Gap.lean); and the results of [`NMSC/`](NMSC) that answer the paper's
claims about Quartet Filtering (the pattern of the concordance factors, and the region of the
anomaly) are listed among the paper's results in the audit, [`scripts/Audit.lean`](../../scripts/Audit.lean).
