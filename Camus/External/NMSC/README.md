# The network multispecies coalescent

**Why it is here.** Sections 3.3 and 3.4 of the paper assume that gene trees evolve down a level-1
network under the network multispecies coalescent (NMSC), and motivate Quartet Filtering
(Algorithm 1) by the distributions of quartet trees that it gives. The model is in
lean4-phylogenetics, which this repository requires: rooted metric level-1 networks described
recursively from the root (`Phylogenetics.Net`, with `Phylogenetics.Net.WellFormed`: positive edge
lengths, inheritance probabilities in `(0, 1)`, no cycle of two edges, distinct leaf labels),
Kingman's coalescent on forests of gene lineages, the NMSC (`Phylogenetics.Net.forestDist`,
`Phylogenetics.Net.geneTreeDist`), the quartet concordance factors (CFs, `Phylogenetics.Net.quartetCF`),
sampling consistency, and the CFs of four components of a cycle, those of the induced metric quarnet
(H. Baños, *Identifying species network features from gene tree quartets under the coalescent
model*, Bull. Math. Biol. 81 (2019) 494–534: `Phylogenetics.nmsc_quartetCF`). This directory, in
the namespace `External.NMSC`, holds the facts about the model that the paper's library needs and
lean4-phylogenetics does not have. They import nothing of the paper's library.

**The files.**

- [`Context.lean`](Context.lean): the argument of `Phylogenetics.quartetCF_eq_sum_top`, stated for any subnetwork:
  the rest of the network acts on the forest at the root of a subnetwork by a nice kernel
  ([`External.NMSC.exists_context_kernel`](Context.lean#L430)), and the quartet CF is the expected score of that forest
  when three of the four lineages are sampled below it ([`External.NMSC.quartetCF_eq_sum_subnet`](Context.lean#L460)).
  [`Cycle.lean`](Cycle.lean): the steps of `Phylogenetics.nmsc_quartetCF` for four given taxa
  ([`External.NMSC.quartetCF_eq_of_components`](Cycle.lean#L459)). Both files repeat the private steps of the
  library's proofs that they need, which lean4-phylogenetics does not export.
- [`Displayed.lean`](Displayed.lean): the displayed trees of a network (the paper's Definition 1), by their clusters,
  and its displayed quartets ([`External.NMSC.Net.Displays`](Displayed.lean#L731)).
- [`ThreeCycle.lean`](ThreeCycle.lean): the quartet CFs of a 3-cycle above two taxa, `N₃₂`, and the anomaly of Ané,
  Fogg, Allman, Baños and Rhodes (2024): the only quartet that `N₃₂` displays on its four taxa can be
  strictly the least probable ([`External.NMSC.net32_anomaly`](ThreeCycle.lean#L585)), or strictly the most probable,
  depending on the edge lengths ([`External.NMSC.net32_long`](ThreeCycle.lean#L614)).
- [`GeneLaw.lean`](GeneLaw.lean): independent gene trees with the law of the NMSC ([`External.NMSC.Net.genes`](GeneLaw.lean#L78)).
- [`Swap.lean`](Swap.lean): the exchange of the two sides of a cycle, with `γ` and `1 − γ`
  ([`External.NMSC.Net.SideSwap`](Swap.lean#L66)), which changes neither the distribution of the gene trees
  ([`External.NMSC.Net.SideSwap.geneTreeDist_eq`](Swap.lean#L309)) nor the displayed trees nor the anomalous configuration.
- [`AnomalyRegion.lean`](AnomalyRegion.lean): the exact region of the parameters of `N₃₂` in which the quartet it displays
  is the least probable ([`External.NMSC.net32_anomalous_iff`](AnomalyRegion.lean#L142)); [`AnomalyShapes.lean`](AnomalyShapes.lean): the two other
  rootings of the same quarnet, whose CFs are those of `N₃₂` with lengths added;
  [`AnomalyGeneral.lean`](AnomalyGeneral.lean): the CFs of four taxa in the anomalous configuration of any network, those
  of `N₃₂` with the probability that the two lineages below the hybrid node reach it apart
  ([`External.NMSC.Net.Cycle.apartProb`](AnomalyGeneral.lean#L424)) and lengths added along the sides
  ([`External.NMSC.Net.Cycle.quartetCF_of_anomalous`](AnomalyGeneral.lean#L768)).
- [`Splits.lean`](Splits.lean), [`FourComponents.lean`](FourComponents.lean), [`Pairs.lean`](Pairs.lean), [`Pattern.lean`](Pattern.lean): the CF pattern that Quartet
  Filtering presumes holds for every set of four taxa except in the anomalous configuration
  ([`External.NMSC.Net.regularOn_of_not_anomalous`](Pattern.lean#L873)), and its weaker part holds always
  ([`External.NMSC.Net.weakPattern`](Pattern.lean#L882)).

The declarations on the networks of lean4-phylogenetics (`Phylogenetics.Net`, `Phylogenetics.Side`,
`Phylogenetics.Net.Cycle`) are named in this namespace, [`External.NMSC.Net.Displays`](Displayed.lean#L731) for instance,
so the code applies them by name (`Net.Displays N q`) rather than with dot notation. They are
general facts about the NMSC, and their home is lean4-phylogenetics ([`Camus/External/README.md`](../README.md)).

The consequences for Sections 3.2 to 3.4 of CAMUS are in [`Camus/Pipelines/NMSC/`](../../Pipelines/NMSC), with the graph
of a network in the representation of CAMUS ([`Camus/Pipelines/NMSC/BaseTree.lean`](../../Pipelines/NMSC/BaseTree.lean),
[`Camus/Pipelines/NMSC/Bridge.lean`](../../Pipelines/NMSC/Bridge.lean)).
