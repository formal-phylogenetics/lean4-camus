# CAMUS: scalable phylogenetic network estimation, in Lean

[![CI](https://github.com/formal-phylogenetics/lean4-camus/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/formal-phylogenetics/lean4-camus/actions/workflows/lean_action_ci.yml)

A Lean 4 formalization of James Willson and Tandy Warnow (2026), "CAMUS: scalable phylogenetic
network estimation", [Bioinformatics 42, Supplement 1 (2026), btag245](https://doi.org/10.1093/bioinformatics/btag245),
with the results it cites. CAMUS takes a rooted binary tree `T` and a multiset `Q` of quartet
trees, and adds edges to `T` to obtain a rooted level-1 phylogenetic network that displays as many
quartets of `Q` as possible. The paper's Theorem 1 says that its dynamic program over `T` finds such
a network.

Every result of the paper is proved, by the paper's argument except at two steps, or refuted, with
no `sorry` and no assumed result: Lemmas 1 and 2, Theorem 1 against every network built on `T` in
the sense of Definition 1, the running time and peak memory of Sections 2.3 and 2.4 for CAMUS
written as a program in a cost semantics, the claim of Section 2.4 for the networks returned by
backtracking, and the steps of the statistical arguments of Sections 3.2 to 3.4 inside the models
they use. Four claims of the paper are false: the best score with exactly `k` reticulations can
decrease as `k` grows, and the stopping rule can stop before a better score (Section 2.4); the true
network need not be the unique optimum, even with the fewest reticulations, cycles of length at
least five and an outgroup (Section 3.2); and a tree of a network need not be a basis for it
(Section 3.2). Under the network multispecies coalescent, Quartet Filtering can keep a quartet
outside `Q(N_r)` and drop the one inside it, exactly in an explicit region of the parameters of the
network (Sections 3.3 and 3.4).

This paper belongs to the hub
[lean4-phylo-network](https://github.com/formal-phylogenetics/lean4-phylo-network), on phylogenetic
network estimation, in the collection rooted at
[lean4-phylogenetics](https://github.com/formal-phylogenetics/lean4-phylogenetics).

## Status

| Part of the paper | Status |
| --- | --- |
| §2.1: Definition 1, Lemmas 1 and 2 | proved; uniqueness in Lemma 1 by the disjointness of the cycles (E1) |
| §2.2: the recurrence, Theorem 1 | proved, against every network built on `T` in the sense of Definition 1 (E8) |
| §2.3: running time `O(n²(\|Q\| + n))`, memory `O(n⁴)` | proved for CAMUS as a program in a cost semantics |
| §2.4: the networks `N_k`, `m ≤ n − 1`, running time | proved, for the networks returned by backtracking through a recurrence of the formalization |
| §2.4: monotonicity and the stopping rule | false (E5, E6); monotonicity for at most `k` reticulations proved |
| §3.2: the SNP pipeline | uniqueness false (E7), the basis claim false (E8); recovery proved under identifiability under inclusion and a tie-break, as one statement in the site model of Warnow et al. |
| §3.3, §3.4: Quartet Filtering | proved under the multispecies coalescent; under the network coalescent, proved outside the anomalous configuration and refuted inside an explicit region (E9) |
| Cited results (Warnow, Tabatabaee, Evans 2025; Allman, Degnan, Rhodes 2011; Baños 2019; Ané et al. 2024) | proved, in [`Camus/External/`](Camus/External), or in lean4-phylogenetics and lean4-allman2011 |
| The experiments | not formalized |

## Main results

The statements of record are the theorems of the Challenge,
[`palomar/Camus/Challenge.lean`](palomar/Camus/Challenge.lean), in the namespace `CamusChallenge`. The Challenge imports only
Mathlib, and its definitions are those of [`Camus/Defs.lean`](Camus/Defs.lean), copied by
[`scripts/sync_challenge_defs.py`](scripts/sync_challenge_defs.py) (its module docstring explains each one).
[`palomar/Camus/Solution.lean`](palomar/Camus/Solution.lean) proves each of them, under the same name, from the library.

| Paper | Lean | Statement |
| --- | --- | --- |
| Theorem 1 | [`CamusChallenge.theorem1`](palomar/Camus/Challenge.lean#L852) | for every array `M` satisfying the recurrence of Equations (1)–(5) and every backtracking trace `E`, the network obtained by adding `E` to `T` is built on `T`, satisfies `M[root]` quartets of `Q`, and no network built on `T` in the sense of Definition 1 satisfies more, or displays more quartets of `Q` |
| Theorem 1 | [`CamusChallenge.exists_array_trace`](palomar/Camus/Challenge.lean#L865) | the array and a trace exist |
| Definition 1 | [`CamusChallenge.tree_displays_iff`](palomar/Camus/Challenge.lean#L870) | a tree displays exactly its own quartets |
| Equation (1) | [`CamusChallenge.edgeWeight_eq`](palomar/Camus/Challenge.lean#L876) | the weights count the quartets satisfied by one added edge |
| Definition 1 | [`CamusChallenge.definition1_reduction`](palomar/Camus/Challenge.lean#L883), [`CamusChallenge.builtOn_not_anchored`](palomar/Camus/Challenge.lean#L891) | every network built on `T` in the sense of Definition 1 has the reticulations and the quartets of a network obtained by adding edges to `T`, and the first class is larger |
| §2.4 | [`CamusChallenge.reticulation_restriction`](palomar/Camus/Challenge.lean#L903), [`CamusChallenge.exists_budget_traces`](palomar/Camus/Challenge.lean#L920) | the modified array's row `k` at the root is nonempty if and only if some network built on `T` has exactly `k` reticulations, and every network returned by backtracking from it is built on `T`, has `k` reticulations and the best score among them |
| §2.4, §3.2 | [`CamusChallenge.not_exactCountMonotone`](palomar/Camus/Challenge.lean#L926), [`CamusChallenge.not_exactStoppingRule`](palomar/Camus/Challenge.lean#L932), [`CamusChallenge.not_atMostStoppingRule`](palomar/Camus/Challenge.lean#L937), [`CamusChallenge.not_uniqueOptimum`](palomar/Camus/Challenge.lean#L942) | the claims, stated as [`ExactCountMonotone`](palomar/Camus/Challenge.lean#L781), [`ExactStoppingRule`](palomar/Camus/Challenge.lean#L826), [`AtMostStoppingRule`](palomar/Camus/Challenge.lean#L834) and [`UniqueOptimum`](palomar/Camus/Challenge.lean#L792), are false |
| §3.2 | [`CamusChallenge.recovery`](palomar/Camus/Challenge.lean#L950), [`CamusChallenge.tree_identifiable`](palomar/Camus/Challenge.lean#L967), [`CamusChallenge.recovery_needs_identifiable`](palomar/Camus/Challenge.lean#L980) | the claim holds when the true network is identifiable under inclusion and ties are broken toward the fewest reticulations; a tree is identifiable; identifiability cannot be dropped, even with the tie-break |

### Also proved in the library

| Paper | Lean | Statement |
| --- | --- | --- |
| Lemmas 1, 2 | [`lemma1`](Camus/Preliminaries/Lemmas.lean#L140), [`lemma1_union`](Camus/Preliminaries/Lemmas.lean#L291), [`lemma2`](Camus/Preliminaries/Lemmas.lean#L162) | the quartets of `Q(N_r)` satisfied by one non-tree edge; at most one non-tree edge per target |
| Theorem 1 | [`theorem1`](Camus/DP/Theorem1.lean#L109), [`theorem1_builtOn`](Camus/DP/Definition1.lean#L76) | Theorem 1, for networks obtained by adding edges and over Definition 1's class |
| §2.3 | [`Complexity.camus_array`](Camus/Complexity/Program.lean#L1090), [`Complexity.camus_time`](Camus/Complexity/Program.lean#L1193), [`Complexity.time_delta`](Camus/Complexity/Delta.lean#L746), [`Complexity.storedIntegers_bound`](Camus/Complexity/Memory.lean#L181), [`Complexity.camus_memory`](Camus/Complexity/PeakMemory.lean#L392) | the program computes `M`, in time `O(n²(\|Q\| + n))`, with `δ_T` in constant time and peak memory `O(n⁴)` |
| §2.4 | [`BudgetDP.reticulation_restriction`](Camus/Restriction/Main.lean#L61), [`BudgetDP.backtracking_networks`](Camus/Restriction/Backtracking.lean#L499), [`Complexity.camusBudget_time`](Camus/Complexity/BudgetProgram.lean#L648), [`Complexity.camusBudgetNetworks_time`](Camus/Complexity/BudgetBacktracking.lean#L1278) | the networks `N_k` by backtracking, in time `O(n²(\|Q\| + m³n))` |
| §2.4 | [`RootedNetwork.anchored_reticulation_bound`](Camus/Network/Reticulations.lean#L229), [`RootedNetwork.reticulationCount_le`](Camus/Network/TreeBased/Root.lean#L256) | at most `n − 1` reticulations, for every rooted binary level-1 network |
| §3.2 | [`RootedNetwork.treeBased`](Camus/Network/TreeBased/Main.lean#L135), [`pipeline_tendsto`](Camus/Pipelines/Pipeline.lean#L486) | tree-basedness; the SNP pipeline, in the site model of Warnow et al. |
| §3.3, §3.4 | [`Coalescent.msc_filterQuartets`](Camus/Pipelines/Coalescent.lean#L250), [`NMSC.nmsc_filterQuartets_support`](Camus/Pipelines/NMSC/Recovery.lean#L100), [`NMSC.anomaly_filterQuartets`](Camus/Pipelines/NMSC/Anomaly.lean#L238), [`NMSC.nmsc_recovery_displayed`](Camus/Pipelines/NMSC/DisplayedTrees.lean#L1104), [`NMSC.nmsc_recovery_underlying`](Camus/Pipelines/NMSC/Pipeline.lean#L117), [`NMSC.anomalous_drop_iff`](Camus/Pipelines/NMSC/AnomalyBoundary.lean#L726) | Quartet Filtering under the multispecies coalescent and the network coalescent, recovery through every displayed tree, and the region of the anomaly |
| Refutations | [`not_exactCountMonotone`](Camus/Restriction/Monotonicity.lean#L37), [`not_exactStoppingRule`](Camus/Restriction/StoppingRule.lean#L462), [`not_atMostStoppingRule`](Camus/Restriction/StoppingRule.lean#L481), [`not_uniqueOptimum`](Camus/Pipelines/Uniqueness.lean#L50), [`Counterexamples.shallow_not_identifiable`](Camus/Pipelines/Inclusion.lean#L219), [`Counterexamples.deeperDonor_meets_hypotheses`](Camus/Pipelines/SNPCondition.lean#L321), [`Counterexamples.camus_output_not_rootAboveNet`](Camus/Network/RootAbove/Example.lean#L384), [`camus_may_add_edge`](Camus/Pipelines/Uniqueness.lean#L135), [`Counterexamples.camus_may_return_deep`](Camus/Pipelines/Inclusion.lean#L374) | E5–E8, with CAMUS itself returning the wrong network |

### The sources

| Source | Lean | Statement |
| --- | --- | --- |
| Warnow, Tabatabaee, Evans 2025, Observation 2 | [`External.WarnowTabatabaeeEvans.observation2`](Camus/External/WarnowTabatabaeeEvans/Observation2.lean#L189) | `ab\|cd ∈ Q(N_r)` iff deleting a cut edge, or two edges of a cycle one of which enters its bottom node, separates `a, b` from `c, d`; stated without proof by its source |
| Warnow, Tabatabaee, Evans 2025, Theorem 6 | [`External.WarnowTabatabaeeEvans.support_tendsto`](Camus/External/WarnowTabatabaeeEvans/Sampling.lean#L102) | under their site model, with `p(e, s, s) > 0` on the tree edges, the quartets of the SNPs converge to `Q(N_r)`; [`theorem6_step_needs_stay`](Camus/Pipelines/Theorem6Gap.lean#L188): the hypothesis cannot be dropped |
| Allman, Degnan, Rhodes 2011, Section 4.1 | [`External.AllmanDegnanRhodes2011.four_unrootedDist_of_mem`](Camus/External/AllmanDegnanRhodes2011/FourTaxa.lean#L38), [`External.AllmanDegnanRhodes2011.four_unrootedDist_of_ne_of_isBinary`](Camus/External/AllmanDegnanRhodes2011/FourTaxa.lean#L46) | the quartet gene trees of a binary species tree on four taxa, from lean4-allman2011 |
| Baños 2019 | `Phylogenetics.nmsc_quartetCF`, [`External.NMSC.quartetCF_eq_of_components`](Camus/External/NMSC/Cycle.lean#L459) | the quartet concordance factors of the components of a cycle under the network coalescent, from lean4-phylogenetics |
| Ané, Fogg, Allman, Baños, Rhodes 2024 | [`External.NMSC.net32_anomaly`](Camus/External/NMSC/ThreeCycle.lean#L585) | a 3-cycle above two taxa can make the displayed quartet the least probable |

## What the audit found

| Finding | Where |
| --- | --- |
| The best score with exactly `k` reticulations can decrease as `k` grows, and the stopping rule can stop before a better score (Section 2.4) | E5, E6 |
| The true network need not be the unique optimum, even with the fewest reticulations, cycles of length at least five and an outgroup; in the site model the tie occurs with probability tending to 1 under every hypothesis of Section 3.2 | E7 |
| A tree of a network need not be a basis for it; the proof of Theorem 1 does not treat the networks of Definition 1 whose root lies above the root of `T`, which display the quartets of networks that it treats | E8 |
| Under the network coalescent, on the anomalous configuration of Ané et al. (2024), Quartet Filtering keeps a quartet outside `Q(N_r)` and drops the one inside it, exactly in a region of the parameters determined for every network | E9 |
| Lemma 1's proof derives uniqueness from Observation 2, which gives only existence; `M[r]` is the number of satisfied quartets, not the score | E1, E2 |
| Equation (1) is read over distinct quartets, and `Pairs(v)` restricted to pairs that give a network | E3, E4 |
| Missing hypotheses: identifiability under inclusion and a tie-break (Section 3.2), `p(e, s, s) > 0` in the site model, a positive threshold for Algorithm 1 | Section 4 |
| A typo | E10 |

[Section 3 of the report](docs/Camus/REPORT.md#3-errors-and-gaps-in-the-paper) gives each finding with its location, the paper's
sentence, a Lean counterexample and the repair. Every proof follows the paper's, except uniqueness
in Lemma 1 and Theorem 1 over Definition 1's class, both in
[Section 7 of the report](docs/Camus/REPORT.md#7-departures-from-the-papers-proofs) with what the paper does, what Lean does and why.

## Trust

- `lake build` passes. Its warnings are the `sorry`s of the Challenge's statements, linter notes
  (unused tactics, global instances) and two deprecated Mathlib names. There is no `sorry`, `axiom`,
  `native_decide` or `implemented_by` in [`Camus/`](Camus) or in the Solution.
- [`scripts/Audit.lean`](scripts/Audit.lean) checks every declaration of the project and of the libraries it requires, including
  private and generated ones, against [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound), and writes the
  routes of the proofs.
- [`scripts/route_check.py`](scripts/route_check.py) compares those routes with the paper's, in
  [`docs/Camus/paper_routes.tsv`](docs/Camus/paper_routes.tsv); [`docs/Camus/route_differences.tsv`](docs/Camus/route_differences.tsv) records every difference, with its
  reason.
- Comparator checks that the Solution proves exactly the Challenge's statements, under Lean's kernel
  and NanoDa.
- No person has reviewed the proofs. Independent agents reviewed the statements, the proofs,
  the findings and the account of the literature ([`docs/Camus/CREDITS.md`](docs/Camus/CREDITS.md)).

## Dependencies

- [Mathlib](https://github.com/leanprover-community/mathlib4), at `v4.37.0-rc1`.
- [lean4-phylogenetics](https://github.com/formal-phylogenetics/lean4-phylogenetics), the library of
  the collection: the multispecies coalescent, the network multispecies coalescent on level-1
  networks with the quartet concordance factors of a cycle, and Steel's determination of a tree by
  its quartets.
- [lean4-phylo-network](https://github.com/formal-phylogenetics/lean4-phylo-network), the library of
  the papers on network estimation, of which this is one.
- [lean4-allman2011](https://github.com/formal-phylogenetics/lean4-allman2011), the formalization of
  Allman, Degnan and Rhodes 2011: the distributions of the gene trees on four taxa.

Each is pinned by commit in [`lakefile.toml`](lakefile.toml).

## Palomar

No submission to Palomar is planned. [`palomar/Camus/`](palomar/Camus) has the files of an entry: the Challenge,
which imports only Mathlib, the Solution, [`palomar/Camus/comparator.json`](palomar/Camus/comparator.json), which names them and the
theorems, and [`palomar/Camus/formalization.yaml`](palomar/Camus/formalization.yaml), the entry's metadata. CI checks that the Challenge's
copy of the definitions is the block of [`Camus/Defs.lean`](Camus/Defs.lean) (`python3 scripts/sync_challenge_defs.py --check`).

## Building

From the root of the repository:

```sh
lake exe cache get
lake build
lake build Phylogenetics PhyloNetwork Allman2011                     # the libraries the audit reads
lake env lean scripts/Audit.lean                                     # axioms and dependencies
python3 scripts/route_check.py check docs/Camus/paper_routes.tsv --accept docs/Camus/route_differences.tsv
python3 scripts/sync_challenge_defs.py --check                       # the Challenge's copy of the definitions
lake env lake comparator --config palomar/Camus/comparator.json      # Comparator; needs bubblewrap
python3 scripts/linkify_docs.py                                      # the documents' links to the code
```

The toolchain is Lean `v4.37.0-rc1` ([`lean-toolchain`](lean-toolchain), [`lake-manifest.json`](lake-manifest.json)).

## Layout

| Folder | Content |
| --- | --- |
| [`Camus/Basic/`](Camus/Basic) | General mathematics, in Mathlib's namespaces; [its README](Camus/Basic/README.md) says where each part could go |
| [`Camus/External/`](Camus/External) | The cited results, one directory per source, in the namespaces `External.<Source>`; [its README](Camus/External/README.md) lists them and the modules they share with the paper's library |
| [`Camus/Defs.lean`](Camus/Defs.lean) | The definitions of the Challenge: trees, quartets, networks and display (Definition 1), networks built on `T`, added edges (Definitions 2, 3, 5), the recurrence (Equations (1)–(5)), the modified recurrence of Section 2.4 and its backtracking, the refuted claims |
| [`Camus/Tree/`](Camus/Tree), [`Camus/Network/`](Camus/Network), [`Camus/Galled/`](Camus/Galled), [`Camus/Score.lean`](Camus/Score.lean) | The geometry of the tree and Lemma 2 for families of added edges; directed networks, their switchings, cuts and clades, the canonical network of a family of added edges, display under subdivision and isomorphism, networks whose root lies above the root of `T`, tree-basedness, reticulation counts; galled networks; Definition 4 and Equation (1) |
| [`Camus/Preliminaries/`](Camus/Preliminaries) | Section 2.1: Lemmas 1 and 2, Figure 1 |
| [`Camus/DP/`](Camus/DP) | Section 2.2: the recurrence and Theorem 1, over Definition 1's class |
| [`Camus/Complexity/`](Camus/Complexity) | Sections 2.3 and 2.4: the cost semantics, CAMUS as a program, its running time and memory |
| [`Camus/Restriction/`](Camus/Restriction) | Section 2.4: the modified recurrence, the networks `N_k`, E5 and E6 |
| [`Camus/Pipelines/`](Camus/Pipelines) | Section 3: E7 and the corrected recovery, the SNP pipeline in the site model, Algorithm 1 under the multispecies coalescent and the network coalescent |
| [`palomar/Camus/`](palomar/Camus) | The Challenge, the Solution, the Comparator configuration and the metadata |
| [`docs/Camus/`](docs/Camus) | [The report](docs/Camus/REPORT.md), [the credits](docs/Camus/CREDITS.md), the routes of the proofs and the reviewed differences |
| [`scripts/`](scripts) | The audit, the route check, the copy of the definitions into the Challenge, the links and the tables |

## Related work

From [the report](docs/Camus/REPORT.md#10-the-paper-in-the-literature), Section 10 (search of 10 October 2026):

- CAMUS belongs to the two-phase methods that add edges to a tree (T-REX, Makarenkov 2001; Cao, Zhu
  and Nakhleh 2019); no exact algorithm for its problem, with the tree fixed, was found before it.
  Without a fixed tree, maximizing consistent triplets over level-`k` networks is NP-hard (van
  Iersel, Kelk and Mnich 2009).
- Observation 2 comes from Warnow, Tabatabaee and Evans (2025), who state it without proof; their
  Theorem 5 shows that the quartets of a level-1 network with cycles of length at least five
  determine its unrooted topology and the bottom node of each cycle, which concerns equality of
  quartet sets, where E7 concerns inclusion.
- Since the paper: NetCS (Dai and Molloy, WABI 2026) and BROOQS (Arasti and Mirarab, preprint, 2026)
  compare with CAMUS; BROOQS reports that CAMUS's default criterion overestimates the number of
  reticulations. No correction of the paper was found.
- No other formalization of CAMUS or Observation 2 was found.

## What's next

Identifiability under inclusion fails even for networks whose cycles have length at least five (E7);
a second tie-break toward the fewest displayed quartets selects the true network in the
counterexample, and whether it recovers every such network is open. Whether a filter that tests all
three frequencies avoids the anomaly of E9 is open. Theorem 1 splits into Lemma 1 and a weighted
packing of paths in a tree, which is how the formal proof is organized. See
[Section 11 of the report](docs/Camus/REPORT.md#11-whats-next).

## Credits

- Maintainer: The-Anh Vu-Le, who requested and supervised the formalization.
- Formalization: in six rounds, following the
  [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure, first by
  OpenAI's `gpt-6.1-sol` in Codex CLI (2026-10-08), then by Claude Opus 5.5 in Claude Code
  (2026-10-10, five rounds). [`docs/Camus/CREDITS.md`](docs/Camus/CREDITS.md) gives the agents, the
  figures and what each round did.
- Review: no person has reviewed the proofs; Lean's kernel checks them. Independent agents reviewed
  the statements, the proofs, the findings and the account of the literature.

## License

Apache-2.0: [LICENSE](LICENSE).
