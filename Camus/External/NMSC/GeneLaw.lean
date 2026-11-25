module

public import Phylogenetics.NMSC.Level1.GeneTrees
public import Phylogenetics.NMSC.Level1.Sampling
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Independent gene trees under the NMSC

Sections 3.3 and 3.4 of CAMUS take gene trees that evolve down a level-1 network under the NMSC,
independently. This file shows that the gene tree distribution of the NMSC on a metric network with
distinct leaf labels is a probability distribution (`Phylogenetics.Net.geneTreeDist_nonneg`,
`Phylogenetics.Net.sum_geneTreeDist`), and builds sequences of independent gene trees with this law on the
product space (`External.NMSC.Net.genes`, with `MeasureTheory.Measure.infinitePi`), as
`Camus/Pipelines/Coalescent/Sampling.lean` does for the multispecies coalescent.

## Main results

* `Phylogenetics.Net.forestDist_nonneg`, `Phylogenetics.Net.geneTreeDist_nonneg`,
  `Phylogenetics.Net.sum_geneTreeDist`: the NMSC gives probability distributions.
* `External.NMSC.Net.geneLaw`: the law of the gene tree, with one lineage per taxon.
* `External.NMSC.Net.genes`, `External.NMSC.Net.genes_iIndepFun`, `External.NMSC.Net.genes_identDistrib`,
  `External.NMSC.Net.genes_law`: independent gene trees with that law.
-/

@[expose] public noncomputable section

namespace External.NMSC

open Phylogenetics

open Finset Matrix MeasureTheory ProbabilityTheory

universe u

section Nonneg

variable {L : Type*} [Fintype L] [DecidableEq L]

variable {X : Type u} [DecidableEq X]

/-- The forests at the root of a network with distinct leaf labels are good. -/
theorem Net.isGood_of_forestDist_ne_zero {N : Net X} (hN : N.leaves.Nodup) (s : L → X)
    {F : Finset (Finset L)} (hF : N.forestDist s F ≠ 0) : IsGoodForest F := by
  rw [Net.forestDist_eq] at hF
  exact (Net.forestDistOf_single_support N hN (sampledAt s) (fun _ _ => isGoodForest_singletons _)
    (fun _ _ _ _ hab => disjoint_lineages_sampledAt s hab) hF).1

end Nonneg

/-! ### Independent gene trees -/

section Genes

variable {X : Type u} [Fintype X] [DecidableEq X] [MeasurableSpace (Finset (Finset X))]

/-- The law of the gene tree of the NMSC on the metric network `N` with distinct leaf labels, one
lineage per taxon: the probability measure on the rooted gene trees (their clusters) with masses
`N.geneTreeDist id`. -/
def Net.geneLaw (N : Net X) (hN : N.WellFormed) : Measure (Finset (Finset X)) :=
  (PMF.ofFintype (fun G => ENNReal.ofReal (N.geneTreeDist id G)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun G _ => Net.geneTreeDist_nonneg _ hN id G,
      Net.sum_geneTreeDist _ hN.2 id, ENNReal.ofReal_one])).toMeasure

instance (N : Net X) (hN : N.WellFormed) : IsProbabilityMeasure ((Net.geneLaw N) hN) := by
  unfold Net.geneLaw
  infer_instance

theorem Net.geneLaw_real_singleton [MeasurableSingletonClass (Finset (Finset X))] (N : Net X)
    (hN : N.WellFormed) (G : Finset (Finset X)) :
    ((Net.geneLaw N) hN).real {G} = N.geneTreeDist id G := by
  rw [measureReal_def, Net.geneLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton G),
    PMF.ofFintype_apply, ENNReal.toReal_ofReal (Net.geneTreeDist_nonneg _ hN id G)]

/-- Independent gene trees under the NMSC on `N`: the product law on the sequences of gene trees,
under which the coordinates are the gene trees. -/
def Net.genes (N : Net X) (hN : N.WellFormed) : Measure (ℕ → Finset (Finset X)) :=
  Measure.infinitePi fun _ => (Net.geneLaw N) hN

instance (N : Net X) (hN : N.WellFormed) : IsProbabilityMeasure ((Net.genes N) hN) := by
  unfold Net.genes
  infer_instance

/-- Under `N.genes hN`, the gene trees are independent. -/
theorem Net.genes_iIndepFun (N : Net X) (hN : N.WellFormed) :
    iIndepFun (fun n (ω : ℕ → Finset (Finset X)) => ω n) ((Net.genes N) hN) :=
  iIndepFun_infinitePi (P := fun _ => (Net.geneLaw N) hN) (X := fun _ => id) fun _ => measurable_id

theorem Net.genes_map (N : Net X) (hN : N.WellFormed) (n : ℕ) :
    ((Net.genes N) hN).map (fun ω => ω n) = (Net.geneLaw N) hN :=
  Measure.infinitePi_map_eval _ n

/-- Under `N.genes hN`, the gene trees are identically distributed. -/
theorem Net.genes_identDistrib (N : Net X) (hN : N.WellFormed) (n : ℕ) :
    IdentDistrib (fun ω : ℕ → Finset (Finset X) => ω n) (fun ω => ω 0) ((Net.genes N) hN) ((Net.genes N) hN)
    where
  aemeasurable_fst := (measurable_pi_apply n).aemeasurable
  aemeasurable_snd := (measurable_pi_apply 0).aemeasurable
  map_eq := by rw [Net.genes_map, Net.genes_map]

/-- Under `N.genes hN`, the first gene tree has the law of the NMSC on `N`. -/
theorem Net.genes_law [MeasurableSingletonClass (Finset (Finset X))] (N : Net X)
    (hN : N.WellFormed) (G : Finset (Finset X)) :
    ((Net.genes N) hN).real ((fun ω : ℕ → Finset (Finset X) => ω 0) ⁻¹' {G}) = N.geneTreeDist id G := by
  rw [measureReal_def, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton G),
    Net.genes_map, ← measureReal_def, Net.geneLaw_real_singleton]

end Genes

end External.NMSC
