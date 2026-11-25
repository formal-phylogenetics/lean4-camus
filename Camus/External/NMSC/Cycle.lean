module

public import Camus.External.NMSC.Context
public import Phylogenetics.NMSC.Level1.Cycle

/-!
# The quartet CF of four taxa in four components of a cycle

`Phylogenetics.nmsc_quartetCF` (lean4-phylogenetics) gives the quartet CFs of the components of a
cycle `Ω` of a metric level-1 network `N` under the NMSC: those of the induced metric quarnet
(Baños 2019). `External.NMSC.quartetCF_eq_of_components` states its steps for four given taxa
`s 0, …, s 3` in distinct components, at the positions `pos l`: the quartet CF is the `γ`-mixture of
the CFs of the quartet trees that the positions induce on the path `0 — 1 — ⋯ — d`, with the hybrid
component at position `0` or `d`.

The proof is that of `Phylogenetics.nmsc_quartetCF`: `Phylogenetics.quartetCF_eq_sum_top` reduces the
CF to the expected score of the forest at the top node of `Ω`; each component sends at most one
lineage, which reaches the cycle unchanged; each side of the cycle is an arm of the displayed tree
(`Phylogenetics.Side.forestDist_eq_armDist`), and `Phylogenetics.displayed_score` computes the
expected score. The private steps, about the positions of the components, the nodes of the sides
and the edges of the cycle, are those of `Phylogenetics.nmsc_quartetCF`, which lean4-phylogenetics
does not export.
-/

@[expose] public noncomputable section

namespace External.NMSC

open Phylogenetics

open Finset Matrix

universe u

/-! ### Subnetworks -/

section Structure

variable {X : Type u}

private theorem nc_pendant_sublist {S : Side X} {n : ℝ × ℝ × Net X} (hn : n ∈ S.nodes) :
    n.2.2.leaves.Sublist S.leaves := by
  rw [Side.leaves_eq_flatten]
  exact List.sublist_flatten_of_mem (List.mem_map_of_mem hn)

end Structure

/-! ### The edges of a cycle -/

section CycleEdges

variable {X : Type u} {N : Net X} (Ω : N.Cycle)

/-- The edges of the two sides of `Ω`, from the hybrid node up `side₁` and down `side₂`: the edges
of the cycle, before the two edges at the top node are merged when it is the root of `N`. -/
private def ncE : List ℝ :=
  [Ω.side₁.hybLen] ++ Ω.side₁.nodes.reverse.map (fun n => n.1) ++
    Ω.side₂.nodes.map (fun n => n.1) ++ [Ω.side₂.hybLen]

private theorem nc_edges_of_ne (h : Ω.top ≠ N) : Ω.edges = ncE Ω := by
  simp only [Net.Cycle.edges, ite_eq_right h]; rfl

private theorem nc_edges_of_eq (h : Ω.top = N) :
    Ω.edges = (ncE Ω).take Ω.side₁.nodes.length ++
      [(ncE Ω).getD Ω.side₁.nodes.length 0 + (ncE Ω).getD (Ω.side₁.nodes.length + 1) 0] ++
        (ncE Ω).drop (Ω.side₁.nodes.length + 2) := by
  simp only [Net.Cycle.edges, ite_eq_left h]; rfl

private theorem ncE_length :
    (ncE Ω).length = Ω.side₁.nodes.length + Ω.side₂.nodes.length + 2 := by
  simp [ncE]; omega

private theorem ncE_zero : (ncE Ω).getD 0 0 = Ω.side₁.hybLen := by simp [ncE]

private theorem ncE_side₁ {i : ℕ} (hi : i < Ω.side₁.nodes.length) :
    (ncE Ω).getD (i + 1) 0 = (Ω.side₁.nodes.reverse[i]'(by simpa using hi)).1 := by
  unfold ncE
  rw [List.append_assoc, List.append_assoc, List.singleton_append, List.getD_cons_succ,
    List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
    List.getElem_map]

private theorem ncE_side₂ {j : ℕ} (hj : j < Ω.side₂.nodes.length) :
    (ncE Ω).getD (Ω.side₁.nodes.length + 1 + j) 0 = (Ω.side₂.nodes[j]).1 := by
  unfold ncE
  rw [List.getD_append _ _ _ _ (by simp; omega),
    List.getD_append_right _ _ _ _ (by simp),
    List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]
  congr 2
  simp

private theorem ncE_last :
    (ncE Ω).getD (Ω.side₁.nodes.length + Ω.side₂.nodes.length + 1) 0 = Ω.side₂.hybLen := by
  unfold ncE
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

private theorem nc_edgeLen_of_ne (h : Ω.top ≠ N) (m : ℕ) : Ω.edgeLen m = (ncE Ω).getD m 0 := by
  rw [Net.Cycle.edgeLen, nc_edges_of_ne Ω h]

private theorem nc_edgeLen_of_lt {m : ℕ} (hm : m < Ω.side₁.nodes.length) :
    Ω.edgeLen m = (ncE Ω).getD m 0 := by
  by_cases h : Ω.top = N
  · have hl := ncE_length Ω
    rw [Net.Cycle.edgeLen, nc_edges_of_eq Ω h, List.append_assoc,
      List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hm]
  · exact nc_edgeLen_of_ne Ω h m

private theorem nc_edgeLen_of_eq_p (h : Ω.top = N) :
    Ω.edgeLen Ω.side₁.nodes.length =
      (ncE Ω).getD Ω.side₁.nodes.length 0 + (ncE Ω).getD (Ω.side₁.nodes.length + 1) 0 := by
  have hl := ncE_length Ω
  rw [Net.Cycle.edgeLen, nc_edges_of_eq Ω h, List.append_assoc,
    List.getD_append_right _ _ _ _ (by simp), List.length_take, Nat.min_eq_left (by omega),
    Nat.sub_self]
  simp

private theorem nc_edgeLen_of_eq_of_gt (h : Ω.top = N) {m : ℕ}
    (hm : Ω.side₁.nodes.length < m) : Ω.edgeLen m = (ncE Ω).getD (m + 1) 0 := by
  have hl := ncE_length Ω
  rw [Net.Cycle.edgeLen, nc_edges_of_eq Ω h,
    List.getD_append_right _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD,
    List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 2
  simp; omega

end CycleEdges

/-! ### The components of a cycle -/

section CycleComponents

variable {X : Type u} [DecidableEq X] {N : Net X} (Ω : N.Cycle)

private theorem nc_component_of_le {i : ℕ} (hi : Ω.size ≤ i) : Ω.component i = ∅ :=
  List.getD_eq_default _ _ hi

omit [DecidableEq X] in
private theorem nc_top_leaves :
    Ω.top.leaves = Ω.side₁.leaves ++ Ω.side₂.leaves ++ Ω.below.leaves := rfl

omit [DecidableEq X] in
private theorem nc_top_sublist : Ω.top.leaves.Sublist N.leaves :=
  Net.leaves_sublist_of_mem_subnets Ω.mem

omit [DecidableEq X] in
private theorem nc_pendant₁_sublist {n : ℝ × ℝ × Net X} (hn : n ∈ Ω.side₁.nodes) :
    n.2.2.leaves.Sublist Ω.top.leaves :=
  (nc_pendant_sublist hn).trans (by
    rw [nc_top_leaves]; exact (List.sublist_append_left _ _).trans (List.sublist_append_left _ _))

omit [DecidableEq X] in
private theorem nc_pendant₂_sublist {n : ℝ × ℝ × Net X} (hn : n ∈ Ω.side₂.nodes) :
    n.2.2.leaves.Sublist Ω.top.leaves :=
  (nc_pendant_sublist hn).trans (by
    rw [nc_top_leaves]; exact (List.sublist_append_right _ _).trans (List.sublist_append_left _ _))

private theorem nc_top_taxa_subset : Ω.top.taxa ⊆ N.taxa := fun y hy => by
  simp only [Net.taxa, List.mem_toFinset] at hy ⊢
  exact (nc_top_sublist Ω).subset hy

/-- Every component except the component of the root lies below the top node of the cycle. -/
private theorem nc_component_subset_top {i : ℕ}
    (hi : Ω.top = N ∨ i ≠ Ω.side₁.nodes.length + 1) : Ω.component i ⊆ Ω.top.taxa := by
  have hsub : ∀ M : Net X, M.leaves.Sublist Ω.top.leaves → M.taxa ⊆ Ω.top.taxa :=
    fun M hM y hy => by
      simp only [Net.taxa, List.mem_toFinset] at hy ⊢
      exact hM.subset hy
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [Net.Cycle.component_zero]
    exact hsub _ (by rw [nc_top_leaves]; exact List.sublist_append_right _ _)
  by_cases hip : i ≤ Ω.side₁.nodes.length
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [Net.Cycle.component_side₁ Ω (by omega)]
    exact hsub _ (nc_pendant₁_sublist Ω (List.mem_reverse.1 (List.getElem_mem _)))
  by_cases hid : Ω.size ≤ i
  · rw [nc_component_of_le Ω hid]; exact empty_subset _
  have hq : Ω.size - 1 - i < Ω.side₂.nodes.length := by
    by_cases h : Ω.top = N
    · rw [Net.Cycle.size_of_top_eq Ω h] at hid ⊢; omega
    · have := hi.resolve_left h
      rw [Net.Cycle.size_of_top_ne Ω h] at hid ⊢; omega
  have := Net.Cycle.component_side₂ Ω hq
  rw [show Ω.size - (Ω.size - 1 - i + 1) = i by omega] at this
  rw [this]
  exact hsub _ (nc_pendant₂_sublist Ω (List.mem_reverse.1 (List.getElem_mem _)))

private theorem nc_component_subset (i : ℕ) : Ω.component i ⊆ N.taxa := by
  by_cases h : Ω.top ≠ N ∧ i = Ω.side₁.nodes.length + 1
  · rw [h.2, Net.Cycle.component_root Ω h.1]; exact sdiff_subset
  · exact (nc_component_subset_top Ω (by tauto)).trans (nc_top_taxa_subset Ω)

end CycleComponents

/-! ### The sides as arms of the displayed trees -/

section Arms

variable {X : Type u} [DecidableEq X] {N : Net X} (Ω : N.Cycle)

/-- The length of the top edge of a side. -/
private def ncTopLen {Y : Type u} : Side Y → ℝ
  | .hyb ℓ => ℓ
  | .node ℓ _ _ _ => ℓ

omit [DecidableEq X] in
private theorem ncTopLen_of_nil {S : Side X} (h : S.nodes = []) : ncTopLen S = S.hybLen := by
  cases S with
  | hyb ℓ => rfl
  | node ℓ b M S => simp [Side.nodes] at h

omit [DecidableEq X] in
private theorem ncTopLen_of_pos {S : Side X} (h : 0 < S.nodes.length) :
    ncTopLen S = (S.nodes[0]'h).1 := by
  cases S with
  | hyb ℓ => simp [Side.nodes] at h
  | node ℓ b M S => rfl

omit [DecidableEq X] in
private theorem ncE_p : (ncE Ω).getD Ω.side₁.nodes.length 0 = ncTopLen Ω.side₁ := by
  rcases Nat.eq_zero_or_pos Ω.side₁.nodes.length with hp | hp
  · rw [hp, ncE_zero, ncTopLen_of_nil (List.length_eq_zero_iff.1 hp)]
  · obtain ⟨i, hi⟩ : ∃ i, Ω.side₁.nodes.length = i + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hp).symm⟩
    rw [hi, ncE_side₁ Ω (by omega), ncTopLen_of_pos hp, List.getElem_reverse]
    exact congrArg (fun n : ℝ × ℝ × Net X => n.1) (getElem_congr_idx (by omega))

omit [DecidableEq X] in
private theorem ncE_p1 : (ncE Ω).getD (Ω.side₁.nodes.length + 1) 0 = ncTopLen Ω.side₂ := by
  rcases Nat.eq_zero_or_pos Ω.side₂.nodes.length with hq | hq
  · have := ncE_last Ω
    rw [hq, add_zero] at this
    rw [this, ncTopLen_of_nil (List.length_eq_zero_iff.1 hq)]
  · have := ncE_side₂ Ω (j := 0) hq
    rw [add_zero] at this
    rw [this, ncTopLen_of_pos hq]

private theorem nc_card_filter_le_one {pos : Fin 4 → ℕ} (hinj : Function.Injective pos) (h : ℕ) :
    #(univ.filter fun l => pos l = h) ≤ 1 :=
  card_le_one.2 fun _ ha _ hb => hinj ((mem_filter.1 ha).2.trans (mem_filter.1 hb).2.symm)

private theorem nc_card_roots_posForest {pos : Fin 4 → ℕ} (hinj : Function.Injective pos)
    (h : ℕ) : #(roots (posForest pos h)) ≤ 1 :=
  (card_le_card (filter_subset _ _)).trans (card_image_le.trans (nc_card_filter_le_one hinj h))

private theorem nc_single_posForest {pos : Fin 4 → ℕ} (hinj : Function.Injective pos) (h : ℕ)
    (t : ℝ) :
    Pi.single (posForest pos h) 1 ᵥ* kingmanTransition t = Pi.single (posForest pos h) 1 :=
  single_vecMul_kingmanTransition (isGoodForest_singletons _).1 (nc_card_roots_posForest hinj h) t

private theorem nc_posForest_cases {pos : Fin 4 → ℕ} (hinj : Function.Injective pos) (h : ℕ) :
    posForest pos h = ∅ ∨ ∃ l, posForest pos h = {{l}} := by
  obtain ⟨l, hl⟩ := card_le_one_iff_subset_singleton.1 (nc_card_filter_le_one hinj h)
  rcases subset_singleton_iff.1 hl with he | he
  · left; unfold posForest; rw [he, image_empty]
  · right; exact ⟨l, by unfold posForest; rw [he, image_singleton]⟩

private theorem nc_posForest_congr {pos pos' : Fin 4 → ℕ} {h : ℕ}
    (hpos : ∀ l, pos' l = h ↔ pos l = h) : posForest pos' h = posForest pos h := by
  unfold posForest
  congr 1
  ext l
  simp [hpos]

/-- A network hanging from the cycle (or below its hybrid node), the component at position `h`:
at most one lineage is sampled from it, and it reaches the cycle unchanged. -/
private theorem nc_pendant_dist (s : Fin 4 → X) {pos : Fin 4 → ℕ}
    (hinj : Function.Injective pos) (hcomp : ∀ l h, s l ∈ Ω.component h ↔ pos l = h)
    {M : Net X} {h : ℕ} (hMh : Ω.component h = M.taxa) (t : ℝ) :
    M.forestDist s ᵥ* kingmanTransition t = Pi.single (posForest pos h) 1 := by
  have hT : (univ.filter fun l => s l ∈ M.taxa) = univ.filter fun l => pos l = h := by
    ext l
    simp only [mem_filter, mem_univ, true_and, ← hMh, hcomp]
  rw [Net.forestDist_of_card_le_one M s (hT ▸ nc_card_filter_le_one hinj h)]
  have hF : M.sampledForest s = posForest pos h := by
    unfold Net.sampledForest posForest
    rw [hT]
  rw [hF, nc_single_posForest hinj h t]

/-- The side `side₁` is the left arm `0, 1, …, p` of the displayed tree. -/
private theorem nc_side₁_eq_leftArm (s : Fin 4 → X)
    {pos pos' : Fin 4 → ℕ} (hinj : Function.Injective pos)
    (hcomp : ∀ l h, s l ∈ Ω.component h ↔ pos l = h)
    (hpos : ∀ l h, 1 ≤ h → h < Ω.size → (pos' l = h ↔ pos l = h)) :
    Ω.side₁.forestDist s (posForest pos' 0) =
      leftArm Ω.side₁.nodes.length Ω.edgeLen (ncTopLen Ω.side₁) pos' := by
  have hpd : Ω.side₁.nodes.length < Ω.size := by
    by_cases h : Ω.top = N
    · rw [Net.Cycle.size_of_top_eq Ω h]; omega
    · rw [Net.Cycle.size_of_top_ne Ω h]; omega
  rw [Side.forestDist_eq_armDist]
  unfold leftArm
  congr 1
  · congr 2
    split_ifs with hp
    · exact (ncTopLen_of_nil (List.length_eq_zero_iff.1 hp)).symm
    · rw [nc_edgeLen_of_lt Ω (Nat.pos_of_ne_zero hp), ncE_zero]
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    have hi : i < Ω.side₁.nodes.length := by simpa using h2
    simp only [List.getElem_map, List.getElem_range]
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [nc_pendant_dist Ω s hinj hcomp (Net.Cycle.component_side₁ Ω hi),
        nc_posForest_congr (fun l => hpos l (i + 1) (by omega) (by omega))]
    · dsimp only
      split_ifs with hip
      · rw [ncTopLen_of_pos (by omega), List.getElem_reverse]
        exact congrArg (fun n : ℝ × ℝ × Net X => n.1) (getElem_congr_idx (by omega))
      · rw [nc_edgeLen_of_lt Ω (by omega), ncE_side₁ Ω hi]

/-- The side `side₂` is the right arm `d, d - 1, …, d - q` of the displayed tree. -/
private theorem nc_side₂_eq_rightArm (s : Fin 4 → X)
    {pos pos' : Fin 4 → ℕ} (hinj : Function.Injective pos)
    (hcomp : ∀ l h, s l ∈ Ω.component h ↔ pos l = h)
    (hpos : ∀ l h, 1 ≤ h → h < Ω.size → (pos' l = h ↔ pos l = h)) :
    Ω.side₂.forestDist s (posForest pos' Ω.size) =
      rightArm Ω.size Ω.side₂.nodes.length Ω.edgeLen (ncTopLen Ω.side₂) pos' := by
  have hqd : Ω.side₂.nodes.length + Ω.side₁.nodes.length + 1 ≤ Ω.size := by
    by_cases h : Ω.top = N
    · rw [Net.Cycle.size_of_top_eq Ω h]; omega
    · rw [Net.Cycle.size_of_top_ne Ω h]; omega
  rw [Side.forestDist_eq_armDist]
  unfold rightArm
  congr 1
  · congr 2
    split_ifs with hq
    · exact (ncTopLen_of_nil (List.length_eq_zero_iff.1 hq)).symm
    · by_cases h : Ω.top = N
      · have hs := Net.Cycle.size_of_top_eq Ω h
        have hm : Ω.side₁.nodes.length < Ω.size - 1 := by omega
        rw [nc_edgeLen_of_eq_of_gt Ω h hm,
          show Ω.size - 1 + 1 = Ω.side₁.nodes.length + Ω.side₂.nodes.length + 1 by omega,
          ncE_last]
      · have hs := Net.Cycle.size_of_top_ne Ω h
        rw [nc_edgeLen_of_ne Ω h,
          show Ω.size - 1 = Ω.side₁.nodes.length + Ω.side₂.nodes.length + 1 by omega, ncE_last]
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    have hi : i < Ω.side₂.nodes.length := by simpa using h2
    simp only [List.getElem_map, List.getElem_range]
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [nc_pendant_dist Ω s hinj hcomp (Net.Cycle.component_side₂ Ω hi),
        nc_posForest_congr (fun l => hpos l (Ω.size - (i + 1)) (by omega) (by omega))]
    · dsimp only
      split_ifs with hiq
      · rw [ncTopLen_of_pos (by omega), List.getElem_reverse]
        exact congrArg (fun n : ℝ × ℝ × Net X => n.1) (getElem_congr_idx (by omega))
      · rw [List.getElem_reverse]
        have hj : Ω.side₂.nodes.length - 1 - i < Ω.side₂.nodes.length := by omega
        by_cases h : Ω.top = N
        · have hs := Net.Cycle.size_of_top_eq Ω h
          have hm : Ω.side₁.nodes.length < Ω.size - (i + 1) - 1 := by omega
          rw [nc_edgeLen_of_eq_of_gt Ω h hm,
            show Ω.size - (i + 1) - 1 + 1 =
              Ω.side₁.nodes.length + 1 + (Ω.side₂.nodes.length - 1 - i) by omega,
            ncE_side₂ Ω hj]
        · have hs := Net.Cycle.size_of_top_ne Ω h
          rw [nc_edgeLen_of_ne Ω h,
            show Ω.size - (i + 1) - 1 =
              Ω.side₁.nodes.length + 1 + (Ω.side₂.nodes.length - 1 - i) by omega,
            ncE_side₂ Ω hj]

/-- The shape of the displayed trees of `Ω`, as `Phylogenetics.displayed_score` takes it: the top node
is a node of the path (the root component hangs there) or lies inside its edge `p`. -/
private theorem nc_rv : ∃ rv : Bool,
    Ω.size = Ω.side₁.nodes.length + Ω.side₂.nodes.length + 1 + (if rv then 1 else 0) ∧
    (if rv then ncTopLen Ω.side₁ = Ω.edgeLen Ω.side₁.nodes.length ∧
        ncTopLen Ω.side₂ = Ω.edgeLen (Ω.side₁.nodes.length + 1)
      else ncTopLen Ω.side₁ + ncTopLen Ω.side₂ = Ω.edgeLen Ω.side₁.nodes.length) := by
  by_cases h : Ω.top = N
  · refine ⟨false, by simp [Net.Cycle.size_of_top_eq Ω h], ?_⟩
    simp only [Bool.false_eq_true, ite_false]
    rw [nc_edgeLen_of_eq_p Ω h, ncE_p, ncE_p1]
  · refine ⟨true, by simp [Net.Cycle.size_of_top_ne Ω h], ?_⟩
    simp only [ite_true]
    rw [nc_edgeLen_of_ne Ω h, nc_edgeLen_of_ne Ω h, ncE_p, ncE_p1]
    exact ⟨rfl, rfl⟩

/-- The expected score at the top node of the cycle, for one lineage from each of four distinct
components: the two placements of the lineage of the hybrid component. -/
private theorem nc_sum_top (hN : N.leaves.Nodup) (s : Fin 4 → X) {pos : Fin 4 → ℕ}
    (hinj : Function.Injective pos) (hlt : ∀ l, pos l < Ω.size)
    (hs : ∀ l, s l ∈ Ω.component (pos l)) :
    ∑ F, Ω.top.forestDist s F * quartetScore F =
      Ω.γ * pathCF Ω.edgeLen (pos 0) (pos 1) (pos 2) (pos 3) +
        (1 - Ω.γ) * pathCF Ω.edgeLen (toRightEnd Ω.size (pos 0)) (toRightEnd Ω.size (pos 1))
          (toRightEnd Ω.size (pos 2)) (toRightEnd Ω.size (pos 3)) := by
  have hcomp : ∀ l h, s l ∈ Ω.component h ↔ pos l = h := fun l h =>
    ⟨fun hm => by
      by_contra hne
      exact disjoint_left.1 (Net.Cycle.component_disjoint Ω hN hne) (hs l) hm,
     fun he => he ▸ hs l⟩
  -- the placement of the lineage of the hybrid component on the side of `C_{d-1}`
  set pos' : Fin 4 → ℕ := fun l => toRightEnd Ω.size (pos l) with hpos'
  have hinj' : Function.Injective pos' := by
    intro a b hab
    apply hinj
    have ha := hlt a
    have hb := hlt b
    simp only [hpos', toRightEnd] at hab
    split_ifs at hab <;> omega
  have hpos'h : ∀ l h, 1 ≤ h → h < Ω.size → (pos' l = h ↔ pos l = h) := by
    intro l h h1 h2
    simp only [hpos', toRightEnd]
    split_ifs <;> omega
  have hle' : ∀ l, pos' l ≤ Ω.size := by
    intro l
    have := hlt l
    simp only [hpos', toRightEnd]
    split_ifs <;> omega
  -- the forests entering the two arms at their lower ends
  have hE0 : posForest pos' 0 = ∅ := by
    unfold posForest
    rw [filter_false_of_mem (fun l _ => ?_), image_empty]
    have := hlt l
    simp only [hpos', toRightEnd]
    split_ifs <;> omega
  have hEd : posForest pos Ω.size = ∅ := by
    unfold posForest
    rw [filter_false_of_mem (fun l _ => (hlt l).ne), image_empty]
  have hEd' : posForest pos' Ω.size = posForest pos 0 := by
    unfold posForest
    congr 1
    ext l
    have := hlt l
    simp only [mem_filter, mem_univ, true_and, hpos', toRightEnd]
    split_ifs <;> omega
  -- the cycle: the hybrid component sends at most one lineage
  have hbelow : Ω.below.forestDist s ᵥ* kingmanTransition Ω.ℓ =
      Pi.single (posForest pos 0) 1 :=
    nc_pendant_dist Ω s hinj hcomp (Net.Cycle.component_zero Ω) Ω.ℓ
  have htop : Ω.top.forestDist s =
      Ω.γ • forestUnion (Ω.side₁.forestDist s (posForest pos 0)) (Ω.side₂.forestDist s ∅) +
        (1 - Ω.γ) • forestUnion (Ω.side₁.forestDist s ∅)
          (Ω.side₂.forestDist s (posForest pos 0)) :=
    Net.forestDist_cycle_of_single s Ω.γ Ω.ℓ Ω.side₁ Ω.side₂ Ω.below _
      (nc_posForest_cases hinj 0) hbelow
  -- the two displayed trees
  obtain ⟨rv, hdrv, ht⟩ := nc_rv Ω
  have A1 := displayed_score _ _ _ rv hdrv _ _ _ ht pos hinj (fun l => (hlt l).le)
  rw [← nc_side₁_eq_leftArm Ω s hinj hcomp (fun _ _ _ _ => Iff.rfl),
    ← nc_side₂_eq_rightArm Ω s hinj hcomp (fun _ _ _ _ => Iff.rfl), hEd] at A1
  have A2 := displayed_score _ _ _ rv hdrv _ _ _ ht pos' hinj' hle'
  rw [← nc_side₁_eq_leftArm Ω s hinj hcomp hpos'h,
    ← nc_side₂_eq_rightArm Ω s hinj hcomp hpos'h, hE0, hEd'] at A2
  rw [htop]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc, sum_add_distrib,
    ← mul_sum]
  rw [A1, A2]

end Arms

/-- The quartet CF of four taxa `s 0, …, s 3` in four distinct components of a cycle `Ω`, at the
positions `pos l`, is the CF of the induced metric quarnet: the `γ`-mixture of the CFs of the
quartet trees that the positions induce on the path `0 — 1 — ⋯ — d` with the hybrid component at
position `0` or at position `d`. (The steps of `Phylogenetics.nmsc_quartetCF` for four given taxa.) -/
theorem quartetCF_eq_of_components {X : Type u} [DecidableEq X] (N : Net X) (hN : N.WellFormed)
    (Ω : N.Cycle) (s : Fin 4 → X) {pos : Fin 4 → ℕ} (hinj : Function.Injective pos)
    (hlt : ∀ l, pos l < Ω.size) (hs : ∀ l, s l ∈ Ω.component (pos l)) :
    N.quartetCF (s 0) (s 1) (s 2) (s 3) =
      Ω.γ * pathCF Ω.edgeLen (pos 0) (pos 1) (pos 2) (pos 3) +
        (1 - Ω.γ) * pathCF Ω.edgeLen (toRightEnd Ω.size (pos 0)) (toRightEnd Ω.size (pos 1))
          (toRightEnd Ω.size (pos 2)) (toRightEnd Ω.size (pos 3)) := by
  have hcomp : ∀ l h, s l ∈ Ω.component h ↔ pos l = h := fun l h =>
    ⟨fun hm => by
      by_contra hne
      exact disjoint_left.1 (Net.Cycle.component_disjoint Ω hN.2 hne) (hs l) hm,
     fun he => he ▸ hs l⟩
  have hsN : ∀ l, s l ∈ N.taxa := fun l => nc_component_subset Ω _ (hs l)
  have h3 : 3 ≤ #(univ.filter fun l => s l ∈ Ω.top.taxa) := by
    have hout : #(univ.filter fun l => ¬ s l ∈ Ω.top.taxa) ≤ 1 := by
      refine (card_le_card fun l hl => ?_).trans
        (nc_card_filter_le_one hinj (Ω.side₁.nodes.length + 1))
      simp only [mem_filter, mem_univ, true_and] at hl ⊢
      by_contra hne
      exact hl (nc_component_subset_top Ω (Or.inr hne) (hs l))
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin 4)))
      (fun l => s l ∈ Ω.top.taxa)
    rw [card_univ, Fintype.card_fin] at this
    omega
  rw [quartetCF_eq_sum_top N hN.2 Ω s hsN h3, nc_sum_top Ω hN.2 s hinj hlt hs]

end External.NMSC
