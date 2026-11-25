module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Logic.Equiv.Fintype

/-!
# Sums over finite types

Regrouping a sum by the fibres of a map; summing out one coordinate of a function; and the total
probability of a Markov chain on a rooted tree.
-/

@[expose] public section

open Finset
open scoped NNReal

namespace Fintype

/-- Regrouping a sum by the image of the summation variable under `R`. -/
theorem sum_ite_comp {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (R : α → β)
    (P : β → Prop) [DecidablePred P] (μ : α → ℝ) :
    ∑ a, (if P (R a) then μ a else 0) =
      ∑ b, if P b then ∑ a, (if R a = b then μ a else 0) else 0 := by
  rw [← Finset.sum_fiberwise univ R]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_filter]
  split_ifs with hb
  · refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : R a = b
    · rw [ite_eq_left ha, ite_eq_left ha, ite_eq_left (ha ▸ hb)]
    · rw [ite_eq_right ha, ite_eq_right ha]
  · refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : R a = b
    · rw [ite_eq_left ha, ite_eq_right (ha ▸ hb)]
    · rw [ite_eq_right ha]

section

variable {V σ : Type*} [Fintype V] [DecidableEq V] [Fintype σ]

/-- Summing out the state at one vertex `b`: if `G`, `k₁` and `k₂` do not depend on the state at
`b`, and the rows `k₁ f` and `k₂ f` have the same total, then weighting `G` by `k₁` or by `k₂` at
the state of `b` gives the same sum over the state functions `f`. -/
theorem sum_mul_eq_of_update (b : V) (G : (V → σ) → ℝ≥0)
    (k₁ k₂ : (V → σ) → σ → ℝ≥0)
    (hG : ∀ f s, G (Function.update f b s) = G f)
    (hk₁ : ∀ f s, k₁ (Function.update f b s) = k₁ f)
    (hk₂ : ∀ f s, k₂ (Function.update f b s) = k₂ f)
    (hk : ∀ f, ∑ s, k₁ f s = ∑ s, k₂ f s) :
    ∑ f, G f * k₁ f (f b) = ∑ f, G f * k₂ f (f b) := by
  rcases isEmpty_or_nonempty σ with hσ | ⟨⟨s₀⟩⟩
  · have : IsEmpty (V → σ) := ⟨fun f => hσ.false (f b)⟩
    simp
  let e := Equiv.funSplitAt b σ
  -- the state function `e.symm (s, g)` is `e.symm (s₀, g)` with the state at `b` set to `s`
  have hupd : ∀ s g, e.symm (s, g) = Function.update (e.symm (s₀, g)) b s := by
    intro s g
    funext j
    by_cases hj : j = b
    · subst hj
      simp [e, Equiv.funSplitAt_symm_apply]
    · simp [e, Equiv.funSplitAt_symm_apply, hj]
  have hb : ∀ s g, e.symm (s, g) b = s := by
    intro s g
    simp [e, Equiv.funSplitAt_symm_apply]
  -- both sides are sums over the other states of `G` times the total of `k₁` or `k₂`
  have key : ∀ k : (V → σ) → σ → ℝ≥0, (∀ f s, k (Function.update f b s) = k f) →
      ∑ f, G f * k f (f b) =
        ∑ g : {j // j ≠ b} → σ, G (e.symm (s₀, g)) * ∑ s, k (e.symm (s₀, g)) s := by
    intro k hk
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hb, hupd, hG, hk]
  rw [key k₁ hk₁, key k₂ hk₂]
  exact Finset.sum_congr rfl fun g _ => by rw [hk]

/-- A Markov chain on a rooted tree: the tree is given by its edge set `E`, in which every vertex
other than the root `r` is the head of exactly one edge and the root of none, and `rank`
increases along the edges. The root state has law `π`, and the state at the head of each edge `e`
is drawn from the row `K e` of the state at its tail. Then the probabilities of the state
functions sum to 1. -/
theorem sum_markov_tree (E : Finset (V × V)) (r : V) (rank : V → ℕ)
    (hrank : ∀ e ∈ E, rank e.1 < rank e.2)
    (hhead : ∀ e ∈ E, ∀ e' ∈ E, e.2 = e'.2 → e = e')
    (hroot : ∀ e ∈ E, e.2 ≠ r)
    (hcover : ∀ v, v ≠ r → ∃ e ∈ E, e.2 = v)
    (π : σ → ℝ≥0) (hπ : ∑ s, π s = 1) (K : V × V → σ → σ → ℝ≥0)
    (hK : ∀ e ∈ E, ∀ s, ∑ s', K e s s' = 1) :
    ∑ f : V → σ, π (f r) * ∏ e ∈ E, K e (f e.1) (f e.2) = 1 := by
  classical
  -- the vertices other than the root that are the head of no edge of `F` get the law `π`
  let free : Finset (V × V) → Finset V := fun F =>
    univ.filter fun v => v ≠ r ∧ ∀ e ∈ F, e.2 ≠ v
  have claim : ∀ n, ∀ F ⊆ E, F.card = n →
      ∑ f : V → σ, π (f r) * (∏ e ∈ F, K e (f e.1) (f e.2)) * ∏ v ∈ free F, π (f v) = 1 := by
    intro n
    induction n with
    | zero =>
      intro F _ hF
      rw [Finset.card_eq_zero.mp hF]
      have hfree : free ∅ = univ.erase r := by
        ext v
        simp [free]
      simp only [Finset.prod_empty, mul_one, hfree]
      calc ∑ f : V → σ, π (f r) * ∏ v ∈ univ.erase r, π (f v)
          = ∑ f : V → σ, ∏ v, π (f v) := by
            refine Finset.sum_congr rfl fun f _ => ?_
            rw [Finset.mul_prod_erase _ (fun v => π (f v)) (Finset.mem_univ r)]
        _ = ∏ _v : V, ∑ s, π s := (Fintype.prod_sum fun _ s => π s).symm
        _ = 1 := by simp [hπ]
    | succ n ih =>
      intro F hFE hF
      have hne : F.Nonempty := Finset.card_pos.mp (by omega)
      -- remove an edge whose head has the largest rank
      obtain ⟨e₀, he₀, hmax⟩ := Finset.exists_max_image F (fun e => rank e.2) hne
      set a := e₀.1
      set b := e₀.2
      have hab : a ≠ b := fun h => by
        have := hrank e₀ (hFE he₀)
        rw [show e₀.1 = e₀.2 from h] at this
        exact lt_irrefl _ this
      have hbr : b ≠ r := hroot e₀ (hFE he₀)
      set F' := F.erase e₀
      have hF' : F'.card = n := by
        rw [Finset.card_erase_of_mem he₀]
        omega
      have hheadF' : ∀ e ∈ F', e.2 ≠ b := by
        intro e he heb
        exact (Finset.mem_erase.mp he).1 (hhead e (hFE (Finset.mem_of_mem_erase he)) e₀
          (hFE he₀) heb)
      have htailF' : ∀ e ∈ F', e.1 ≠ b := by
        intro e he heb
        have h1 := hrank e (hFE (Finset.mem_of_mem_erase he))
        have h2 := hmax e (Finset.mem_of_mem_erase he)
        rw [heb] at h1
        exact absurd h2 (not_le.mpr h1)
      have hfree : free F' = insert b (free F) := by
        ext v
        simp only [free, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨hvr, hv⟩
          by_cases hvb : v = b
          · exact Or.inl hvb
          · refine Or.inr ⟨hvr, fun e he hev => ?_⟩
            by_cases hee : e = e₀
            · exact hvb (by subst hee; exact hev.symm)
            · exact hv e (Finset.mem_erase.mpr ⟨hee, he⟩) hev
        · rintro (rfl | ⟨hvr, hv⟩)
          · exact ⟨hbr, hheadF'⟩
          · exact ⟨hvr, fun e he => hv e (Finset.mem_of_mem_erase he)⟩
      have hbfree : b ∉ free F := by
        simp only [free, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_forall]
        exact fun _ => ⟨e₀, he₀, fun h => h rfl⟩
      -- the part of the summand that does not involve the state at `b`
      let G : (V → σ) → ℝ≥0 := fun f =>
        π (f r) * (∏ e ∈ F', K e (f e.1) (f e.2)) * ∏ v ∈ free F, π (f v)
      have hG : ∀ f s, G (Function.update f b s) = G f := by
        intro f s
        have h1 : Function.update f b s r = f r := Function.update_of_ne hbr.symm _ _
        have h2 : ∏ e ∈ F', K e (Function.update f b s e.1) (Function.update f b s e.2) =
            ∏ e ∈ F', K e (f e.1) (f e.2) := by
          refine Finset.prod_congr rfl fun e he => ?_
          rw [Function.update_of_ne (htailF' e he), Function.update_of_ne (hheadF' e he)]
        have h3 : ∏ v ∈ free F, π (Function.update f b s v) = ∏ v ∈ free F, π (f v) := by
          refine Finset.prod_congr rfl fun v hv => ?_
          have hvb : v ≠ b := fun h => hbfree (by rw [← h]; exact hv)
          rw [Function.update_of_ne hvb]
        simp only [G, h1, h2, h3]
      -- summing out the state at `b` replaces the row of `e₀` by the law `π`
      have hstep :=
        Fintype.sum_mul_eq_of_update b G (fun f s => K e₀ (f a) s) (fun _ s => π s) hG
        (fun f s => by rw [Function.update_of_ne hab]) (fun _ _ => rfl)
        (fun f => by rw [hK e₀ (hFE he₀), hπ])
      calc ∑ f : V → σ, π (f r) * (∏ e ∈ F, K e (f e.1) (f e.2)) * ∏ v ∈ free F, π (f v)
          = ∑ f : V → σ, G f * K e₀ (f a) (f b) := by
            refine Finset.sum_congr rfl fun f _ => ?_
            simp only [G]
            rw [← Finset.mul_prod_erase F _ he₀]
            ring
        _ = ∑ f : V → σ, G f * π (f b) := hstep
        _ = ∑ f : V → σ, π (f r) * (∏ e ∈ F', K e (f e.1) (f e.2)) *
              ∏ v ∈ free F', π (f v) := by
            refine Finset.sum_congr rfl fun f _ => ?_
            simp only [G]
            rw [hfree, Finset.prod_insert hbfree]
            ring
        _ = 1 := ih F' ((Finset.erase_subset _ _).trans hFE) hF'
  -- with `F = E`, every vertex other than the root is the head of an edge
  have hfreeE : free E = ∅ := by
    ext v
    simp only [free, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_and, not_forall, not_not]
    intro hvr
    obtain ⟨e, he, hev⟩ := hcover v hvr
    exact ⟨e, he, hev⟩
  have h := claim E.card E (Finset.Subset.refl _) rfl
  simpa only [hfreeE, Finset.prod_empty, mul_one] using h

end

end Fintype
