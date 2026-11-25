module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.BooleanAlgebra.Set

/-!
# Finite sets

Counting the elements of `insert a s` with a property; sets that contain one set and avoid its
complement; a predicate that separates two nonempty sets; the elements of a set of pairs with a
given second coordinate.
-/

@[expose] public section

open Finset

namespace Finset

/-- Counting the elements of `insert a s` with a property. -/
theorem card_filter_insert_eq {α : Type*} [DecidableEq α] {s : Finset α} {a : α}
    (ha : a ∉ s) (p : α → Prop) [DecidablePred p] :
    ((insert a s).filter p).card = (s.filter p).card + if p a then 1 else 0 := by
  rw [Finset.filter_insert]
  split_ifs with h
  · exact Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.mp hm).1)
  · simp

/-- `D` contains `C` and avoids its complement iff `D = C`. -/
theorem subset_and_disjoint_compl_iff {α : Type*} [Fintype α] [DecidableEq α] (C D : Finset α) :
    C ⊆ D ∧ Disjoint Cᶜ D ↔ D = C := by
  constructor
  · rintro ⟨h1, h2⟩
    refine Subset.antisymm (fun i hi => ?_) h1
    by_contra hc
    exact disjoint_left.1 h2 (mem_compl.2 hc) hi
  · rintro rfl
    exact ⟨Subset.rfl, disjoint_compl_left⟩

/-- `D` contains the complement of `C` and avoids `C` iff `D = Cᶜ`. -/
theorem compl_subset_and_disjoint_iff {α : Type*} [Fintype α] [DecidableEq α] (C D : Finset α) :
    Cᶜ ⊆ D ∧ Disjoint C D ↔ D = Cᶜ := by
  have h := Finset.subset_and_disjoint_compl_iff Cᶜ D
  rwa [compl_compl] at h

/-- For nonempty sets `A`, `B` and a predicate `P`: `P` is constant on `A` and on `B`, with
different values on the two, if and only if `P` holds on `A` and fails on `B`, or the reverse. -/
theorem iff_partition_of_nonempty {A B : Finset ℕ} (hA : A.Nonempty) (hB : B.Nonempty)
    (P : ℕ → Prop) :
    ((∀ a ∈ A, ∀ b ∈ A, P a ↔ P b) ∧
      (∀ a ∈ B, ∀ b ∈ B, P a ↔ P b) ∧
      (∀ a ∈ A, ∀ b ∈ B, ¬(P a ↔ P b))) ↔
    ((∀ a ∈ A, P a) ∧ (∀ b ∈ B, ¬P b) ∨
      (∀ a ∈ A, ¬P a) ∧ (∀ b ∈ B, P b)) := by
  classical
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  constructor
  · rintro ⟨hAA, hBB, hAB⟩
    by_cases hPa : P a
    · have hPb : ¬P b := fun hPb => hAB a ha b hb ⟨fun _ => hPb, fun _ => hPa⟩
      exact Or.inl ⟨fun x hx => (hAA a ha x hx).mp hPa,
        fun x hx hPx => hPb ((hBB x hx b hb).mp hPx)⟩
    · have hPb : P b := by
        by_contra h
        exact hAB a ha b hb ⟨fun h => (hPa h).elim, fun h' => (h h').elim⟩
      exact Or.inr ⟨fun x hx hPx => hPa ((hAA x hx a ha).mp hPx),
        fun x hx => (hBB b hb x hx).mp hPb⟩
  · rintro (⟨hA, hB⟩ | ⟨hA, hB⟩)
    · exact ⟨fun a ha b hb => ⟨fun _ => hA b hb, fun _ => hA a ha⟩,
        fun a ha b hb => ⟨fun h => (hB a ha h).elim, fun h => (hB b hb h).elim⟩,
        fun a ha b hb h => hB b hb (h.mp (hA a ha))⟩
    · exact ⟨fun a ha b hb => ⟨fun h => (hA a ha h).elim, fun h => (hA b hb h).elim⟩,
        fun a ha b hb => ⟨fun _ => hB b hb, fun _ => hB a ha⟩,
        fun a ha b hb h => hA a ha (h.mpr (hB b hb))⟩

/-- If the only edge of `S` into `v` comes from `p`, then exactly one edge of `S` enters `v`. -/
theorem card_filter_snd_eq_one {S : Finset (ℕ × ℕ)} {v p : ℕ}
    (hin : ∀ z, (z, v) ∈ S ↔ z = p) : (S.filter (fun f => f.2 = v)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨(p, v), ?_⟩
  ext f
  obtain ⟨z, v'⟩ := f
  simp only [Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hf, rfl⟩
    exact ⟨(hin z).mp hf, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨(hin z).mpr rfl, rfl⟩

end Finset
