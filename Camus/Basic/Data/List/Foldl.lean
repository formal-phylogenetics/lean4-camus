module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Order.WithBot
public import Mathlib.Tactic.Ring
public import Mathlib.Data.List.Range
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Union

/-!
# Loops over lists

Folds of lists as the loops of a program: an invariant along a loop, and the values of the loops
that sum, take maxima, count, prepend, or update a function at a list of keys.
-/

@[expose] public section

namespace List

section

variable {α β σ : Type}

theorem sum_map_const_eq_length_mul (l : List α) (c : ℕ) :
    (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; ring

theorem foldl_add_eq_add_sum (g : α → ℕ) (l : List α) (s : ℕ) :
    l.foldl (fun acc a => acc + g a) s = s + (l.map g).sum := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

theorem foldl_max_eq_max_sup [DecidableEq α] (g : α → ℕ) (l : List α) (s : ℕ) :
    l.foldl (fun acc a => max acc (g a)) s = max s (l.toFinset.sup g) := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons, ih, List.toFinset_cons, Finset.sup_insert]
    simp only [max_assoc]

end

section

variable {α κ β : Type} [DecidableEq κ]

/-- After a loop of updates, a key that no element updates keeps its value. -/
theorem foldl_update_of_forall_ne (key : α → κ) (v : α → β) (l : List α) (f : κ → β)
    {k : κ}
    (hk : ∀ a ∈ l, key a ≠ k) :
    (l.foldl (fun f a => Function.update f (key a) (v a)) f) k = f k := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun b hb => hk b (by simp [hb]))]
    exact Function.update_of_ne (hk a (by simp)).symm _ _

/-- After a loop of updates with distinct keys, the key of `x` holds the value of `x`. -/
theorem foldl_update_of_mem (key : α → κ) (v : α → β) (l : List α) (f : κ → β)
    (hl : (l.map key).Nodup) {x : α} (hx : x ∈ l) :
    (l.foldl (fun f a => Function.update f (key a) (v a)) f) (key x) = v x := by
  induction l generalizing f with
  | nil => simp at hx
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hl
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [List.foldl_update_of_forall_ne key v l _ (fun b hb h => hl.1 ⟨b, hb, h⟩)]
      simp
    · exact ih _ hl.2 hx

end

/-- Induction along a loop: if `P` holds before the loop, and each iteration on an element `a` of
`l = A ++ a :: B` takes a state satisfying `P A` to one satisfying `P (A ++ [a])`, then the state
after the loop satisfies `P l`. -/
theorem foldl_invariant {α σ : Type*} (l : List α) (step : σ → α → σ)
    (P : List α → σ → Prop)
    {s : σ} (h0 : P [] s)
    (hstep : ∀ A a B s, l = A ++ a :: B → P A s → P (A ++ [a]) (step s a)) :
    P l (l.foldl step s) := by
  have key : ∀ (B A : List α) (s : σ), l = A ++ B → P A s → P l (B.foldl step s) := by
    intro B
    induction B with
    | nil => intro A s hl hs; simpa [hl] using hs
    | cons a B ih =>
      intro A s hl hs
      exact ih (A ++ [a]) (step s a) (by simp [hl]) (hstep A a B s hl hs)
  exact key l [] s (by simp) h0

/-- Prepending in a loop. -/
theorem foldl_prepend_append {α β : Type} (f : α → List β) (L : List α) (a c : List β) :
    L.foldl (fun acc r => f r ++ acc) (a ++ c) = L.foldl (fun acc r => f r ++ acc) a ++ c := by
  induction L generalizing a with
  | nil => rfl
  | cons r L ih =>
    simp only [List.foldl_cons]
    rw [← List.append_assoc, ih]

theorem toFinset_foldl_prepend {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → List β)
    (L : List α) (a : List β) :
    (L.foldl (fun acc r => f r ++ acc) a).toFinset =
      a.toFinset ∪ L.toFinset.biUnion fun r => (f r).toFinset := by
  induction L generalizing a with
  | nil => simp
  | cons r L ih =>
    simp only [List.foldl_cons, ih, List.toFinset_append, List.toFinset_cons,
      Finset.biUnion_insert]
    ext x
    simp only [Finset.mem_union]
    tauto

/-- The length of a list grown by prepending in a loop. -/
theorem length_foldl_prepend {α β : Type} (f : α → List β) (L : List α) (a : List β) :
    (L.foldl (fun acc r => f r ++ acc) a).length =
      a.length + (L.map fun r => (f r).length).sum := by
  induction L generalizing a with
  | nil => simp
  | cons r L ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.map_cons, List.sum_cons]
    omega

/-- Counting the elements of a list in a loop. -/
theorem foldl_add_one {α : Type} (l : List α) (c : ℕ) :
    l.foldl (fun s _ => s + 1) c = c + l.length := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons, ih, List.length_cons]; omega

/-- A loop of updates at the keys `0, …, j` writes the value of each key. -/
theorem foldl_update_range {β : Type} (f : ℕ → β) (F : ℕ → β) {j i : ℕ}
    (hi : i ≤ j) :
    ((List.range (j + 1)).foldl (fun F i => Function.update F i (f i)) F) i = f i := by
  have h := List.foldl_update_of_mem (fun i => i) f (List.range (j + 1)) F
    (by simpa using List.nodup_range) (List.mem_range.mpr (Nat.lt_succ_of_le hi))
  exact h

/-- A loop of updates at the keys `(c, 0), …, (c, j)` writes the value of each of them and leaves
the other keys unchanged. -/
theorem foldl_update_range_pair {β : Type} (c : ℕ) (f : ℕ → β) (F : ℕ × ℕ → β) (j : ℕ)
    (x : ℕ × ℕ) :
    ((List.range (j + 1)).foldl (fun F b => Function.update F (c, b) (f b)) F) x =
      if x.1 = c ∧ x.2 ≤ j then f x.2 else F x := by
  have hnd : ((List.range (j + 1)).map fun b => (c, b)).Nodup :=
    List.nodup_range.map (fun a b h => (Prod.mk.inj h).2)
  split_ifs with hx
  · obtain ⟨x1, x2⟩ := x
    obtain ⟨rfl, hx2⟩ := hx
    exact List.foldl_update_of_mem (fun b => (x1, b)) f _ F hnd
      (List.mem_range.mpr (Nat.lt_succ_of_le hx2))
  · apply List.foldl_update_of_forall_ne (fun b => (c, b)) f
    intro b hb h
    apply hx
    rw [← h]
    exact ⟨rfl, Nat.lt_succ_iff.mp (List.mem_range.mp hb)⟩

end List
