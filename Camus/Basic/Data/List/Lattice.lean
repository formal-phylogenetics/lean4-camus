module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.WithBot
public import Mathlib.Order.Lattice.Nat

/-!
# Loops that take suprema

A loop over a list that keeps the larger value computes the supremum over the elements of the list.
-/

@[expose] public section

namespace List

/-- A loop keeping the larger value computes the supremum over the elements of the list. -/
theorem foldl_sup_eq_sup_sup {α : Type} [DecidableEq α] (f : α → WithBot ℕ) (l : List α)
    (a : WithBot ℕ) :
    l.foldl (fun acc x => acc ⊔ f x) a = a ⊔ l.toFinset.sup f := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons, ih, List.toFinset_cons, Finset.sup_insert, sup_assoc]

end List
