module

public import Mathlib.Data.List.Range
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Zip
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.List.Pairwise

/-!
# Lists

Facts about the first and last elements of lists, `List.dropLast`, `List.tail`, the pairs of
consecutive elements, and `List.range`.
-/

@[expose] public section

namespace List

theorem toFinset_range (n : ℕ) : (List.range n).toFinset = Finset.range n := by
  ext i
  simp

/-- In `List.range n = K ++ k :: K'`, the elements before `k` are those below `k`. -/
theorem mem_iff_lt_of_range_eq_append_cons {n k : ℕ} {K K' : List ℕ}
    (h : List.range n = K ++ k :: K') (i : ℕ) :
    i ∈ K ↔ i < k := by
  have hpw := List.pairwise_lt_range (n := n)
  rw [h, List.pairwise_append] at hpw
  have hk : k < n := List.mem_range.mp (by rw [h]; simp)
  constructor
  · intro hi
    exact hpw.2.2 i hi k (by simp)
  · intro hik
    have hin : i ∈ List.range n := List.mem_range.mpr (by omega)
    rw [h] at hin
    rcases List.mem_append.mp hin with hK | hK
    · exact hK
    · rcases List.mem_cons.mp hK with rfl | hK'
      · omega
      · have := (List.pairwise_cons.mp hpw.2.1).1 i hK'
        omega

/-- The first components of the pairs of consecutive elements of `l`, in order, form `l` without
its last element. -/
theorem map_fst_zip_tail (l : List ℕ) :
    (l.zip l.tail).map Prod.fst = l.dropLast := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    cases l with
    | nil => rfl
    | cons y l =>
      simpa only [List.tail_cons, List.zip_cons_cons, List.map_cons,
        List.dropLast_cons_cons] using congrArg (List.cons x) ih

/-- The second components of the pairs of consecutive elements of `l`, in order, form `l` without
its first element. -/
theorem map_snd_zip_tail (l : List ℕ) :
    (l.zip l.tail).map Prod.snd = l.tail :=
  List.map_snd_zip (by simp)

/-- In a list without repetition, the first element does not occur again. -/
theorem not_mem_tail_of_head?_eq_some {l : List ℕ} (hl : l.Nodup) {v : ℕ}
    (hv : l.head? = some v) : v ∉ l.tail := by
  cases l with
  | nil => simp at hv
  | cons a l =>
    simp only [List.head?_cons, Option.some.injEq] at hv
    subst v
    exact (List.nodup_cons.mp hl).1

/-- In a list with at least two elements, the first element lies in `l.dropLast`. -/
theorem mem_dropLast_of_head?_eq_some {l : List ℕ} (hlen : 2 ≤ l.length) {v : ℕ}
    (hv : l.head? = some v) : v ∈ l.dropLast := by
  cases l with
  | nil => simp at hlen
  | cons a l =>
    cases l with
    | nil => simp at hlen
    | cons b l =>
      simp only [List.head?_cons, Option.some.injEq] at hv
      subst v
      simp

theorem not_mem_dropLast_of_getLast?_eq_some {L : List ℕ} (hL : L.Nodup) {v : ℕ}
    (hv : L.getLast? = some v) : v ∉ L.dropLast := by
  have hne : L ≠ [] := by intro h; simp [h] at hv
  have hlast : L.getLast hne = v := Option.some.inj
    ((List.getLast?_eq_some_getLast hne).symm.trans hv)
  have hn : (L.dropLast ++ [v]).Nodup := by
    rw [← hlast, List.dropLast_append_getLast hne]
    exact hL
  intro h
  exact (List.nodup_append.mp hn).2.2 _ h _ (by simp) rfl

/-- A list of length at least two with first element `a` and last element `b` is
`a :: (l.tail.dropLast ++ [b])`. -/
theorem eq_cons_tail_dropLast_append {l : List ℕ} (hlen : 2 ≤ l.length) {a b : ℕ}
    (hhead : l.head? = some a) (hlast : l.getLast? = some b) :
    l = a :: (l.tail.dropLast ++ [b]) := by
  cases l with
  | nil => simp at hlen
  | cons x l =>
    cases l with
    | nil => simp at hlen
    | cons y l =>
      simp only [List.head?_cons,Option.some.injEq] at hhead
      subst x
      have htail : (y :: l).getLast? = some b := by simpa using hlast
      exact congrArg (List.cons a) (List.dropLast_append_getLast? b (htail ▸ Option.mem_some_self
          b)).symm

/-- A list without repetition whose first and last elements are `x` is `[x]`. -/
theorem eq_singleton_of_head?_eq_getLast? {L : List ℕ} (hL : L.Nodup) {x : ℕ}
    (hh : L.head? = some x) (hl : L.getLast? = some x) : L = [x] := by
  match L, hL, hh, hl with
  | [a], _, hh, _ =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    rw [hh]
  | a :: b :: rest, hL, hh, hl =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    rw [List.getLast?_cons_cons] at hl
    exact absurd (hh ▸ List.mem_of_getLast? hl) (List.nodup_cons.mp hL).1

/-- The head of a nonempty list is one of its elements. -/
theorem headD_append_singleton_mem (L : List ℕ) (x d : ℕ) :
    (L ++ [x]).headD d ∈ L ++ [x] := by
  cases L <;> simp

/-- A list with at least two elements starts with its first element and a second one. -/
theorem exists_eq_cons_cons_of_head?_eq_some {L : List ℕ} {x : ℕ} (hlen : 2 ≤ L.length)
    (hx : L.head? = some x) :
    ∃ b rest, L = x :: b :: rest := by
  match L, hlen, hx with
  | a :: b :: rest, _, hx =>
    simp only [List.head?_cons, Option.some.injEq] at hx
    exact ⟨b, rest, by rw [hx]⟩

end List
