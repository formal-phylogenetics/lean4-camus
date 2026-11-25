module

public import Mathlib.Logic.Relation
public import Mathlib.Data.Finset.Basic

/-!
# Reachability along a set of pairs

The reflexive transitive closure of the relation `(a, b) ∈ S` of a finite set `S` of pairs: when
the only pair into `v`, or none, is known, and after exchanging a pair for another with the same
second coordinate.
-/

@[expose] public section

namespace Relation

/-- If the only edge of `S` into `v` comes from `p`, then `v` is reached from `y` along `S` iff
`y = v` or `p` is reached from `y`. -/
theorem reflTransGen_mem_iff_of_incoming {S : Finset (ℕ × ℕ)} {v p : ℕ}
    (hin : ∀ z, (z, v) ∈ S ↔ z = p) (y : ℕ) :
    Relation.ReflTransGen (fun a b => (a, b) ∈ S) y v ↔
      y = v ∨ Relation.ReflTransGen (fun a b => (a, b) ∈ S) y p := by
  constructor
  · intro h
    rcases h.cases_tail with h | ⟨c, hc, hcv⟩
    · exact Or.inl h.symm
    · exact Or.inr ((hin c).mp hcv ▸ hc)
  · rintro (rfl | h)
    · exact .refl
    · exact h.tail ((hin p).mpr rfl)

/-- If no edge of `S` enters `v`, then `v` is reached from `y` along `S` only if `y = v`. -/
theorem reflTransGen_mem_iff_of_no_incoming {S : Finset (ℕ × ℕ)} {v : ℕ}
    (hin : ∀ z, (z, v) ∉ S) (y : ℕ) :
    Relation.ReflTransGen (fun a b => (a, b) ∈ S) y v ↔ y = v := by
  constructor
  · intro h
    rcases h.cases_tail with h | ⟨c, _, hcv⟩
    · exact h.symm
    · exact absurd hcv (hin c)
  · rintro rfl
    exact .refl

section

variable {S : Finset (ℕ × ℕ)} {g d : ℕ × ℕ}

/-- After the exchange of `g` for `d`, the vertices reached from the common head `d.2` are those
reached before: a path from `d.2` never uses an edge into `d.2`. -/
theorem reflTransGen_exchange_head (hgd : g.2 = d.2) {x : ℕ} :
    Relation.ReflTransGen (fun u v => (u, v) ∈ insert d (S.erase g)) d.2 x ↔
      Relation.ReflTransGen (fun u v => (u, v) ∈ S) d.2 x := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y x _ hyx ih =>
      rcases Finset.mem_insert.1 hyx with h | h
      · obtain rfl : x = d.2 := congrArg Prod.snd h
        exact .refl
      · exact ih.tail (Finset.mem_of_mem_erase h)
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y x _ hyx ih =>
      by_cases hg' : (y, x) = g
      · obtain rfl : x = d.2 := (congrArg Prod.snd hg').trans hgd
        exact .refl
      · exact ih.tail (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hg', hyx⟩))

/-- After the exchange of `g` for `d`, a vertex not reached from `d.2` is reached from `v` iff it
was before: a path to it uses neither edge into `d.2`. -/
theorem reflTransGen_exchange_outside (hgd : g.2 = d.2) {v x : ℕ}
    (hx : ¬Relation.ReflTransGen (fun u v => (u, v) ∈ S) d.2 x) :
    Relation.ReflTransGen (fun u v => (u, v) ∈ insert d (S.erase g)) v x ↔
      Relation.ReflTransGen (fun u v => (u, v) ∈ S) v x := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y x _ hyx ih =>
      rcases Finset.mem_insert.1 hyx with h | h
      · obtain rfl : x = d.2 := congrArg Prod.snd h
        exact absurd .refl hx
      · have hyS := Finset.mem_of_mem_erase h
        exact (ih fun hy => hx (hy.tail hyS)).tail hyS
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y x _ hyx ih =>
      by_cases hg' : (y, x) = g
      · obtain rfl : x = d.2 := (congrArg Prod.snd hg').trans hgd
        exact absurd .refl hx
      · exact (ih fun hy => hx (hy.tail hyx)).tail
          (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hg', hyx⟩))

end

end Relation
