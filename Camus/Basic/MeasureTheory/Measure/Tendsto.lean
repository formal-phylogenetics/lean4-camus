module

public import Mathlib.Probability.Notation
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Order.Basic
public import Mathlib.MeasureTheory.Measure.Basic

/-!
# Events that hold eventually, almost surely

Events that hold, almost surely, for all large indices have probability tending to `1`.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Events that hold, almost surely, for all large `m` have probability tending to 1. -/
theorem tendsto_measure_of_ae_eventually {P : Measure Ω} [IsProbabilityMeasure P]
    {A : ℕ → Set Ω} (h : ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ω ∈ A m) :
    Tendsto (fun m => P (A m)) atTop (𝓝 1) := by
  -- the events "`A k` for all `k ≥ m`" increase to an event of probability 1
  let B : ℕ → Set Ω := fun m => {ω | ∀ k ≥ m, ω ∈ A k}
  have hmono : Monotone B := fun m m' hmm' ω hω k hk => hω k (hmm'.trans hk)
  have hunion : P (⋃ m, B m) = 1 := by
    refine le_antisymm prob_le_one ?_
    have hnull : P {ω | ¬ ∀ᶠ m in atTop, ω ∈ A m} = 0 := ae_iff.mp h
    calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
      _ ≤ P ((⋃ m, B m) ∪ {ω | ¬ ∀ᶠ m in atTop, ω ∈ A m}) := by
        refine measure_mono fun ω _ => ?_
        by_cases hω : ∀ᶠ m in atTop, ω ∈ A m
        · obtain ⟨m, hm⟩ := eventually_atTop.mp hω
          exact Or.inl (Set.mem_iUnion.mpr ⟨m, hm⟩)
        · exact Or.inr hω
      _ ≤ P (⋃ m, B m) + P {ω | ¬ ∀ᶠ m in atTop, ω ∈ A m} := measure_union_le _ _
      _ = P (⋃ m, B m) := by rw [hnull, add_zero]
  have hB : Tendsto (fun m => P (B m)) atTop (𝓝 1) := by
    rw [← hunion]
    exact tendsto_measure_iUnion_atTop hmono
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hB tendsto_const_nhds
    (fun m => measure_mono fun ω hω => hω m le_rfl) fun _ => prob_le_one

end MeasureTheory
