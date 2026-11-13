/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestWordMass
public import BGW.StableTrees.DiscreteForestMass
import BGW.Tree.ForestCycle

/-!
# Finite first-passage masses

The finite count-vector law and the sealed forest-code correspondence give the
mass of first passage to any strictly negative integer level.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Classical

namespace BGW.StableTrees.DiscreteForest

/-- First passage to `-j` at time `r`, expressed without a totalized hitting time. -/
def forestHit (j r : ℕ) : Set (ℕ → ℕ) :=
  {ω | walk ω r = -(j : ℤ) ∧ ∀ i < r, -(j : ℤ) < walk ω i}

/-- The first-passage event is a finite count-vector forest-code cylinder. -/
theorem forestHit_eq_preimage (j r : ℕ) :
    forestHit j r = (fun ω (i : Fin r) => ω i) ⁻¹'
      {a | IsForestCode j (BGW.stepWord a)} := by
  ext ω
  change (walk ω r = -(j : ℤ) ∧ ∀ i < r, -(j : ℤ) < walk ω i) ↔
    IsForestCode j (BGW.stepWord (fun i : Fin r => ω i))
  rw [stepWord_initial]
  have hsum (i : ℕ) (hi : i ≤ r) :
      (((seqPrefix r ω).map (fun d : ℕ => (d : ℤ) - 1)).take i).sum = walk ω i := by
    rw [← List.map_take, take_seqPrefix r i ω hi, sum_seqPrefix]
  constructor
  · rintro ⟨he, hpre⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
      omega
    · rwa [sum_seqPrefix]
    · intro i hi
      have hir : i < r := by simpa [seqPrefix] using hi
      rw [hsum i hir.le]
      exact hpre i hir
  · rintro ⟨_, he, hpre⟩
    refine ⟨?_, fun i hi => ?_⟩
    · rwa [sum_seqPrefix] at he
    · have h := hpre i (by simpa [seqPrefix] using hi)
      rwa [hsum i hi.le] at h

/-- First passage is a measurable finite cylinder. -/
theorem measurableSet_forestHit (j r : ℕ) : MeasurableSet (forestHit j r) := by
  rw [forestHit_eq_preimage]
  exact (Set.to_countable _).measurableSet.preimage (by fun_prop)

private theorem forestCode_tsum (p : ℕ → ℝ≥0∞) (j r : ℕ) :
    (∑' x : List ℤ, Set.indicator {x | IsForestCode j x ∧ x.length = r}
      (BGW.walkWeight p) x) =
    ∑' a : Fin r → ℕ, Set.indicator {a | IsForestCode j (BGW.stepWord a)}
      (fun a => ∏ i, p (a i)) a := by
  have hrange : Function.support
      (Set.indicator {x : List ℤ | IsForestCode j x ∧ x.length = r} (BGW.walkWeight p)) ⊆
      Set.range (BGW.stepWord (n := r)) := by
    intro x hx
    by_contra hr
    apply hx
    have hnot : x ∉ {x : List ℤ | IsForestCode j x ∧ x.length = r} := fun h =>
      hr (BGW.exists_stepWord_eq_of_entries h.2 h.1.1)
    exact Set.indicator_of_notMem hnot _
  rw [← BGW.stepWord_injective.tsum_eq hrange]
  apply tsum_congr
  intro a
  by_cases ha : IsForestCode j (BGW.stepWord a)
  · rw [Set.indicator_of_mem (show BGW.stepWord a ∈
      {x | IsForestCode j x ∧ x.length = r} from ⟨ha, by simp [BGW.stepWord]⟩),
      Set.indicator_of_mem (show a ∈ {a | IsForestCode j (BGW.stepWord a)} from ha),
      BGW.walkWeight_stepWord]
  · rw [Set.indicator_of_notMem (show BGW.stepWord a ∉
      {x | IsForestCode j x ∧ x.length = r} from fun h => ha h.1),
      Set.indicator_of_notMem (show a ∉ {a | IsForestCode j (BGW.stepWord a)} from ha)]

/-- The mass of first passage to `-j` is the mass of the corresponding `j`-forest. -/
theorem forestHit_mass (μ : PMF ℕ) {j : ℕ} (hj : 1 ≤ j) (r : ℕ) :
    (offspringSeqLaw μ).toMeasure (forestHit j r) = BGW.forestWeight μ j r := by
  rw [forestHit_eq_preimage, ← Measure.map_apply (by fun_prop)
    (Set.to_countable _).measurableSet, map_offspringSeqLaw_initial,
    BGW.pi_eq_tsum_indicator, BGW.forestWeight_eq_tsum_codes μ hj, forestCode_tsum]
  apply tsum_congr
  intro a
  by_cases ha : IsForestCode j (BGW.stepWord a)
  · simp only [Set.indicator_of_mem (show a ∈ {a | IsForestCode j (BGW.stepWord a)} from ha),
      PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)]
  · simp only [Set.indicator_of_notMem (show a ∉ {a | IsForestCode j (BGW.stepWord a)} from ha)]

end BGW.StableTrees.DiscreteForest
