/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumReflectedFamily

/-!
# Constancy of the auxiliary clock off supremum contact

With no negative jumps of the original path, reflection at the supremum is lower
semicontinuous. On a compact interval with no contact its minimum is positive, so every
sufficiently small occupation cutoff is constant there. The same holds for its limit.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Reflection is lower semicontinuous when the original path has no negative jumps. -/
theorem lowerSemicontinuous_supReflected {f : DLoc}
    (hf : ∀ u, Function.leftLim f.1 u ≤ f.1 u) : LowerSemicontinuous (supReflected f) := by
  intro u a ha
  rw [← nhdsLT_sup_nhdsGE u, eventually_sup]
  constructor
  · exact ((isCadlag_supReflected f).tendsto_nhdsLT_leftLim u).eventually
      (eventually_gt_nhds (ha.trans_le (supReflected_le_leftLim hf u)))
  · have hc : ContinuousWithinAt (supReflected f) (Ici u) u := by
      rw [ContinuousWithinAt, ← nhdsGT_sup_nhdsWithin_singleton u, tendsto_sup]
      exact ⟨(isCadlag_supReflected f).isRightContinuous u,
        by simpa only [nhdsWithin_singleton] using tendsto_pure_nhds (supReflected f) u⟩
    exact hc.eventually (eventually_gt_nhds ha)

/-- An occupation cutoff below every reflected value on an interval has equal endpoint values. -/
theorem supOccupation_eq_of_gap {ε : ℝ} (f : DLoc) {s t : ℝ≥0} (hst : s ≤ t)
    (hgap : ∀ u ∈ Icc s t, ε ≤ supReflected f u) :
    supOccupation ε f t = supOccupation ε f s := by
  have he : {r : ℝ | 0 ≤ r ∧ r ≤ (t : ℝ) ∧ supReflected f r.toNNReal < ε} =
      {r : ℝ | 0 ≤ r ∧ r ≤ (s : ℝ) ∧ supReflected f r.toNNReal < ε} := by
    ext r
    constructor
    · rintro ⟨hr0, hrt, hrε⟩
      refine ⟨hr0, ?_, hrε⟩
      by_contra hrs
      have hrs' : (s : ℝ) < r := lt_of_not_ge hrs
      have hu : r.toNNReal ∈ Icc s t := by
        constructor <;> apply NNReal.coe_le_coe.mp <;> rw [Real.coe_toNNReal _ hr0]
        · exact hrs'.le
        · exact hrt
      exact (not_lt_of_ge (hgap _ hu)) hrε
    · rintro ⟨hr0, hrs, hrε⟩
      exact ⟨hr0, hrs.trans (NNReal.coe_le_coe.mpr hst), hrε⟩
  simp only [supOccupation, he]

end BGW.StableTrees
