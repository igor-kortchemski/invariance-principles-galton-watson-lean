/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.PathTailDefs

/-!
# Measurability of the limiting extraction triple

The first long label is a.e. measurable. Jointly measurable passage maps and excursion
restriction then give the limiting endpoints and cut as an a.e. measurable map.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees.PathTail

/-- The selected end is a.e. measurable under the local stable law. -/
theorem aemeasurable_firstLongEnd {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    AEMeasurable (fun f : DLoc => passageTime (firstLongLabel f) f)
      (stableLocalLaw θ : Measure DLoc) := by
  have hp : AEMeasurable (fun f : DLoc => (firstLongLabel f, f))
      (stableLocalLaw θ : Measure DLoc) :=
    (aemeasurable_firstLongLabel hθ).prodMk aemeasurable_id
  have hm : Measurable (fun p : ℝ≥0 × DLoc => passageTime p.1 p.2) :=
    measurable_passageTime_uncurry
  exact hm.comp_aemeasurable (f := fun f : DLoc => (firstLongLabel f, f)) hp

/-- The endpoint/cut triple is a.e. measurable under the local stable law. -/
theorem aemeasurable_longCutTriple {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    AEMeasurable (longCutTriple T) (stableLocalLaw θ : Measure DLoc) := by
  have hp := (aemeasurable_firstLongLabel hθ).prodMk aemeasurable_id
  have hg := measurable_passageTimeMinus_uncurry.comp_aemeasurable hp
  have hd := aemeasurable_firstLongEnd hθ
  have hc := (measurable_excursionRestrict T).comp_aemeasurable
    (aemeasurable_firstLongMark hθ)
  exact hg.coe_nnreal_real.prodMk (hd.coe_nnreal_real.prodMk hc)

end BGW.StableTrees.PathTail
