/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionCutAdapters
public import BGW.StableTrees.LongExtractionEndpoints

/-!
# Continuity and identification at the selected long excursion

The good-path predicate gives continuity of the source at both selected endpoints, and the
selected excursion is the actual translated stopped cut.
-/

@[expose] public section

open Set Filter Topology
open scoped NNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The source path is continuous at both endpoints of the selected long excursion.
Reference: Billingsley (1999), Chapter 3. -/
theorem GoodLongExtractionPath.continuousAt_firstLong_ends {M : ℝ≥0} {f : DLoc}
    (hf : GoodLongExtractionPath M f) :
    ContinuousAt f.1 (passageTimeMinus (firstLongLabel f) f) ∧
      ContinuousAt f.1 (passageTime (firstLongLabel f) f) := by
  have hreg := hf.regular (firstLongLabel f) hf.isLeast_firstLongLabel.1.1
  have heq : f.1 = fun t => (reflectedFrom 0 f).1 t + runningInfLoc f t := by
    funext t
    rw [reflectedFrom_zero_apply hf.zero]
    ring
  rw [heq]
  exact ⟨hreg.2.1.add hf.infContinuous.continuousAt,
    hreg.2.2.1.add hf.infContinuous.continuousAt⟩

/-- The selected excursion path is the sealed translated stopped cut at its selected endpoints.
Reference: Billingsley (1999), Chapter 3. -/
private theorem GoodLongExtractionPath.firstLongMark_path {M : ℝ≥0} {f : DLoc}
    (hf : GoodLongExtractionPath M f) :
    (firstLongMark f).path =
      cutPath (passageTimeMinus (firstLongLabel f) f) (passageTime (firstLongLabel f) f) f := by
  apply Subtype.ext
  funext t
  have hc := (hf.regular (firstLongLabel f) hf.isLeast_firstLongLabel.1.1).1
  change (excursionCut _ _ f).path.1 t = (cutPath _ _ f).1 t
  rw [excursionCut_eval hc, cutPath_min_apply hc.1.le]

/-- The finite stopped cut of the restricted source is the selected excursion restriction.
Reference: Billingsley (1999), Chapter 3. -/
theorem GoodLongExtractionPath.translatedStoppedCut_eq {M T : ℝ≥0} {f : DLoc}
    (hf : GoodLongExtractionPath M f) :
    translatedStoppedCut T (DLoc.restrict M f)
      ⟨passageTimeMinus (firstLongLabel f) f, (passageTimeMinus (firstLongLabel f) f).2,
        by exact_mod_cast hf.isLeast_firstLongLabel.1.1.2.le.trans hf.end_lt.le⟩
      ⟨passageTime (firstLongLabel f) f, (passageTime (firstLongLabel f) f).2,
        by exact_mod_cast hf.end_lt.le⟩
      (by exact_mod_cast hf.isLeast_firstLongLabel.1.1.2.le) =
        excursionRestrict T (firstLongMark f) := by
  rw [translatedStoppedCut_restrict f hf.isLeast_firstLongLabel.1.1.2.le hf.end_lt.le]
  rw [excursionRestrict, hf.firstLongMark_path]

end BGW.StableTrees
