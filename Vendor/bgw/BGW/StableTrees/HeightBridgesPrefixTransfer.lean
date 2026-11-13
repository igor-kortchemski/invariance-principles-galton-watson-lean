/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridgesPrefixLaw
public import BGW.StableTrees.HeightBridgesCompact
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Transfer of prefix events with an independent fresh path

A measurable event that reads its first path only up to a fixed horizon has the same
probability for the reversed prefix and fresh increments as for two independent stable paths.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Prefix-local events transfer together with independent fresh increments. -/
theorem measure_reversed_prefix_fresh_event {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {t : ℝ≥0} (ht : 0 < t) {E : Set (DLoc × DLoc)} (hE : MeasurableSet E)
    (hloc : ∀ f g h : DLoc, DLoc.restrict t f = DLoc.restrict t g →
      ((f, h) ∈ E ↔ (g, h) ∈ E)) :
    (stableLocalLaw θ : Measure DLoc)
      {f | (reversedAt t f, DLoc.shift t f) ∈ E} =
      ((stableLocalLaw θ : Measure DLoc).prod (stableLocalLaw θ : Measure DLoc)) E := by
  let P : Measure DLoc := stableLocalLaw θ
  let E' : Set (D (t : ℝ) ℝ × DLoc) :=
    (fun p => (horizonExtension t p.1, p.2)) ⁻¹' E
  have hE' : MeasurableSet E' := hE.preimage
    (((measurable_horizonExtension t).comp measurable_fst).prodMk measurable_snd)
  have hpair : Measurable (fun f => (DLoc.restrict t (reversedAt t f), DLoc.shift t f)) :=
    ((DLoc.measurable_restrict t).comp
      (measurable_reversedAt_uncurry.comp (measurable_const.prodMk measurable_id))).prodMk
        (DLoc.measurable_shift_fixed t)
  calc
    _ = P {f | (horizonExtension t (DLoc.restrict t (reversedAt t f)),
        DLoc.shift t f) ∈ E} := by
      congr 1
      ext f
      exact (hloc _ _ _ (restrict_horizonExtension t _)).symm
    _ = (P.map (fun f => (DLoc.restrict t (reversedAt t f), DLoc.shift t f))) E' :=
      (Measure.map_apply hpair hE').symm
    _ = ((P.map (DLoc.restrict t)).prod P) E' := by
      rw [map_reversed_prefix_shift_stableLocalLaw hθ ht]
    _ = ((P.prod P).map (Prod.map (DLoc.restrict t) id)) E' := by
      rw [← Measure.map_prod_map P P (DLoc.measurable_restrict t) measurable_id,
        Measure.map_id]
    _ = (P.prod P) E := by
      rw [Measure.map_apply ((DLoc.measurable_restrict t).prodMap measurable_id) hE']
      congr 1
      ext p
      exact hloc _ _ _ (restrict_horizonExtension t _)

/-- Equality of compact prefixes preserves the supremum clock at every earlier age. -/
theorem supLocalTime_eq_of_restrict_eq (θ : ℝ) {t : ℝ≥0} (f g : DLoc)
    (he : DLoc.restrict t f = DLoc.restrict t g) (u : ℝ≥0) (hu : u ≤ t) :
    supLocalTime θ f u = supLocalTime θ g u := by
  have he' : DLoc.restrict u f = DLoc.restrict u g := by
    rw [← DLoc.restrict_restrict hu f, ← DLoc.restrict_restrict hu g, he]
  exact (measurable_supLocalTime_prefix θ u).factorsThrough he'

/-- Equality of compact prefixes preserves the running supremum at every earlier age. -/
theorem supRunning_eq_of_restrict_eq {t : ℝ≥0} (f g : DLoc)
    (he : DLoc.restrict t f = DLoc.restrict t g) (u : ℝ≥0) (hu : u ≤ t) :
    supRunning f u = supRunning g u := by
  have he' : DLoc.restrict u f = DLoc.restrict u g := by
    rw [← DLoc.restrict_restrict hu f, ← DLoc.restrict_restrict hu g, he]
  exact (measurable_supRunning_prefix u).factorsThrough he'

end BGW.StableTrees
