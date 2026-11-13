/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.PathTailLimitMeasurable

/-!
# Large measurable events for source-horizon localization

A measurable version of the selected end gives measurable good events. Their bad probabilities
vanish as the source horizon increases, by the sealed first-long-end supplier.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees.PathTail

/-- The first long excursion ends inside a deterministic positive horizon on a measurable event
whose complement has arbitrarily small real probability. -/
theorem exists_firstLongEnd_good_set {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (M : ℝ≥0) (_ : 0 < M) (G : Set DLoc), MeasurableSet G ∧
      (stableLocalLaw θ : Measure DLoc).real Gᶜ < δ ∧
      ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
        (f ∈ G ↔ passageTime (firstLongLabel f) f < M) := by
  have he := aemeasurable_firstLongEnd hθ
  let g : DLoc → ℝ≥0 := he.mk (fun f => passageTime (firstLongLabel f) f)
  have hgm : Measurable g := he.measurable_mk
  have hgeq : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      passageTime (firstLongLabel f) f = g f := he.ae_eq_mk
  have hm (M : ℝ≥0) : (stableLocalLaw θ : Measure DLoc) {f | g f < M} =
      (stableLocalLaw θ : Measure DLoc) {f | passageTime (firstLongLabel f) f < M} := by
    apply measure_congr
    filter_upwards [hgeq] with f hf
    simp only [hf]
  have hlim : Tendsto (fun M : ℝ≥0 =>
      (stableLocalLaw θ : Measure DLoc) {f | g f < M}) atTop (𝓝 1) :=
    (tendsto_measure_firstLongEnd_lt hθ).congr' (Eventually.of_forall fun M => (hm M).symm)
  have hr : Tendsto (fun M : ℝ≥0 =>
      (stableLocalLaw θ : Measure DLoc).real {f | g f < M}) atTop (𝓝 1) := by
    simpa only [measureReal_def, ENNReal.toReal_one, Function.comp_def] using
      (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤)).comp hlim
  have hcomp (M : ℝ≥0) : (stableLocalLaw θ : Measure DLoc).real {f | g f < M}ᶜ =
      1 - (stableLocalLaw θ : Measure DLoc).real {f | g f < M} :=
    probReal_compl_eq_one_sub (measurableSet_lt hgm measurable_const)
  have hbad : Tendsto (fun M : ℝ≥0 =>
      (stableLocalLaw θ : Measure DLoc).real {f | g f < M}ᶜ) atTop (𝓝 0) := by
    simpa only [hcomp, sub_self] using (tendsto_const_nhds (x := (1 : ℝ))).sub hr
  obtain ⟨M, hM, hsmall⟩ := ((eventually_gt_atTop (0 : ℝ≥0)).and
    (hbad.eventually_lt_const hδ)).exists
  refine ⟨M, hM, {f | g f < M}, measurableSet_lt hgm measurable_const, hsmall, ?_⟩
  filter_upwards [hgeq] with f hf
  simp only [hf]

end BGW.StableTrees.PathTail
