/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumFactorizationClock

/-! # Integrating out an independent exponential clock

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Integrating over the product clock law is the exponentially weighted resolvent integral. -/
theorem lintegral_expClockLaw (θ : ℝ) {q : ℝ} (hq : 0 < q)
    {H : DLoc × ℝ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ p, H p ∂expClockLaw θ q =
      ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (q * Real.exp (-q * t)) *
        ∫⁻ f, H (f, t) ∂(stableLocalLaw θ : Measure DLoc) := by
  let := isProbabilityMeasure_expMeasure hq
  rw [expClockLaw, lintegral_prod_symm _ hH.aemeasurable]
  have hm : Measurable (fun t => ∫⁻ f, H (f, t) ∂(stableLocalLaw θ : Measure DLoc)) :=
    hH.lintegral_prod_left'
  change (∫⁻ t, (∫⁻ f, H (f, t) ∂(stableLocalLaw θ : Measure DLoc))
    ∂volume.withDensity (exponentialPDF q)) = _
  have hd : Measurable (exponentialPDF q) :=
    (measurable_exponentialPDFReal q).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul volume hd hm]
  rw [← lintegral_indicator measurableSet_Ici]
  apply lintegral_congr
  intro t
  by_cases ht : 0 ≤ t
  · rw [Set.indicator_of_mem (show t ∈ Ici 0 from ht), Pi.mul_apply, exponentialPDF_of_nonneg ht]
    simp only [neg_mul]
  · rw [Set.indicator_of_notMem (show t ∉ Ici 0 from ht), Pi.mul_apply,
      exponentialPDF_of_neg (lt_of_not_ge ht),
      zero_mul]

end BGW.StableTrees
