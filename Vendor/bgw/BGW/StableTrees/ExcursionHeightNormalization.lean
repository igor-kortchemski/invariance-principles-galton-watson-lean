/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightUnitScaling

/-!
# Normalization of the excursion and its continuous height

The joint shape/lifetime law pulls back a measurable product scaling event. This does not
substitute an excursion-dependent scale into a fixed-scale almost-sure assertion.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Normalization of the pair** under `N`: `H(e)(ζ t) = ζ^(1-1/θ) H(normalizeExc θ e)(t)`. -/
theorem ae_excursionHeight_normalize {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(excursionMeasure θ), ∀ t : ℝ≥0,
      excursionHeight θ e (e.lifetime * t) =
        (e.lifetime : ℝ) ^ (1 - 1 / θ) * excursionHeight θ (normalizeExc θ e) t := by
  have hp : ∀ᵐ p ∂((lifetimeLaw θ).prod (unitExcursionLaw θ : Measure Excursion)),
      ∀ t : ℝ≥0, excursionHeight θ (excursionScale θ p.1 p.2)
        ((p.1 : ℝ).toNNReal * t) =
          (p.1 : ℝ) ^ (1 - 1 / θ) * excursionHeight θ p.2 t :=
    (MeasureTheory.Measure.ae_prod_iff_ae_ae (measurableSet_excursionHeight_scale θ)).mpr
      (ae_of_all _ (ae_excursionHeight_scale_unit hθ))
  rw [← shapeLifetime_map_excursionMeasure hθ] at hp
  have ha := ae_of_ae_map (measurable_shapeLifetime θ).aemeasurable hp
  filter_upwards [ha] with e he t
  have hc : excursionScale θ e.lifetimePos (normalizeExc θ e) = e :=
    fromShapeLifetime_shapeLifetime θ e
  change ∀ t : ℝ≥0, excursionHeight θ
    (excursionScale θ e.lifetimePos (normalizeExc θ e))
    ((e.lifetimePos : ℝ).toNNReal * t) =
      (e.lifetimePos : ℝ) ^ (1 - 1 / θ) * excursionHeight θ (normalizeExc θ e) t at he
  rw [hc] at he
  simpa only [Excursion.lifetimePos, Real.toNNReal_coe] using he t

end BGW.StableTrees
