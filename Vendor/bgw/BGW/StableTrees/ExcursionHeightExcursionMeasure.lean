/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightLocality
public import BGW.StableTrees.ExcursionHeightMeasurable
import BGW.StableTrees.ExcursionMeasureSupportTransfer

/-!
# Continuous height versions under the excursion measure

The measurable non-junk event transfers from every jump mark to the excursion measure.
The deterministic prefix graph then holds simultaneously at all surviving horizons.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Under the excursion measure every excursion has an a.e.-age height version (the non-junk
branch of `excursionHeight`). -/
theorem ae_exists_isExcursionHeightVersion {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(excursionMeasure θ), ∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ e g := by
  apply ae_excursionMeasure_of_ae_jumpExcursion hθ
    (measurableSet_exists_isExcursionHeightVersion θ)
  exact (ae_jumpExcursion_heightVersion hθ).mono fun _ hf x hx => (hf x hx).1

/-- **Graph identity under `N`**, simultaneously for all horizons `a < ζ`: the a.e.-time prefix
map applied to the restricted excursion is the excursion height on `[0,a]`. -/
theorem ae_heightPrefixAE_excursionRestrict {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(excursionMeasure θ), ∀ a : ℝ≥0, a < e.lifetime → ∀ t : Set.Icc (0 : ℝ) a,
      heightPrefixAE θ a (excursionRestrict a e) t = excursionHeight θ e ⟨t, t.2.1⟩ := by
  filter_upwards [ae_exists_isExcursionHeightVersion hθ] with e he
  intro a ha t
  exact heightPrefixAE_excursionRestrict_of_exists θ e he ha t

/-- **Graph identity under `N ↾ {a < ζ}`** for a fixed horizon `a`. -/
theorem ae_restrict_heightPrefixAE_excursionRestrict {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) :
    ∀ᵐ e ∂((excursionMeasure θ).restrict {e : Excursion | a < e.lifetime}),
      ∀ t : Set.Icc (0 : ℝ) a,
        heightPrefixAE θ a (excursionRestrict a e) t = excursionHeight θ e ⟨t, t.2.1⟩ := by
  apply (ae_restrict_iff' (measurableSet_lt measurable_const measurable_excursion_lifetime)).mpr
  exact (ae_heightPrefixAE_excursionRestrict hθ).mono fun _ hf ha => hf a ha

/-- **Graph identity under the tail law** `N(· | ζ > 1)`, simultaneously for all horizons
`a < ζ` (in particular every `a ≤ 1`), with the same Borel map `heightPrefixAE θ a`. -/
theorem ae_heightPrefixAE_tailExcursionLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(tailExcursionLaw θ : Measure Excursion), ∀ a : ℝ≥0, a < e.lifetime →
      ∀ t : Set.Icc (0 : ℝ) a,
        heightPrefixAE θ a (excursionRestrict a e) t = excursionHeight θ e ⟨t, t.2.1⟩ := by
  rw [coe_tailExcursionLaw hθ]
  exact Measure.ae_smul_measure (ae_restrict_of_ae (ae_heightPrefixAE_excursionRestrict hθ)) _

end BGW.StableTrees
