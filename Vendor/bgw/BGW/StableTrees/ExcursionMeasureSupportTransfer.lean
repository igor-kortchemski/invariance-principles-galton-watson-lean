/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureBasic

/-! Transfer of measurable mark properties from the jump excursions to the mean mark measure.

See Bertoin, *Lévy Processes*, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- A measurable property shared by all jump marks almost surely holds almost everywhere
for the excursion measure. The measurability hypothesis must be proved before applying this
lemma to a property quantified over all times. -/
theorem ae_excursionMeasure_of_ae_jumpExcursion {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {Q : Excursion → Prop} (hQ : MeasurableSet {e | Q e})
    (hmarks : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∀ x ∈ passageJumpSet f, Q (jumpExcursion x f)) :
    ∀ᵐ e ∂(excursionMeasure θ), Q e := by
  classical
  rw [ae_iff]
  change excursionMeasure θ {e | Q e}ᶜ = 0
  rw [excursionMeasure_apply hθ hQ.compl]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hmarks, ae_passageJumpSet_countable hθ] with f hf hc
  rw [excursionPointMeasure_apply hc (measurable_box hQ.compl)]
  have hempty : {x ∈ passageJumpSet f |
      (x, jumpExcursion x f) ∈ Ioc 0 1 ×ˢ {e | Q e}ᶜ} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, _, hbad⟩
    exact hbad (hf x hx)
  rw [hempty]
  simp

end BGW.StableTrees
