/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridgesExcursionLimit
public import BGW.StableTrees.HeightBridgesProduct

/-!
# Joint approximation limits on age windows

All product measures used here are finite. The excursion product is restricted to survival,
and its joint limit is obtained by the Cauchy criterion rather than a measurable choice of limits.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- Joint age/path measurability of an excursion approximation. -/
theorem measurable_heightApprox_age_excursion (ε : ℝ) :
    Measurable (fun p : ℝ × Excursion => heightApprox ε p.2.path p.1.toNNReal) :=
  measurable_heightApprox_uncurry.comp (measurable_const.prodMk
    ((measurable_real_toNNReal.comp measurable_fst).prodMk
      (measurable_excursion_path.comp measurable_snd)))

/-- Joint age/path measurability of a stable-path approximation. -/
theorem measurable_heightApprox_age_stable (ε : ℝ) :
    Measurable (fun p : ℝ × DLoc => heightApprox ε p.2 p.1.toNNReal) :=
  measurable_heightApprox_uncurry.comp (measurable_const.prodMk
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))

/-- Existence of a joint limit on a finite surviving excursion age window. -/
theorem exists_heightApprox_tendstoInMeasure_excursion_ages {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (S : ℝ≥0) :
    ∃ L : ℝ × Excursion → ℝ, Measurable L ∧ TendstoInMeasure
      (heightExcursionAgeMeasure θ S)
      (fun (ε : ℝ) p => heightApprox ε p.2.path p.1.toNNReal) (𝓝[>] (0 : ℝ)) L := by
  have := sigmaFinite_excursionMeasure hθ
  have : IsFiniteMeasure (((volume.restrict (Ioo (0 : ℝ) (S : ℝ))).prod
      (excursionMeasure θ)).restrict {p | p.1.toNNReal < p.2.lifetime}) := by
    change IsFiniteMeasure (heightExcursionAgeMeasure θ S)
    exact isFiniteMeasure_heightExcursionAgeMeasure hθ S
  apply exists_joint_tendstoInMeasure_of_fiber_limits
    (volume.restrict (Ioo (0 : ℝ) (S : ℝ))) (excursionMeasure θ)
    measurableSet_heightExcursionAge_survival _ measurable_heightApprox_age_excursion
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  obtain ⟨L, _, hL⟩ := exists_heightApprox_tendstoInMeasure_excursion hθ s.toNNReal
    (Real.toNNReal_pos.mpr hs.1)
  exact ⟨L, hL⟩

/-- Existence of a joint limit on a bounded stable-path age window. -/
theorem exists_heightApprox_tendstoInMeasure_stable_ages {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (S : ℝ≥0) :
    ∃ L : ℝ × DLoc → ℝ, Measurable L ∧ TendstoInMeasure
      ((volume.restrict (Ioo (0 : ℝ) (S : ℝ))).prod (stableLocalLaw θ : Measure DLoc))
      (fun (ε : ℝ) p => heightApprox ε p.2 p.1.toNNReal) (𝓝[>] (0 : ℝ)) L := by
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) (S : ℝ))) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  obtain ⟨L, hL, hconv⟩ := exists_joint_tendstoInMeasure_of_fiber_limits
    (volume.restrict (Ioo (0 : ℝ) (S : ℝ))) (stableLocalLaw θ : Measure DLoc)
    (S := univ) MeasurableSet.univ _ measurable_heightApprox_age_stable
    (ae_of_all _ fun s => ⟨fun f => height θ f s.toNNReal, by
      simpa only [mem_univ, ofPred_true, Measure.restrict_univ] using
        heightApprox_tendstoInMeasure hθ s.toNNReal⟩)
  exact ⟨L, hL, by simpa only [Measure.restrict_univ] using hconv⟩

/-- Existence of a joint limit on the unit-law age window `(0,1)`. -/
theorem exists_heightApprox_tendstoInMeasure_unit_ages {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ L : ℝ × Excursion → ℝ, Measurable L ∧ TendstoInMeasure
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (unitExcursionLaw θ : Measure Excursion))
      (fun (ε : ℝ) p => heightApprox ε p.2.path p.1.toNNReal) (𝓝[>] (0 : ℝ)) L := by
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hslice : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) 1), ∃ L : Excursion → ℝ,
      TendstoInMeasure ((unitExcursionLaw θ : Measure Excursion).restrict univ)
        (fun ε e => heightApprox ε e.path s.toNNReal) (𝓝[>] (0 : ℝ)) L := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hs0 : 0 < s.toNNReal := Real.toNNReal_pos.mpr hs.1
    have hs1 : s.toNNReal < 1 := by
      exact_mod_cast (show (s.toNNReal : ℝ) < 1 by
        rw [Real.coe_toNNReal _ hs.1.le]
        exact hs.2)
    obtain ⟨L, _, hL⟩ := exists_heightApprox_tendstoInMeasure_unit hθ s.toNNReal hs0 hs1
    exact ⟨L, by simpa only [Measure.restrict_univ] using hL⟩
  obtain ⟨L, hL, hconv⟩ := exists_joint_tendstoInMeasure_of_fiber_limits
    (volume.restrict (Ioo (0 : ℝ) 1)) (unitExcursionLaw θ : Measure Excursion)
    (S := univ) MeasurableSet.univ _ measurable_heightApprox_age_excursion hslice
  exact ⟨L, hL, by simpa only [Measure.restrict_univ] using hconv⟩

end BGW.StableTrees
