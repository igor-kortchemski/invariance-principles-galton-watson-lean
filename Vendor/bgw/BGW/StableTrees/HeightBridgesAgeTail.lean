/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridgesAgeMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Vanishing integrated excursion survival tails near age zero

Integrability of the lifetime tail gives vanishing mass on shrinking initial windows.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.StableTrees

/-- The survival mass is a measurable function of the observation age. -/
theorem measurable_excursion_lifetime_tail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    Measurable (fun s : ℝ => excursionMeasure θ {e : Excursion | s.toNNReal < e.lifetime}) := by
  have := sigmaFinite_excursionMeasure hθ
  exact measurable_measure_prodMk_left measurableSet_heightExcursionAge_survival

private theorem shrinking_window_lintegral (T : ℝ≥0) (a : ℕ → ℝ≥0)
    (ha : Tendsto a atTop (𝓝 0)) (hle : ∀ n, a n ≤ T)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (hfin : (∫⁻ s in Ioo (0 : ℝ) (T : ℝ), f s) ≠ ⊤) :
    Tendsto (fun n => ∫⁻ s in Ioo (0 : ℝ) (a n : ℝ), f s) atTop (𝓝 0) := by
  let F : ℕ → ℝ → ℝ≥0∞ := fun n => (Ioo (0 : ℝ) (a n : ℝ)).indicator f
  have heq (n : ℕ) : (∫⁻ s in Ioo (0 : ℝ) (T : ℝ), F n s) =
      ∫⁻ s in Ioo (0 : ℝ) (a n : ℝ), f s := by
    change (∫⁻ s in Ioo (0 : ℝ) (T : ℝ), (Ioo (0 : ℝ) (a n : ℝ)).indicator f s) = _
    rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
    rw [show Ioo (0 : ℝ) (a n : ℝ) ∩ Ioo (0 : ℝ) (T : ℝ) =
      Ioo (0 : ℝ) (a n : ℝ) from inter_eq_left.mpr
        (fun _ hs => ⟨hs.1, hs.2.trans_le (hle n)⟩)]
  have har : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, NNReal.coe_zero] using
      NNReal.continuous_coe.continuousAt.tendsto.comp ha
  have hlim : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) T),
      Tendsto (fun n => F n s) atTop (𝓝 (0 : ℝ≥0∞)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hz : (fun n => F n s) =ᶠ[atTop] fun _ => 0 := by
      filter_upwards [har.eventually (eventually_lt_nhds hs.1)] with n hn
      exact Set.indicator_of_notMem (fun h => (not_lt_of_ge hn.le) h.2) _
    exact (tendsto_congr' hz).mpr tendsto_const_nhds
  have hbound (n : ℕ) : F n ≤ᵐ[volume.restrict (Ioo (0 : ℝ) T)] f := by
    filter_upwards with s
    by_cases hs : s ∈ Ioo (0 : ℝ) (a n : ℝ)
    · exact (Set.indicator_of_mem hs f).le
    · exact (Set.indicator_of_notMem hs f).trans_le zero_le
  have hdom : Tendsto (fun n => ∫⁻ s in Ioo (0 : ℝ) (T : ℝ), F n s) atTop (𝓝 0) := by
    simpa only [lintegral_zero] using
      tendsto_lintegral_of_dominated_convergence
        (μ := volume.restrict (Ioo (0 : ℝ) T)) (F := F) (f := fun _ => 0) f
        (fun n => hf.indicator measurableSet_Ioo) hbound hfin hlim
  simpa only [heq] using hdom

/-- Integrated lifetime tails vanish on any sequence of shrinking initial age windows. -/
theorem tendsto_lintegral_excursion_lifetime_tail_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (T : ℝ≥0) (a : ℕ → ℝ≥0) (ha : Tendsto a atTop (𝓝 0)) (hle : ∀ n, a n ≤ T) :
    Tendsto (fun n => ∫⁻ s in Ioo (0 : ℝ) (a n : ℝ),
      excursionMeasure θ {e : Excursion | s.toNNReal < e.lifetime}) atTop (𝓝 0) := by
  exact shrinking_window_lintegral T a ha hle _
    (measurable_excursion_lifetime_tail hθ) (lintegral_excursion_lifetime_tail_lt_top hθ T).ne

end BGW.StableTrees
