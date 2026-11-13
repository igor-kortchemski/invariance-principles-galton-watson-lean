/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeLaplace

/-!
# Cumulative Tonelli formula for decreasing weights

Writing a decreasing weight as the tail of a measure exchanges the clock measure and
its continuous cumulative function. No differentiation of the weight is required.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.StableTrees

/-- Tonelli exchanges a tail weight and the open-interval cumulative mass.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem lintegral_tail_eq_lintegral_cumulative (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (a : ℝ) :
    (∫⁻ t in Ioi a, ν (Ioi t) ∂μ) = ∫⁻ s in Ioi a, μ (Ioo a s) ∂ν := by
  let K : ℝ × ℝ → ℝ≥0∞ := fun p => if p.1 < p.2 then 1 else 0
  have hK : Measurable K := measurable_const.ite
    (measurableSet_lt measurable_fst measurable_snd) measurable_const
  have hleft (t : ℝ) (ht : a < t) :
      (∫⁻ s in Ioi a, K (t, s) ∂ν) = ν (Ioi t) := by
    change (∫⁻ s in Ioi a, (Ioi t).indicator (fun _ => (1 : ℝ≥0∞)) s ∂ν) = _
    rw [lintegral_indicator measurableSet_Ioi, lintegral_const,
      Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Ioi,
      inter_eq_left.mpr (Ioi_subset_Ioi ht.le), one_mul]
  have hright (s : ℝ) :
      (∫⁻ t in Ioi a, K (t, s) ∂μ) = μ (Ioo a s) := by
    change (∫⁻ t in Ioi a, (Iio s).indicator (fun _ => (1 : ℝ≥0∞)) t ∂μ) = _
    rw [lintegral_indicator measurableSet_Iio, lintegral_const,
      Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Iio,
      Iio_inter_Ioi, one_mul]
  calc
    _ = ∫⁻ t in Ioi a, ∫⁻ s in Ioi a, K (t, s) ∂ν ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hleft t ht).symm
    _ = ∫⁻ s in Ioi a, ∫⁻ t in Ioi a, K (t, s) ∂μ ∂ν :=
      lintegral_lintegral_swap hK.aemeasurable
    _ = _ := by simp_rw [hright]

/-- A continuous clock integrates a decreasing weight through its cumulative values.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem pathStieltjes_lintegral_tail {m : ℝ≥0 → ℝ}
    (hm : Monotone m ∧ Continuous m) (hm0 : m 0 = 0) (ν : Measure ℝ) [SFinite ν] :
    (∫⁻ t in Ioi (0 : ℝ), ν (Ioi t) ∂(pathStieltjes m).measure) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (m s.toNNReal) ∂ν := by
  rw [lintegral_tail_eq_lintegral_cumulative]
  apply lintegral_congr
  intro s
  rw [StieltjesFunction.measure_Ioo,
    (continuous_pathStieltjes m).continuousAt.continuousWithinAt.leftLim_eq,
    pathStieltjes_apply hm, pathStieltjes_apply hm, Real.toNNReal_zero, hm0, sub_zero]

/-- A Stieltjes function with finite limit supplies a decreasing tail weight.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem pathStieltjes_lintegral_decreasing {m : ℝ≥0 → ℝ}
    (hm : Monotone m ∧ Continuous m) (hm0 : m 0 = 0)
    (g : StieltjesFunction ℝ) {l : ℝ} (hg : Tendsto g atTop (𝓝 l)) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (l - g t) ∂(pathStieltjes m).measure) =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (m s.toNNReal) ∂g.measure := by
  have h := pathStieltjes_lintegral_tail hm hm0 g.measure
  simpa only [g.measure_Ioi hg] using h

end BGW.StableTrees
