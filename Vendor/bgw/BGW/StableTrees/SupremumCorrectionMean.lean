/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCorrectionMartingale

/-!
# Stopped means of the occupation error

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The stopped error has mean zero at every bounded horizon. -/
theorem integral_errorMartingale_stopped {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) {σ : DLoc → ℝ≥0∞} (hσ : IsStoppingTime DLoc.filtration σ) (t : ℝ≥0) :
    ∫ f, errorMartingale θ ε (errStopTime n σ t f) f ∂(stableLocalLaw θ : Measure DLoc) = 0 := by
  have hM := martingale_errorMartingale_stopped hθ hε n hσ
  have hi := hM.setIntegral_eq (show (0 : ℝ≥0) ≤ t from zero_le) MeasurableSet.univ
  simp only [setIntegral_univ] at hi
  rw [← hi]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_errorMartingale_zero hθ hε] with f hf
  simpa [errStopTime] using hf

private theorem integrable_stopped_components {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) (n : ℕ) {σ : DLoc → ℝ≥0∞} (hσ : IsStoppingTime DLoc.filtration σ) (t : ℝ≥0) :
    Integrable (fun f => supOccupation ε f (errStopTime n σ t f))
        (stableLocalLaw θ : Measure DLoc) ∧
      Integrable (fun f => supAuxLocalTime θ f (errStopTime n σ t f))
        (stableLocalLaw θ : Measure DLoc) ∧
      Integrable (fun f => occupationCorrection θ ε (errStopTime n σ t f) f)
        (stableLocalLaw θ : Measure DLoc) := by
  have hOm := ((stronglyMeasurable_errStopTime_eval
    (isStronglyProgressive_supOccupation hε) n hσ t).mono
      (DLoc.filtration.le t)).aestronglyMeasurable
      (μ := (stableLocalLaw θ : Measure DLoc))
  have hMm := ((stronglyMeasurable_errStopTime_eval
    (isStronglyProgressive_supAuxLocalTime hθ) n hσ t).mono
      (DLoc.filtration.le t)).aestronglyMeasurable
      (μ := (stableLocalLaw θ : Measure DLoc))
  have hw : IsStronglyProgressive DLoc.filtration (fun s f => occupationCorrection θ ε s f) := by
    intro T
    exact (((measurable_supCorrection θ ε).comp
      (isStronglyProgressive_supReflectedFrom 0 T).measurable).sub
        measurable_const).stronglyMeasurable
  have hWm := ((stronglyMeasurable_errStopTime_eval hw n hσ t).mono
      (DLoc.filtration.le t)).aestronglyMeasurable
      (μ := (stableLocalLaw θ : Measure DLoc))
  refine ⟨?_, ?_, ?_⟩
  · apply Integrable.of_bound hOm ((t : ℝ) / ε)
    filter_upwards with f
    rw [Real.norm_eq_abs, abs_of_nonneg (supOccupation_nonneg hε.le f _)]
    have hb := (supOccupation_sub_mem hε f
      (show (0 : ℝ≥0) ≤ errStopTime n σ t f from zero_le)).2
    simp only [supOccupation_zero, NNReal.coe_zero, sub_zero] at hb
    exact hb.trans (by
      rw [div_eq_mul_inv, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (NNReal.coe_le_coe.mpr (errStopTime_le n σ t f)) (inv_pos.mpr hε).le)
  · apply (integrable_supAuxLocalTime hθ t).mono' hMm
    filter_upwards [ae_supAuxLocalTime_continuous hθ] with f hf
    rw [Real.norm_eq_abs, abs_of_nonneg (hf.1 ▸ hf.2.1
      (show (0 : ℝ≥0) ≤ errStopTime n σ t f from zero_le))]
    exact hf.2.1 (errStopTime_le n σ t f)
  · apply Integrable.of_bound hWm (2 * supCorrectionBound θ ε)
    exact ae_of_all _ (fun f => by
      rw [Real.norm_eq_abs]
      exact abs_occupationCorrection_le hθ hε _ f)

/-- The mean occupation error is minus the mean correction, giving the stopped mean bound. -/
theorem integral_supOccupation_stopped_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) {σ : DLoc → ℝ≥0∞} (hσ : IsStoppingTime DLoc.filtration σ) (t : ℝ≥0) :
    (∫ f, (supOccupation ε f (errStopTime n σ t f) - supAuxLocalTime θ f (errStopTime n σ t f))
        ∂(stableLocalLaw θ : Measure DLoc) =
      -∫ f, occupationCorrection θ ε (errStopTime n σ t f) f ∂(stableLocalLaw θ : Measure DLoc)) ∧
    ∫ f, supOccupation ε f (errStopTime n σ t f) ∂(stableLocalLaw θ : Measure DLoc) ≤
      ∫ f, supAuxLocalTime θ f (errStopTime n σ t f) ∂(stableLocalLaw θ : Measure DLoc) +
        2 * supCorrectionBound θ ε := by
  obtain ⟨hO, hM, hW⟩ := integrable_stopped_components hθ hε n hσ t
  have hmean := integral_errorMartingale_stopped hθ hε n hσ t
  unfold errorMartingale at hmean
  have hOM : Integrable (fun f => supOccupation ε f (errStopTime n σ t f) -
      supAuxLocalTime θ f (errStopTime n σ t f)) (stableLocalLaw θ : Measure DLoc) :=
    hO.sub hM
  rw [integral_add hOM hW] at hmean
  refine ⟨by linarith only [hmean], ?_⟩
  rw [integral_sub hO hM] at hmean
  have hlow : -(2 * supCorrectionBound θ ε) ≤
      ∫ f, occupationCorrection θ ε (errStopTime n σ t f) f
        ∂(stableLocalLaw θ : Measure DLoc) := by
    have hh := integral_mono_ae (integrable_const (-(2 * supCorrectionBound θ ε))) hW
      (ae_of_all _ (fun f => (abs_le.mp (abs_occupationCorrection_le hθ hε
        (errStopTime n σ t f) f)).1))
    simpa only [integral_const, probReal_univ, one_smul] using hh
  linarith only [hmean, hlow]

end BGW.StableTrees
