/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCorrectionCutoff
public import BGW.StableTrees.SupremumCorrectionPath

/-!
# Bounded stopping epochs and square integrability of the error

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Reading the finite stopping epoch as an extended time recovers its defining minimum. -/
private theorem coe_errStopTime (n : ℕ) (σ : DLoc → ℝ≥0∞) (t : ℝ≥0) (f : DLoc) :
    (errStopTime n σ t f : ℝ≥0∞) = min (t : ℝ≥0∞) (min (σ f) (errCutoff n f)) := by
  unfold errStopTime
  rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top
    ((min_le_left _ _).trans (min_le_left _ _))), min_assoc]

/-- The bounded stopping epoch never exceeds its deterministic horizon. -/
theorem errStopTime_le (n : ℕ) (σ : DLoc → ℝ≥0∞) (t : ℝ≥0) (f : DLoc) :
    errStopTime n σ t f ≤ t := by
  rw [← ENNReal.coe_le_coe, coe_errStopTime]
  exact min_le_left _ _

/-- The bounded stopping epoch never exceeds the localizing cutoff. -/
theorem errStopTime_le_cutoff (n : ℕ) (σ : DLoc → ℝ≥0∞) (t : ℝ≥0) (f : DLoc) :
    (errStopTime n σ t f : ℝ≥0∞) ≤ errCutoff n f := by
  rw [coe_errStopTime]
  exact (min_le_right _ _).trans (min_le_right _ _)

/-- Evaluation at the finite epoch agrees with Mathlib's stopped-process representative. -/
theorem errStopTime_eval_eq_stoppedProcess (F : ℝ≥0 → DLoc → ℝ) (n : ℕ)
    (σ : DLoc → ℝ≥0∞) (t : ℝ≥0) (f : DLoc) :
    F (errStopTime n σ t f) f = stoppedProcess F (fun f => min (σ f) (errCutoff n f)) t f := by
  change F _ f = F ((min (t : WithTop ℝ≥0) (min (σ f) (errCutoff n f))).untopA) f
  have he := coe_errStopTime n σ t f
  have he' : (errStopTime n σ t f : WithTop ℝ≥0) =
      min (t : WithTop ℝ≥0) (min (σ f) (errCutoff n f)) := he
  rw [← he', WithTop.untopA_eq_untop WithTop.coe_ne_top]
  congr 1

/-- Progressive processes evaluated at the bounded epoch are measurable at that horizon. -/
theorem stronglyMeasurable_errStopTime_eval {F : ℝ≥0 → DLoc → ℝ}
    (hF : IsStronglyProgressive DLoc.filtration F) (n : ℕ) {σ : DLoc → ℝ≥0∞}
    (hσ : IsStoppingTime DLoc.filtration σ) (t : ℝ≥0) :
    StronglyMeasurable[DLoc.filtration t] (fun f => F (errStopTime n σ t f) f) := by
  have he : (fun f => F (errStopTime n σ t f) f) =
      stoppedProcess F (fun f => min (σ f) (errCutoff n f)) t :=
    funext (errStopTime_eval_eq_stoppedProcess F n σ t)
  rw [he]
  exact hF.stronglyAdapted_stoppedProcess (hσ.min (isStoppingTime_errCutoff n)) t

/-- Uniform pathwise domination of the error at arbitrary epochs before a fixed horizon. -/
private theorem ae_abs_errorMartingale_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε)
    (T : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s ≤ T,
      |errorMartingale θ ε s f| ≤ T / ε + supAuxLocalTime θ f T + 2 * supCorrectionBound θ ε := by
  filter_upwards [ae_supAuxLocalTime_continuous hθ] with f hf
  intro s hs
  have hm0 : 0 ≤ supAuxLocalTime θ f s := hf.1 ▸ hf.2.1 (zero_le : 0 ≤ s)
  have hO := (supOccupation_sub_mem hε f (show (0 : ℝ≥0) ≤ s from zero_le)).2
  simp only [supOccupation_zero, NNReal.coe_zero, sub_zero] at hO
  have hOn := supOccupation_nonneg hε.le f s
  have hw := abs_occupationCorrection_le hθ hε s f
  have hM := hf.2.1 hs
  have hst : ε⁻¹ * (s : ℝ) ≤ (T : ℝ) / ε := by
    rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hs) (inv_pos.mpr hε).le
  have hh := (abs_add_le (supOccupation ε f s - supAuxLocalTime θ f s)
    (occupationCorrection θ ε s f)).trans
      (add_le_add (abs_sub _ _) le_rfl)
  rw [abs_of_nonneg hOn, abs_of_nonneg hm0] at hh
  exact hh.trans (by linarith only [hO, hst, hM, hw])

/-- The stopped error has an integrable square at each bounded horizon. -/
theorem integrable_sq_errorMartingale_stopped {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) (n : ℕ) {σ : DLoc → ℝ≥0∞} (hσ : IsStoppingTime DLoc.filtration σ)
    (t : ℝ≥0) :
    Integrable (fun f => (errorMartingale θ ε (errStopTime n σ t f) f) ^ 2)
      (stableLocalLaw θ : Measure DLoc) := by
  let a : ℝ := (t : ℝ) / ε + 2 * supCorrectionBound θ ε
  have hi : Integrable (fun f => (a + supAuxLocalTime θ f t) ^ 2)
      (stableLocalLaw θ : Measure DLoc) := by
    have hh := ((integrable_const (a ^ 2)).add
      ((integrable_supAuxLocalTime hθ t).const_mul (2 * a))).add
        (integrable_sq_supAuxLocalTime hθ t)
    convert hh using 1
    funext f
    simp only [Pi.add_apply]
    ring
  have hm := ((stronglyMeasurable_errStopTime_eval
    (isStronglyProgressive_errorMartingale hθ hε) n hσ t).mono (DLoc.filtration.le t)).pow 2
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_abs_errorMartingale_le hθ hε t] with f hf
  have hb := hf (errStopTime n σ t f) (errStopTime_le n σ t f)
  have hb' : |errorMartingale θ ε (errStopTime n σ t f) f| ≤ a + supAuxLocalTime θ f t := by
    dsimp [a]
    linarith only [hb]
  have hsq := sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hb') |>.mpr hb'
  change ‖errorMartingale θ ε (errStopTime n σ t f) f ^ 2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using hsq

end BGW.StableTrees
