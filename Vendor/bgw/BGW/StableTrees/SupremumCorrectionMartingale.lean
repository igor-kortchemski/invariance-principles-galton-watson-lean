/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCorrectionEpoch
public import BGW.StableTrees.SupremumCorrectionBound
public import BGW.StableTrees.SupremumCorrectionRightContinuous
public import BGW.StableTrees.SupremumCorrectionStopped
import BGW.StableTrees.SupremumAuxLocalTimeConditionalLimit

/-!
# The localized zero-rate error martingale

Positive-rate martingales are stopped first. Simultaneous compact-state domination then
passes the centered zero-rate limit through deterministic conditional expectations.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The error is integrable at every bounded stopping epoch. -/
private theorem integrable_errorMartingale_stopped {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) (n : ℕ) {σ : DLoc → ℝ≥0∞} (hσ : IsStoppingTime DLoc.filtration σ)
    (t : ℝ≥0) :
    Integrable (fun f => errorMartingale θ ε (errStopTime n σ t f) f)
      (stableLocalLaw θ : Measure DLoc) := by
  have hm : AEStronglyMeasurable
      (fun f => errorMartingale θ ε (errStopTime n σ t f) f)
      (stableLocalLaw θ : Measure DLoc) :=
    ((stronglyMeasurable_errStopTime_eval (isStronglyProgressive_errorMartingale hθ hε)
      n hσ t).mono (DLoc.filtration.le t)).aestronglyMeasurable
  exact MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    ((memLp_two_iff_integrable_sq hm).mpr (integrable_sq_errorMartingale_stopped hθ hε n hσ t))

/-- Stopping the positive-rate martingale and subtracting its deterministic initial correction
preserves the martingale property. -/
private theorem martingale_centered_discounted_stopped {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) (n : ℕ) {σ : DLoc → ℝ≥0∞}
    (hσ : IsStoppingTime DLoc.filtration σ) :
    Martingale (fun t f => discountedErrorMartingale θ q ε (errStopTime n σ t f) f -
      (supOccupationResolvent θ q ε 0 - supPotential θ q 0)) DLoc.filtration
        (stableLocalLaw θ : Measure DLoc) := by
  have hstop := martingale_stoppedProcess_of_ae_rightContinuous
    (martingale_discountedErrorMartingale hθ hq hε)
    (isStronglyProgressive_discountedErrorMartingale hθ hq hε)
    (ae_rightContinuous_discountedErrorMartingale hθ hq hε)
    (hσ.min (isStoppingTime_errCutoff n))
  have hc : Martingale (fun (_ : ℝ≥0) (_ : DLoc) =>
      supOccupationResolvent θ q ε 0 - supPotential θ q 0) DLoc.filtration
        (stableLocalLaw θ : Measure DLoc) :=
    martingale_const DLoc.filtration (stableLocalLaw θ : Measure DLoc) _
  have ha : StronglyAdapted DLoc.filtration (fun t f =>
      discountedErrorMartingale θ q ε (errStopTime n σ t f) f -
        (supOccupationResolvent θ q ε 0 - supPotential θ q 0)) := fun t =>
    (stronglyMeasurable_errStopTime_eval
      (isStronglyProgressive_discountedErrorMartingale hθ hq hε) n hσ t).sub
        stronglyMeasurable_const
  apply (hstop.sub hc).congr ha
  intro t
  apply ae_of_all
  intro f
  simp only [Pi.sub_apply, errStopTime_eval_eq_stoppedProcess]

/-- The zero-rate error stopped at an arbitrary stopping time and the localizing cutoff
is a martingale. Localization of the positive-rate processes precedes the centered limit. -/
theorem martingale_errorMartingale_stopped {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) {σ : DLoc → ℝ≥0∞} (hσ : IsStoppingTime DLoc.filtration σ) :
    Martingale (fun t f => errorMartingale θ ε (errStopTime n σ t f) f) DLoc.filtration
      (stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  let D : ℝ≥0 → DLoc → ℝ := fun t f => errorMartingale θ ε (errStopTime n σ t f) f
  let Q : ℝ → ℝ≥0 → DLoc → ℝ := fun q t f =>
    discountedErrorMartingale θ q ε (errStopTime n σ t f) f -
      (supOccupationResolvent θ q ε 0 - supPotential θ q 0)
  have hDi (r : ℝ≥0) : Integrable (D r) P := integrable_errorMartingale_stopped hθ hε n hσ r
  refine ⟨fun r => stronglyMeasurable_errStopTime_eval
    (isStronglyProgressive_errorMartingale hθ hε) n hσ r, fun s t hst => ?_⟩
  obtain ⟨q₀, C, hq₀, hbound⟩ := ae_abs_discountedErrorMartingale_le hθ hε (n : ℝ) t
  let q : ℕ → ℝ := fun k => q₀ / ((k : ℝ) + 2)
  have hqpos (k : ℕ) : 0 < q k := div_pos hq₀ (by positivity)
  have hqlt (k : ℕ) : q k < q₀ := (div_lt_self hq₀ (by norm_cast; omega))
  have hqt : Tendsto q atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall hqpos⟩
    exact Tendsto.div_atTop tendsto_const_nhds
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hQM (k : ℕ) : Martingale (Q (q k)) DLoc.filtration P :=
    martingale_centered_discounted_stopped hθ (hqpos k) hε n hσ
  have hlim (r : ℝ≥0) : ∀ᵐ f ∂P, Tendsto (fun k => Q (q k) r f) atTop (𝓝 (D r f)) := by
    filter_upwards [ae_tendsto_discountedErrorMartingale hθ hε] with f hf
    exact (hf (errStopTime n σ r f)).comp hqt
  have hQB : ∀ᵐ f ∂P, ∀ r ≤ t, ∀ k : ℕ,
      |Q (q k) r f| ≤ 2 * ((t : ℝ) / ε + supAuxLocalTime θ f t + C) := by
    filter_upwards [hbound, ae_supReflectedFrom_le_of_le_errCutoff hθ,
      ae_supAuxLocalTime_continuous hθ, ae_eval_zero_stableLocalLaw hθ] with f hf hR hM h0
    intro r hr k
    have hepoch := (errStopTime_le n σ r f).trans hr
    have hval := hf (errStopTime n σ r f) hepoch
      (hR n _ (errStopTime_le_cutoff n σ r f)) (q k) (hqpos k) (hqlt k)
    have hR0 : supReflectedFrom 0 f 0 = 0 := by simp [supReflectedFrom, supRunning_zero, h0]
    have hcenter := hf 0 (zero_le : 0 ≤ t)
      (by rw [hR0]; positivity) (q k) (hqpos k) (hqlt k)
    have hzero : discountedErrorMartingale θ (q k) ε 0 f =
        supOccupationResolvent θ (q k) ε 0 - supPotential θ (q k) 0 := by
      simp [discountedErrorMartingale, supOccupationDiscountedHead, supAuxDiscountedHead,
        hM.1, hR0]
    rw [hzero] at hcenter
    exact (abs_sub _ _).trans (by linarith only [hval, hcenter])
  have hl (r : ℝ≥0) (hr : r ≤ t) :
      Tendsto (fun k => ∫ f, |Q (q k) r f - D r f| ∂P) atTop (𝓝 0) := by
    let H : DLoc → ℝ := fun f =>
      2 * ((t : ℝ) / ε + supAuxLocalTime θ f t + C) + |D r f|
    have hHi : Integrable H P :=
      (((integrable_const ((t : ℝ) / ε)).add (integrable_supAuxLocalTime hθ t)).add
        (integrable_const C) |>.const_mul 2).add (hDi r).abs
    have hconv := tendsto_integral_of_dominated_convergence (μ := P)
      (F := fun k f => |Q (q k) r f - D r f|) (f := fun _ => (0 : ℝ)) H
      (fun k => by
        simpa only [Pi.sub_apply] using
          ((hQM k).integrable r |>.sub (hDi r)).abs.aestronglyMeasurable) hHi
      (fun k => hQB.mono (fun f hf => by
        rw [Real.norm_eq_abs, abs_abs]
        exact (abs_sub _ _).trans (add_le_add (hf r hr k) le_rfl)))
      ((hlim r).mono (fun f hf => by
        simpa only [sub_self, abs_zero] using
          (hf.sub (tendsto_const_nhds (x := D r f))).abs))
    simpa only [integral_zero] using hconv
  exact condExp_eq_of_integral_abs_tendsto (DLoc.filtration s) (hDi t) (hDi s)
    (fun k => (hQM k).integrable t) (fun k => (hQM k).integrable s)
    (fun k => (hQM k).condExp_ae_eq hst) (hl t le_rfl) (hl s hst)

end BGW.StableTrees
