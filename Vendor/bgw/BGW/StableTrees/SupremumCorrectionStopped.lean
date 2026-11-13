/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCorrectionSampling

/-!
# Stopping progressive martingales with almost surely right continuous paths

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Continuous-time stopping for a progressive martingale with right continuous paths on a
single event of full probability. The stopping time itself may be unbounded. -/
theorem martingale_stoppedProcess_of_ae_rightContinuous {P : Measure DLoc}
    [IsProbabilityMeasure P] {M : ℝ≥0 → DLoc → ℝ}
    (hM : Martingale M DLoc.filtration P)
    (hprog : IsStronglyProgressive DLoc.filtration M)
    (hright : ∀ᵐ f ∂P, ∀ r, ContinuousWithinAt (fun s => M s f) (Ici r) r)
    {τ : DLoc → WithTop ℝ≥0} (hτ : IsStoppingTime DLoc.filtration τ) :
    Martingale (stoppedProcess M τ) DLoc.filtration P := by
  have hadapt := hprog.stronglyAdapted_stoppedProcess hτ
  have hi (t : ℝ≥0) : Integrable (stoppedProcess M τ t) P := by
    have hh := stoppedValue_ae_eq_condExp_of_ae_rightContinuous hM hprog hright
      ((isStoppingTime_const _ t).min hτ) (fun _ => min_le_left _ _)
    exact integrable_condExp.congr hh.symm
  refine ⟨hadapt, fun s t hst => ?_⟩
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (DLoc.filtration.le s) (hi t)
    (fun _ _ _ => (hi s).integrableOn) ?_ (hadapt s).aestronglyMeasurable
  intro A hA _
  let E : Set DLoc := {f | τ f ≤ s}
  have hE : MeasurableSet[DLoc.filtration s] E := hτ s
  have hEm : MeasurableSet E := DLoc.filtration.le s _ hE
  have hfirst : (∫ f in A ∩ E, stoppedProcess M τ s f ∂P) =
      ∫ f in A ∩ E, stoppedProcess M τ t f ∂P := by
    apply setIntegral_congr_fun ((DLoc.filtration.le s) _ (hA.inter hE))
    intro f hf
    rw [stoppedProcess_eq_of_ge hf.2,
      stoppedProcess_eq_of_ge (hf.2.trans (WithTop.coe_le_coe.mpr hst))]
  let ρ : DLoc → WithTop ℝ≥0 := fun f => max (s : WithTop ℝ≥0) (min (t : WithTop ℝ≥0) (τ f))
  have hρ : IsStoppingTime DLoc.filtration ρ :=
    (isStoppingTime_const _ s).max ((isStoppingTime_const _ t).min hτ)
  have hρle (f : DLoc) : ρ f ≤ t := max_le (WithTop.coe_le_coe.mpr hst) (min_le_left _ _)
  have hρge (f : DLoc) : (s : WithTop ℝ≥0) ≤ ρ f := le_max_left _ _
  have hsample := stoppedValue_ae_eq_condExp_of_ae_rightContinuous hM hprog hright hρ hρle
  have hB : MeasurableSet[DLoc.filtration s] (A \ E) := hA.diff hE
  have hBm : MeasurableSet (A \ E) := DLoc.filtration.le s _ hB
  have hsecond : (∫ f in A \ E, stoppedProcess M τ s f ∂P) =
      ∫ f in A \ E, stoppedProcess M τ t f ∂P := by
    calc
      _ = ∫ f in A \ E, M s f ∂P := by
        apply setIntegral_congr_fun hBm
        intro f hf
        exact stoppedProcess_eq_of_le (le_of_not_ge hf.2)
      _ = ∫ f in A \ E, M t f ∂P := hM.setIntegral_eq hst hB
      _ = ∫ f in A \ E, (P[M t | hρ.measurableSpace]) f ∂P :=
        (setIntegral_condExp hρ.measurableSpace_le (hM.integrable t)
          (hρ.le_measurableSpace_of_const_le hρge _ hB)).symm
      _ = ∫ f in A \ E, stoppedValue M ρ f ∂P :=
        setIntegral_congr_ae hBm (hsample.symm.mono (fun _ hf _ => hf))
      _ = _ := by
        apply setIntegral_congr_fun hBm
        intro f hf
        have hsr : (s : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) (τ f) :=
          le_min (WithTop.coe_le_coe.mpr hst) (le_of_not_ge hf.2)
        change M ((max (s : WithTop ℝ≥0) (min (t : WithTop ℝ≥0) (τ f))).untopA) f = _
        rw [max_eq_right hsr]
        rfl
  rw [← integral_inter_add_sdiff hEm (hi s).integrableOn,
    ← integral_inter_add_sdiff hEm (hi t).integrableOn, hfirst, hsecond]

end BGW.StableTrees
