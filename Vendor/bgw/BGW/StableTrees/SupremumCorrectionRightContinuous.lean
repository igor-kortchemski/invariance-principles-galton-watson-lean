/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCorrectionPositive
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Right continuity of the positive-rate errors

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem continuous_nnreal_head {a : ℝ → ℝ} (ha : IntegrableOn a (Ioi (0 : ℝ))) :
    Continuous (fun t : ℝ≥0 => ∫ s in Ioc (0 : ℝ) t, a s) := by
  have hc : Continuous (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, a s
      ∂volume.restrict (Ioi (0 : ℝ))) := (intervalIntegral.continuous_primitive
    (μ := volume.restrict (Ioi (0 : ℝ)))
      (fun _ _ => (show Integrable a (volume.restrict (Ioi (0 : ℝ))) from ha).intervalIntegrable)
      0).comp
      continuous_subtype_val
  apply hc.congr
  intro t
  rw [intervalIntegral.integral_of_le t.coe_nonneg,
    Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]

/-- Almost surely the positive-rate process is right continuous at all times. -/
theorem ae_rightContinuous_discountedErrorMartingale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s => discountedErrorMartingale θ q ε s f) (Ici t) t := by
  filter_upwards [ae_supAuxLocalTime_continuous hθ,
    (integrable_exp_supAuxLocalTime_prod hθ hq 0).prod_left_ae] with f hf hi
  change IntegrableOn (fun s : ℝ => Real.exp (-q * s) * supAuxLocalTime θ f s.toNNReal)
    (Ioi (0 : ℝ)) at hi
  have hO : Continuous (fun t => supOccupationDiscountedHead q ε t f) :=
    continuous_nnreal_head (integrableOn_supAuxKernel_exp hq hε 0 f)
  have he : Continuous (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) := by fun_prop
  have hM : Continuous (fun t => supAuxDiscountedHead θ q t f) :=
    (he.mul hf.2.2).add ((continuous_nnreal_head hi).const_mul q)
  intro t
  have hR := continuousWithinAt_Ioi_iff_Ici.mp
    ((isCadlag_supReflectedFrom 0 f).isRightContinuous t)
  have hu := (continuousOn_supOccupationResolvent hθ hq hε _
    (supReflectedFrom_nonneg 0 f t)).comp hR
      (fun s _ => supReflectedFrom_nonneg 0 f s)
  have hv := (continuous_supPotential hθ hq).continuousAt.comp_continuousWithinAt hR
  exact (hO.continuousWithinAt.sub hM.continuousWithinAt).add
    (he.continuousWithinAt.mul (hu.sub hv))

end BGW.StableTrees
