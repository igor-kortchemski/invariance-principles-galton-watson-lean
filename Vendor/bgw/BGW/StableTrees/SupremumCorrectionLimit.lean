/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCorrectionPath
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Centered zero-rate limit of the error process

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem tendsto_discounted_head {a : ℝ → ℝ} (ha : Measurable a) (t : ℝ≥0)
    {C : ℝ} (hb : ∀ s ∈ Ioc (0 : ℝ) t, |a s| ≤ C) :
    Tendsto (fun q : ℝ => ∫ s in Ioc (0 : ℝ) t, Real.exp (-q * s) * a s)
      (𝓝[>] 0) (𝓝 (∫ s in Ioc (0 : ℝ) t, a s)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
  · exact Eventually.of_forall (fun q =>
      ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul ha).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with q hq
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (hb s hs) (Real.exp_pos _).le).trans
      (mul_le_of_le_one_left ((abs_nonneg _).trans (hb s hs))
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq.le) hs.1.le)))
  · exact integrableOn_const (by simp)
  · filter_upwards with s
    have hc : Continuous (fun q : ℝ => Real.exp (-q * s) * a s) := by fun_prop
    simpa only [neg_zero, zero_mul, Real.exp_zero, one_mul] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- The centered positive-rate errors converge at all times on a single full-measure event. -/
theorem ae_tendsto_discountedErrorMartingale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      Tendsto (fun q : ℝ => discountedErrorMartingale θ q ε t f -
          (supOccupationResolvent θ q ε 0 - supPotential θ q 0))
        (𝓝[>] 0) (𝓝 (errorMartingale θ ε t f)) := by
  filter_upwards [ae_supAuxLocalTime_continuous hθ, ae_eval_zero_stableLocalLaw hθ]
    with f hf h0
  intro t
  have hmR : Measurable (fun s : ℝ => supReflectedFrom 0 f s.toNNReal) :=
    DLoc.measurable_eval₂.comp
      ((measurable_const (a := supReflectedFromLoc 0 f)).prodMk measurable_real_toNNReal)
  have hO := tendsto_discounted_head
    (a := fun s => supOccKernel ε (supReflectedFrom 0 f s.toNNReal))
    ((measurable_supOccKernel ε).comp hmR) t (C := ε⁻¹)
    (fun s _ => by
      rw [abs_of_nonneg (supOccKernel_mem_Icc hε _).1]
      exact (supOccKernel_mem_Icc hε _).2)
  have hM := tendsto_discounted_head
    (a := fun s => supAuxLocalTime θ f s.toNNReal)
    (hf.2.2.measurable.comp measurable_real_toNNReal) t
    (C := supAuxLocalTime θ f t) (fun s hs => by
      have hs0 : (0 : ℝ≥0) ≤ s.toNNReal := zero_le
      have hst : s.toNNReal ≤ t := (Real.toNNReal_le_iff_le_coe).mpr hs.2
      rw [abs_of_nonneg (hf.1 ▸ hf.2.1 hs0)]
      exact hf.2.1 hst)
  have he : Tendsto (fun q : ℝ => Real.exp (-q * (t : ℝ))) (𝓝[>] 0) (𝓝 1) := by
    have hc : Continuous (fun q : ℝ => Real.exp (-q * (t : ℝ))) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hq : Tendsto (fun q : ℝ => q) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hhead := (he.mul (tendsto_const_nhds (x := supAuxLocalTime θ f t))).add (hq.mul hM)
  have hcorr := (tendstoLocallyUniformlyOn_supOccupationResolvent_sub hθ hε).tendsto_at
    (supReflectedFrom_nonneg 0 f t)
  have hcenter := (tendstoLocallyUniformlyOn_supOccupationResolvent_sub hθ hε).tendsto_at
    (show (0 : ℝ) ∈ Ici 0 from le_rfl)
  have hlim := ((hO.sub hhead).add (he.mul hcorr)).sub hcenter
  rw [← supOccupation_eq_integral_supOccKernel f h0 t] at hlim
  simpa only [discountedErrorMartingale, supOccupationDiscountedHead,
    supAuxDiscountedHead, one_mul, zero_mul, add_zero, errorMartingale,
    occupationCorrection, add_sub_assoc] using hlim

end BGW.StableTrees
