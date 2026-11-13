/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeWeighted
public import BGW.StableTrees.SupremumAuxLocalTimePrimitive
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Mean discounted potential of the auxiliary clock

The half-rate growth bound dominates cumulative occupation means. Ordinary dominated
convergence and Fubini identify the mean clock potential before any recurrence argument.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Fubini expresses the clock's discounted mean through its cumulative first moments. -/
theorem integral_supAuxDiscountedTail_eq_cumulative {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q : ℝ} (hq : 0 < q) :
    (∫ f, supAuxDiscountedTail θ q 0 f ∂(stableLocalLaw θ : Measure DLoc)) =
      q * ∫ t in Ioi (0 : ℝ), Real.exp (-q * t) *
        (∫ f, supAuxLocalTime θ f t.toNNReal ∂(stableLocalLaw θ : Measure DLoc)) := by
  have he : supAuxDiscountedTail θ q 0 =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      fun f => q * ∫ t in Ioi (0 : ℝ), Real.exp (-q * t) *
        supAuxLocalTime θ f t.toNNReal := by
    filter_upwards [ae_supAuxDiscountedTail_eq_cumulative hθ hq 0,
      ae_supAuxLocalTime_continuous hθ] with f hf hm
    simpa only [hm.1, sub_zero, NNReal.coe_zero] using hf
  rw [integral_congr_ae he, integral_const_mul]
  congr 1
  have hs := integral_integral_swap
    (f := fun t f => Real.exp (-q * t) * supAuxLocalTime θ f t.toNNReal)
    (integrable_exp_supAuxLocalTime_prod hθ hq 0)
  simp only [NNReal.coe_zero] at hs
  rw [← hs]
  apply integral_congr_ae
  filter_upwards with t
  exact integral_const_mul _ _

/-- The occupation resolvent is the discounted integral of cumulative occupation means. -/
theorem supOccupationResolvent_zero_eq_cumulative {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) :
    supOccupationResolvent θ q ε 0 =
      q * ∫ t in Ioi (0 : ℝ), Real.exp (-q * t) *
        (∫ f, supOccupation ε f t.toNNReal ∂(stableLocalLaw θ : Measure DLoc)) := by
  rw [← integral_supAuxOccupationTail_zero]
  have he : supAuxOccupationTail q ε 0 =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      fun f => q * ∫ t in Ioi (0 : ℝ), Real.exp (-q * t) * supOccupation ε f t.toNNReal := by
    filter_upwards [ae_eval_zero_stableLocalLaw hθ] with f hf
    simpa only [supOccupation_zero, sub_zero, NNReal.coe_zero] using
      supAuxOccupationTail_eq_cumulative hq hε f hf 0
  rw [integral_congr_ae he, integral_const_mul]
  congr 1
  have hs := integral_integral_swap
    (f := fun t f => Real.exp (-q * t) * supOccupation ε f t.toNNReal)
    (integrable_exp_supOccupation_prod hθ hq hε 0)
  simp only [NNReal.coe_zero] at hs
  rw [← hs]
  apply integral_congr_ae
  filter_upwards with t
  exact integral_const_mul _ _

/-- Half-rate domination passes the discounted cumulative means to the clock. -/
theorem tendsto_integral_discounted_supOccupation_mean {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q : ℝ} (hq : 0 < q) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (0 : ℝ), Real.exp (-q * t) *
        (∫ f, supOccupation ε f t.toNNReal ∂(stableLocalLaw θ : Measure DLoc)))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ t in Ioi (0 : ℝ), Real.exp (-q * t) *
        (∫ f, supAuxLocalTime θ f t.toNNReal ∂(stableLocalLaw θ : Measure DLoc)))) := by
  let C := (q / 2) ^ (1 / θ) / (q / 2)
  have hm (ε : ℝ) : Measurable (fun t : ℝ => ∫ f, supOccupation ε f t.toNNReal
      ∂(stableLocalLaw θ : Measure DLoc)) := by
    have hA := measurable_supOccupation_uncurry.comp
      ((measurable_const : Measurable (fun _ : ℝ × DLoc => ε)).prodMk
        ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))
    exact (hA.stronglyMeasurable.integral_prod_right'
      (ν := (stableLocalLaw θ : Measure DLoc))).measurable
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖Real.exp (-q * t) * (∫ f, supOccupation ε f t.toNNReal
        ∂(stableLocalLaw θ : Measure DLoc))‖ ≤ Real.exp (-(q / 2) * t) * C := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (integral_nonneg fun f => supOccupation_nonneg hε.le f _))]
    calc
      _ ≤ Real.exp (-q * t) * (Real.exp ((q / 2) * t) * C) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        simpa only [Real.coe_toNNReal _ ht.le] using
          integral_supOccupation_le_exp hθ (half_pos hq) hε t.toNNReal
      _ = _ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  apply tendsto_integral_filter_of_dominated_convergence
    (fun t => Real.exp (-(q / 2) * t) * C)
    (Eventually.of_forall fun ε => Measurable.aestronglyMeasurable
      ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul (hm ε))) hbound
    ((integrableOn_exp_mul_Ioi (by linarith : -(q / 2) < 0) 0).mul_const C)
  exact ae_of_all _ fun t => (tendsto_integral_supOccupation hθ t.toNNReal).const_mul _

/-- **Mean potential** `E ∫_0^∞ e^{-qt} dL^aux_t = h_q(0) = Φ/q` (`= 1` at `q = 1`: the clock is
non-trivial; the normalization `c = 1`). -/
theorem integral_supAuxDiscountedTail_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    ∫ f, supAuxDiscountedTail θ q 0 f ∂(stableLocalLaw θ : Measure DLoc) =
      supPotential θ q 0 := by
  have hc := (tendsto_integral_discounted_supOccupation_mean hθ hq).const_mul q
  rw [← integral_supAuxDiscountedTail_eq_cumulative hθ hq] at hc
  have hr := (tendstoUniformlyOn_supOccupationResolvent hθ hq).tendsto_at
    (show (0 : ℝ) ∈ Ici 0 from le_rfl)
  apply tendsto_nhds_unique hc
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact supOccupationResolvent_zero_eq_cumulative hθ hq hε

end BGW.StableTrees
