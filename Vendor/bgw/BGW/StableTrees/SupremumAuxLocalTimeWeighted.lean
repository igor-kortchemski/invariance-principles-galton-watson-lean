/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeMeanBounds
public import BGW.StableTrees.SupremumAuxLocalTimeIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integrable discounted cumulative clocks

The half-rate first-moment bound gives product integrability. This precedes and justifies
conversion from extended integrals to the actual Stieltjes real integrals.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- A nonnegative process with an exponential first-moment bound has an integrable
more rapidly discounted time-path integral. -/
theorem integrable_exp_process_prod_of_mean_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {A : ℝ × Ω → ℝ} (hA : Measurable A)
    (hAi : ∀ t, Integrable (fun f => A (t, f)) μ)
    (hA0 : ∀ t, ∀ᵐ f ∂μ, 0 ≤ A (t, f)) {q C : ℝ} (hq : 0 < q) (s : ℝ≥0)
    (hmean : ∀ t : ℝ, 0 ≤ t → (∫ f, A (t, f) ∂μ) ≤ Real.exp ((q / 2) * t) * C) :
    Integrable (fun p : ℝ × Ω => Real.exp (-q * p.1) * A p)
      ((volume.restrict (Ioi (s : ℝ))).prod μ) := by
  have hF : Measurable (fun p : ℝ × Ω => Real.exp (-q * p.1) * A p) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul hA
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ fun t => (hAi t).const_mul (Real.exp (-q * t)), ?_⟩
  have hd : IntegrableOn (fun t => Real.exp (-(q / 2) * t) * C) (Ioi (s : ℝ)) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(q / 2) < 0) s).mul_const C
  have hm := hF.stronglyMeasurable.norm.integral_prod_right' (ν := μ)
  apply hd.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have he : (∫ f, ‖Real.exp (-q * t) * A (t, f)‖ ∂μ) =
      Real.exp (-q * t) * (∫ f, A (t, f) ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hA0 t] with f hf
    exact Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le hf)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun f => norm_nonneg _), he]
  calc
    _ ≤ Real.exp (-q * t) * (Real.exp ((q / 2) * t) * C) :=
      mul_le_mul_of_nonneg_left (hmean t (s.coe_nonneg.trans ht.le)) (Real.exp_pos _).le
    _ = _ := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Discounting the auxiliary clock gives an integrable time-path function at every rate. -/
theorem integrable_exp_supAuxLocalTime_prod {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q : ℝ} (hq : 0 < q) (s : ℝ≥0) :
    Integrable (fun p : ℝ × DLoc => Real.exp (-q * p.1) *
      supAuxLocalTime θ p.2 p.1.toNNReal)
      ((volume.restrict (Ioi (s : ℝ))).prod (stableLocalLaw θ : Measure DLoc)) := by
  apply integrable_exp_process_prod_of_mean_le
    ((measurable_supAuxLocalTime_uncurry θ).comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))
    (fun t => integrable_supAuxLocalTime hθ t.toNNReal)
    (fun t => (ae_supAuxLocalTime_nonneg hθ).mono fun f hf => hf t.toNNReal) hq s
  intro t ht
  simpa only [Function.comp_def, Real.coe_toNNReal _ ht] using
    integral_supAuxLocalTime_le_exp hθ (half_pos hq) t.toNNReal

/-- The occupation cumulative functions satisfy the same discounted product integrability. -/
theorem integrable_exp_supOccupation_prod {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) (s : ℝ≥0) :
    Integrable (fun p : ℝ × DLoc => Real.exp (-q * p.1) * supOccupation ε p.2 p.1.toNNReal)
      ((volume.restrict (Ioi (s : ℝ))).prod (stableLocalLaw θ : Measure DLoc)) := by
  apply integrable_exp_process_prod_of_mean_le
    (measurable_supOccupation_uncurry.comp
      (measurable_const.prodMk
        ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)))
    (fun t => integrable_supOccupation θ hε t.toNNReal)
    (fun t => ae_of_all _ fun f => supOccupation_nonneg hε.le f t.toNNReal) hq s
  intro t ht
  simpa only [Function.comp_def, Real.coe_toNNReal _ ht] using
    integral_supOccupation_le_exp hθ (half_pos hq) hε t.toNNReal

/-- Discounted clock increments are integrable on the time-path product. -/
theorem integrable_exp_supAuxIncrement_prod {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q : ℝ} (hq : 0 < q) (s : ℝ≥0) :
    Integrable (fun p : ℝ × DLoc => Real.exp (-q * p.1) *
      (supAuxLocalTime θ p.2 p.1.toNNReal - supAuxLocalTime θ p.2 s))
      ((volume.restrict (Ioi (s : ℝ))).prod (stableLocalLaw θ : Measure DLoc)) := by
  have hm := integrable_exp_supAuxLocalTime_prod hθ hq s
  have hc := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hq) (s : ℝ)).mul_prod
    (integrable_supAuxLocalTime hθ s)
  apply (hm.sub hc).congr
  filter_upwards with p
  exact (mul_sub _ _ _).symm

/-- The actual discounted Stieltjes tail equals the cumulative time integral almost surely. -/
theorem ae_supAuxDiscountedTail_eq_cumulative {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q : ℝ} (hq : 0 < q) (s : ℝ≥0) :
    supAuxDiscountedTail θ q s =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      fun f => q * ∫ t in Ioi (s : ℝ), Real.exp (-q * t) *
        (supAuxLocalTime θ f t.toNNReal - supAuxLocalTime θ f s) := by
  filter_upwards [ae_supAuxLocalTime_continuous hθ,
    (integrable_exp_supAuxIncrement_prod hθ hq s).prod_left_ae] with f hf hi
  exact (pathStieltjes_integral_exp ⟨hf.2.1, hf.2.2⟩ hq s hi).2

/-- The discounted Stieltjes tail is integrable at every positive rate. -/
theorem integrable_supAuxDiscountedTail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    (s : ℝ≥0) : Integrable (supAuxDiscountedTail θ q s) (stableLocalLaw θ : Measure DLoc) := by
  exact ((integrable_exp_supAuxIncrement_prod hθ hq s).integral_prod_right.const_mul q).congr
    (ae_supAuxDiscountedTail_eq_cumulative hθ hq s).symm

/-- Almost-everywhere measurability of the discounted tail (everywhere measurability of the
Stieltjes totalization of a raw `limsup` clock is not needed downstream; exact measurability, if
required later, comes from the totalized clock of the identification step). -/
theorem aemeasurable_supAuxDiscountedTail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    (s : ℝ≥0) : AEMeasurable (supAuxDiscountedTail θ q s) (stableLocalLaw θ : Measure DLoc) :=
  (integrable_supAuxDiscountedTail hθ hq s).aemeasurable

end BGW.StableTrees
