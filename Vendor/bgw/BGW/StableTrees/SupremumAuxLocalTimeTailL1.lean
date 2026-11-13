/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimePotential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Convergence in mean of discounted occupation tails

Half-rate growth dominates the expected absolute cumulative errors. The ordinary cumulative
formula then transfers this convergence to discounted occupation tails.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Discounted absolute cumulative errors tend to zero in mean over time. -/
theorem tendsto_integral_discounted_supAuxError {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q : ℝ} (hq : 0 < q) (s : ℝ≥0) :
    Tendsto (fun ε : ℝ => ∫ t in Ioi (s : ℝ), Real.exp (-q * t) *
        (∫ f, |supOccupation ε f t.toNNReal - supAuxLocalTime θ f t.toNNReal|
          ∂(stableLocalLaw θ : Measure DLoc))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let C := (q / 2) ^ (1 / θ) / (q / 2)
  have hm (ε : ℝ) : Measurable (fun t : ℝ => ∫ f,
      |supOccupation ε f t.toNNReal - supAuxLocalTime θ f t.toNNReal|
      ∂(stableLocalLaw θ : Measure DLoc)) := by
    have hA := measurable_supOccupation_uncurry.comp
      ((measurable_const : Measurable (fun _ : ℝ × DLoc => ε)).prodMk
        ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))
    have hM := (measurable_supAuxLocalTime_uncurry θ).comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
    have hh := (hA.sub hM).norm.stronglyMeasurable.integral_prod_right'
      (ν := (stableLocalLaw θ : Measure DLoc))
    simpa only [Function.comp_def, Pi.sub_apply, Real.norm_eq_abs] using hh.measurable
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ t ∂(volume.restrict (Ioi (s : ℝ))),
      ‖Real.exp (-q * t) * (∫ f,
        |supOccupation ε f t.toNNReal - supAuxLocalTime θ f t.toNNReal|
        ∂(stableLocalLaw θ : Measure DLoc))‖ ≤ Real.exp (-(q / 2) * t) * (2 * C) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 := s.coe_nonneg.trans ht.le
    have hO := integrable_supOccupation θ hε t.toNNReal
    have hM := integrable_supAuxLocalTime hθ t.toNNReal
    have hmean : (∫ f, |supOccupation ε f t.toNNReal - supAuxLocalTime θ f t.toNNReal|
        ∂(stableLocalLaw θ : Measure DLoc)) ≤
        Real.exp ((q / 2) * t) * C + Real.exp ((q / 2) * t) * C := by
      calc
        _ ≤ ∫ f, supOccupation ε f t.toNNReal + supAuxLocalTime θ f t.toNNReal
            ∂(stableLocalLaw θ : Measure DLoc) := by
          apply integral_mono_ae (hO.sub hM).abs (hO.add hM)
          filter_upwards [ae_supAuxLocalTime_nonneg hθ] with f hf
          simpa only [Pi.sub_apply, Pi.add_apply, abs_of_nonneg (supOccupation_nonneg hε.le f _),
            abs_of_nonneg (hf _)] using
            (abs_sub (supOccupation ε f t.toNNReal) (supAuxLocalTime θ f t.toNNReal))
        _ = _ := integral_add hO hM
        _ ≤ _ := add_le_add
          (by simpa only [Real.coe_toNNReal _ ht0] using
            integral_supOccupation_le_exp hθ (half_pos hq) hε t.toNNReal)
          (by simpa only [Real.coe_toNNReal _ ht0] using
            integral_supAuxLocalTime_le_exp hθ (half_pos hq) t.toNNReal)
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (integral_nonneg fun f => abs_nonneg _))]
    calc
      _ ≤ Real.exp (-q * t) *
          (Real.exp ((q / 2) * t) * C + Real.exp ((q / 2) * t) * C) :=
        mul_le_mul_of_nonneg_left hmean (Real.exp_pos _).le
      _ = (Real.exp (-q * t) * Real.exp ((q / 2) * t)) * (2 * C) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring
  have hl := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (s : ℝ))) (fun t => Real.exp (-(q / 2) * t) * (2 * C))
    (Eventually.of_forall fun ε => Measurable.aestronglyMeasurable
      ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul (hm ε))) hb
    ((integrableOn_exp_mul_Ioi (by linarith : -(q / 2) < 0) s).mul_const (2 * C))
    (ae_of_all _ fun t => (tendsto_integral_abs_supOccupation_sub hθ t.toNNReal).const_mul
      (Real.exp (-q * t)))
  simpa only [Function.comp_def, Pi.mul_apply, id_eq, mul_zero, integral_zero] using hl

/-- The discounted cumulative formula separates the endpoint term explicitly. -/
theorem discounted_cumulative_eq_primitive {m : ℝ → ℝ} {q : ℝ} (hq : 0 < q) (s a : ℝ)
    (hi : IntegrableOn (fun t => Real.exp (-q * t) * m t) (Ioi s)) :
    q * (∫ t in Ioi s, Real.exp (-q * t) * (m t - a)) =
      q * (∫ t in Ioi s, Real.exp (-q * t) * m t) - Real.exp (-q * s) * a := by
  have hc := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hq) s).mul_const a
  simp_rw [mul_sub]
  rw [integral_sub hi hc, integral_mul_const,
    integral_exp_mul_Ioi (neg_neg_of_pos hq)]
  field_simp

/-- The discounted difference of occupation and clock cumulatives is product integrable. -/
theorem integrable_exp_supAuxDifference_prod {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) (s : ℝ≥0) :
    Integrable (fun p : ℝ × DLoc => Real.exp (-q * p.1) *
      (supOccupation ε p.2 p.1.toNNReal - supAuxLocalTime θ p.2 p.1.toNNReal))
      ((volume.restrict (Ioi (s : ℝ))).prod (stableLocalLaw θ : Measure DLoc)) := by
  apply ((integrable_exp_supOccupation_prod hθ hq hε s).sub
    (integrable_exp_supAuxLocalTime_prod hθ hq s)).congr
  filter_upwards with p
  exact (mul_sub _ _ _).symm

/-- The cumulative error controls the difference of discounted clock tails in mean. -/
theorem integral_abs_supAuxOccupationTail_sub_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) (s : ℝ≥0) :
    (∫ f, |supAuxOccupationTail q ε s f - supAuxDiscountedTail θ q s f|
      ∂(stableLocalLaw θ : Measure DLoc)) ≤
      q * (∫ t in Ioi (s : ℝ), Real.exp (-q * t) *
        (∫ f, |supOccupation ε f t.toNNReal - supAuxLocalTime θ f t.toNNReal|
          ∂(stableLocalLaw θ : Measure DLoc))) +
      Real.exp (-q * s) * (∫ f, |supOccupation ε f s - supAuxLocalTime θ f s|
        ∂(stableLocalLaw θ : Measure DLoc)) := by
  let P : Measure DLoc := stableLocalLaw θ
  let U : DLoc → ℝ := fun f => ∫ t in Ioi (s : ℝ), Real.exp (-q * t) *
    (supOccupation ε f t.toNNReal - supAuxLocalTime θ f t.toNNReal)
  have hD := integrable_exp_supAuxDifference_prod hθ hq hε s
  have hUi : Integrable U P := hD.integral_prod_right
  have hE : Integrable (fun f => supOccupation ε f s - supAuxLocalTime θ f s) P :=
    (integrable_supOccupation θ hε s).sub (integrable_supAuxLocalTime hθ s)
  have he : (fun f => supAuxOccupationTail q ε s f - supAuxDiscountedTail θ q s f) =ᵐ[P]
      fun f => q * U f - Real.exp (-q * s) *
        (supOccupation ε f s - supAuxLocalTime θ f s) := by
    filter_upwards [ae_eval_zero_stableLocalLaw hθ,
      ae_supAuxDiscountedTail_eq_cumulative hθ hq s,
      (integrable_exp_supOccupation_prod hθ hq hε s).prod_left_ae,
      (integrable_exp_supAuxLocalTime_prod hθ hq s).prod_left_ae] with f hf hc hO hM
    rw [supAuxOccupationTail_eq_cumulative hq hε f hf s, hc,
      discounted_cumulative_eq_primitive hq (s : ℝ) _ hO,
      discounted_cumulative_eq_primitive hq (s : ℝ) _ hM]
    have hi := integral_sub hO hM
    have hU : U f = (∫ t in Ioi (s : ℝ), Real.exp (-q * t) * supOccupation ε f t.toNNReal) -
        ∫ t in Ioi (s : ℝ), Real.exp (-q * t) * supAuxLocalTime θ f t.toNNReal := by
      rw [← hi]
      apply integral_congr_ae
      exact ae_of_all _ fun t => mul_sub _ _ _
    rw [hU]
    ring
  have hUbound : (∫ f, |U f| ∂P) ≤
      ∫ t in Ioi (s : ℝ), Real.exp (-q * t) *
        (∫ f, |supOccupation ε f t.toNNReal - supAuxLocalTime θ f t.toNNReal| ∂P) := by
    calc
      _ ≤ ∫ f, (∫ t in Ioi (s : ℝ),
          |Real.exp (-q * t) * (supOccupation ε f t.toNNReal -
            supAuxLocalTime θ f t.toNNReal)|) ∂P := by
        apply integral_mono_ae hUi.abs hD.integral_norm_prod_right
        filter_upwards with f
        simpa only [U, Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun t : ℝ => Real.exp (-q * t) *
            (supOccupation ε f t.toNNReal - supAuxLocalTime θ f t.toNNReal))
      _ = _ := by
        have hs := integral_integral_swap
          (f := fun t f => |Real.exp (-q * t) *
            (supOccupation ε f t.toNNReal - supAuxLocalTime θ f t.toNNReal)|) hD.abs
        rw [← hs]
        apply integral_congr_ae
        filter_upwards with t
        simp_rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact integral_const_mul _ _
  calc
    _ = ∫ f, |q * U f - Real.exp (-q * s) *
        (supOccupation ε f s - supAuxLocalTime θ f s)| ∂P :=
      integral_congr_ae (he.mono fun f hf => congrArg abs hf)
    _ ≤ ∫ f, q * |U f| + Real.exp (-q * s) *
        |supOccupation ε f s - supAuxLocalTime θ f s| ∂P := by
      apply integral_mono_ae ((hUi.const_mul q).sub (hE.const_mul _)).abs
        ((hUi.abs.const_mul q).add (hE.abs.const_mul _))
      filter_upwards with f
      simpa only [Pi.sub_apply, Pi.add_apply, abs_mul, abs_of_pos hq,
        abs_of_pos (Real.exp_pos _)] using
        abs_sub (q * U f) (Real.exp (-q * s) * (supOccupation ε f s - supAuxLocalTime θ f s))
    _ = q * (∫ f, |U f| ∂P) + Real.exp (-q * s) *
        (∫ f, |supOccupation ε f s - supAuxLocalTime θ f s| ∂P) := by
      rw [integral_add (hUi.abs.const_mul q) (hE.abs.const_mul _), integral_const_mul,
        integral_const_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hUbound hq.le) le_rfl

/-- Discounted occupation tails converge to the constructed Stieltjes tail in mean. -/
theorem tendsto_integral_abs_supAuxOccupationTail_sub {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q : ℝ} (hq : 0 < q) (s : ℝ≥0) :
    Tendsto (fun ε : ℝ => ∫ f,
      |supAuxOccupationTail q ε s f - supAuxDiscountedTail θ q s f|
      ∂(stableLocalLaw θ : Measure DLoc)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hl := ((tendsto_integral_discounted_supAuxError hθ hq s).const_mul q).add
    ((tendsto_integral_abs_supOccupation_sub hθ s).const_mul (Real.exp (-q * s)))
  simp only [mul_zero, add_zero] at hl
  apply squeeze_zero' (Eventually.of_forall fun ε => integral_nonneg fun f => abs_nonneg _) _ hl
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact integral_abs_supAuxOccupationTail_sub_le hθ hq hε s

end BGW.StableTrees
