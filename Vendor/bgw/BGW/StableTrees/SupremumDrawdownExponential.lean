/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Exponential tails and transforms for the drawdown clock

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace BGW.StableTrees

/-- The strict upper tail of a positive-rate exponential law. -/
theorem expMeasure_Ioi_nonneg {r : ℝ} (hr : 0 < r) {y : ℝ} (hy : 0 ≤ y) :
    expMeasure r (Ioi y) = ENNReal.ofReal (Real.exp (-(r * y))) := by
  let := isProbabilityMeasure_expMeasure hr
  have he : expMeasure r (Iic y) = ENNReal.ofReal (1 - Real.exp (-(r * y))) := by
    rw [← ofReal_cdf, cdf_expMeasure_eq hr, ite_eq_left hy]
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ, he,
    ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
  apply ENNReal.sub_sub_cancel (by simp)
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hr.le hy))

/-- The exponential moment on its finite domain, in nonnegative integral form. -/
theorem lintegral_exp_mul_expMeasure {r c : ℝ} (hr : 0 < r) (hc : c < r) :
    ∫⁻ t, ENNReal.ofReal (Real.exp (c * t)) ∂expMeasure r =
      ENNReal.ofReal (r / (r - c)) := by
  have hd : Measurable (exponentialPDF r) :=
    (measurable_exponentialPDFReal r).ennreal_ofReal
  change (∫⁻ t, ENNReal.ofReal (Real.exp (c * t)) ∂volume.withDensity (exponentialPDF r)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume hd (by fun_prop)]
  have he : (exponentialPDF r * fun t => ENNReal.ofReal (Real.exp (c * t))) =
      (Ici (0 : ℝ)).indicator (fun t => ENNReal.ofReal (r * Real.exp ((c - r) * t))) := by
    funext t
    by_cases ht : 0 ≤ t
    · rw [Pi.mul_apply, exponentialPDF_of_nonneg ht,
        indicator_of_mem (show t ∈ Ici 0 from ht), ← ENNReal.ofReal_mul
          (mul_nonneg hr.le (Real.exp_pos _).le)]
      congr 1
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    · rw [Pi.mul_apply, exponentialPDF_of_neg (lt_of_not_ge ht), zero_mul,
        indicator_of_notMem (show t ∉ Ici 0 from ht)]
  rw [he, lintegral_indicator measurableSet_Ici]
  have hi : IntegrableOn (fun t : ℝ => r * Real.exp ((c - r) * t)) (Ici 0) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      (integrableOn_exp_mul_Ioi (sub_neg.mpr hc) 0)).const_mul r
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun t => mul_nonneg hr.le (Real.exp_pos _).le)]
  congr 1
  rw [integral_const_mul, integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (sub_neg.mpr hc)]
  simp only [mul_zero, Real.exp_zero]
  field_simp [ne_of_lt (sub_neg.mpr hc), ne_of_gt (sub_pos.mpr hc)]
  ring

/-- Exponential moments are integrable on their finite domain, with the usual value. -/
theorem integral_exp_mul_expMeasure {r c : ℝ} (hr : 0 < r) (hc : c < r) :
    Integrable (fun t : ℝ => Real.exp (c * t)) (expMeasure r) ∧
      (∫ t, Real.exp (c * t) ∂expMeasure r) = r / (r - c) := by
  have hi : Integrable (fun t : ℝ => Real.exp (c * t)) (expMeasure r) := by
    refine ⟨(by fun_prop : Measurable fun t : ℝ => Real.exp (c * t)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => (Real.exp_pos _).le),
      lintegral_exp_mul_expMeasure hr hc]
    exact ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  have he := lintegral_exp_mul_expMeasure hr hc
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)] at he
  have ht := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun _ => (Real.exp_pos _).le),
    ENNReal.toReal_ofReal (div_nonneg hr.le (sub_pos.mpr hc).le)] using ht

end BGW.StableTrees
