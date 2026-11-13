/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.BrownianBridge
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.Ring

/-!
# Nondegenerate increments of the constructed Brownian bridge

An evaluation difference has variance `d * (1 - d)`, where `d` is the distance
between its two unit-interval times. For `0 < d < 1` its Gaussian law has no
atoms. The exclusions are essential: equal times and the pair of endpoints
both give a deterministic zero difference.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace BGW.ContinuumTrees.BrownianBridge

/-- Differences of evaluations are Gaussian under the actual continuous bridge law. -/
theorem hasGaussianLaw_eval_sub (s t : unitInterval) :
    HasGaussianLaw (fun f : C(unitInterval, ℝ) => f s - f t)
      (law : Measure C(unitInterval, ℝ)) :=
  isGaussianProcess_eval.hasGaussianLaw_fun_sub

theorem integral_eval_sub (s t : unitInterval) :
    ∫ f : C(unitInterval, ℝ), f s - f t ∂(law : Measure C(unitInterval, ℝ)) = 0 := by
  rw [integral_sub (integrable_eval s) (integrable_eval t), integral_eval, integral_eval,
    sub_self]

/-- The variance of an individual bridge evaluation. -/
theorem variance_eval (s : unitInterval) :
    Var[fun f : C(unitInterval, ℝ) => f s; (law : Measure C(unitInterval, ℝ))] =
      (s : ℝ) - (s : ℝ) * (s : ℝ) := by
  rw [← covariance_self (ContinuousMap.measurable_eval s).aemeasurable, covariance_eval,
    min_self]

/-- The increment variance includes the endpoint degeneracy at distance one. -/
theorem variance_eval_sub (s t : unitInterval) :
    Var[fun f : C(unitInterval, ℝ) => f s - f t; (law : Measure C(unitInterval, ℝ))] =
      |(s : ℝ) - (t : ℝ)| * (1 - |(s : ℝ) - (t : ℝ)|) := by
  have hmem (r : unitInterval) := (isGaussianProcess_eval.hasGaussianLaw_eval r).memLp_two
  rw [variance_fun_sub (hmem s) (hmem t), variance_eval, variance_eval, covariance_eval]
  rcases le_total (s : ℝ) (t : ℝ) with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- Every increment at a nonzero distance strictly below one has positive variance. -/
theorem variance_eval_sub_pos (s t : unitInterval)
    (hzero : 0 < |(s : ℝ) - (t : ℝ)|) (hone : |(s : ℝ) - (t : ℝ)| < 1) :
    0 < Var[fun f : C(unitInterval, ℝ) => f s - f t;
      (law : Measure C(unitInterval, ℝ))] := by
  rw [variance_eval_sub]
  exact mul_pos hzero (sub_pos.mpr hone)

/-- Nondegenerate bridge increments have zero mass at each real value. -/
theorem measure_eval_sub_eq_zero (s t : unitInterval)
    (hzero : 0 < |(s : ℝ) - (t : ℝ)|) (hone : |(s : ℝ) - (t : ℝ)| < 1) (a : ℝ) :
    (law : Measure C(unitInterval, ℝ)) {f | f s - f t = a} = 0 := by
  have hv := variance_eval_sub_pos s t hzero hone
  have hmap := (hasGaussianLaw_eval_sub s t).map_eq_gaussianReal
  rw [integral_eval_sub] at hmap
  let : NullSingletonClass (gaussianReal 0
      (Var[fun f : C(unitInterval, ℝ) => f s - f t;
        (law : Measure C(unitInterval, ℝ))]).toNNReal) :=
    nullSingletonClass_gaussianReal (ne_of_gt (Real.toNNReal_pos.mpr hv))
  have h := congrArg (fun μ : Measure ℝ => μ {a}) hmap
  have hm : Measurable (fun f : C(unitInterval, ℝ) => f s - f t) := by fun_prop
  rw [Measure.map_apply hm (measurableSet_singleton a), measure_singleton] at h
  exact h

/-- Two bridge values at nondegenerate time separation are almost surely distinct. -/
theorem ae_eval_ne (s t : unitInterval)
    (hzero : 0 < |(s : ℝ) - (t : ℝ)|) (hone : |(s : ℝ) - (t : ℝ)| < 1) :
    ∀ᵐ f ∂(law : Measure C(unitInterval, ℝ)), f s ≠ f t := by
  rw [ae_iff]
  simpa only [not_not, sub_eq_zero] using measure_eval_sub_eq_zero s t hzero hone 0

end BGW.ContinuumTrees.BrownianBridge
