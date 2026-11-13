/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BrownianMotion.Gaussian.BrownianMotion
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.UnitInterval

import Mathlib.Tactic.Ring

/-!
# A continuous Brownian bridge law

The source probability space and Brownian motion are the actual constructions
`ProbabilityTheory.gaussianLimit` and `ProbabilityTheory.brownian` supplied by the pinned
BrownianMotion dependency. No existence assumption on a process is required here.

The path is anchored as `B t - B 0 - t * (B 1 - B 0)`. Its two endpoint values are
zero for every outcome, including exceptional outcomes for which `B 0` need not vanish.
Its measurable pushforward to `C(unitInterval, ℝ)` is a probability law with centered
Gaussian finite-dimensional distributions and covariance `min s t - s * t`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BGW.ContinuumTrees.BrownianBridge

/-- A unit-interval time viewed as a nonnegative real Brownian time. -/
def time (t : unitInterval) : ℝ≥0 := ⟨(t : ℝ), unitInterval.nonneg t⟩

@[simp] theorem coe_time (t : unitInterval) : (time t : ℝ) = (t : ℝ) := rfl

@[simp] theorem time_zero : time 0 = 0 := by
  apply Subtype.ext
  rfl

@[simp] theorem time_one : time 1 = 1 := by
  apply Subtype.ext
  rfl

@[fun_prop] theorem continuous_time : Continuous time :=
  continuous_subtype_val.subtype_mk _

/-- The anchored continuous path obtained from the constructed Brownian motion. -/
noncomputable def path (ω : ℝ≥0 → ℝ) : C(unitInterval, ℝ) where
  toFun t := brownian (time t) ω - brownian 0 ω -
    (t : ℝ) * (brownian 1 ω - brownian 0 ω)
  continuous_toFun := by
    exact (((continuous_brownian ω).comp continuous_time).sub continuous_const).sub
      (continuous_subtype_val.mul continuous_const)

@[simp] theorem path_apply (ω : ℝ≥0 → ℝ) (t : unitInterval) :
    path ω t = brownian (time t) ω - brownian 0 ω -
      (t : ℝ) * (brownian 1 ω - brownian 0 ω) := rfl

theorem path_zero (ω : ℝ≥0 → ℝ) : path ω 0 = 0 := by
  rw [path_apply, time_zero]
  simp only [Set.Icc.coe_zero, zero_mul, sub_self]

theorem path_one (ω : ℝ≥0 → ℝ) : path ω 1 = 0 := by
  rw [path_apply, time_one]
  simp only [Set.Icc.coe_one, one_mul, sub_self]

/-- Measurability is for the Borel structure of the continuous-path space. -/
@[fun_prop] theorem measurable_path : Measurable path := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  change Measurable (fun ω => brownian (time t) ω - brownian 0 ω -
    (t : ℝ) * (brownian 1 ω - brownian 0 ω))
  fun_prop

/-- The genuine pushforward of the constructed Brownian probability measure. -/
noncomputable def law : ProbabilityMeasure C(unitInterval, ℝ) :=
  ⟨Measure.map path gaussianLimit, inferInstance⟩

@[simp] theorem coe_law :
    (law : Measure C(unitInterval, ℝ)) = Measure.map path gaussianLimit := rfl

theorem law_apply {A : Set C(unitInterval, ℝ)} (hA : MeasurableSet A) :
    (law : Measure C(unitInterval, ℝ)) A = gaussianLimit (path ⁻¹' A) :=
  Measure.map_apply measurable_path hA

theorem hasLaw_path : HasLaw path (law : Measure C(unitInterval, ℝ)) gaussianLimit where
  aemeasurable := measurable_path.aemeasurable
  map_eq := rfl

/-- The continuous bridge law is concentrated on paths with both endpoints zero. -/
theorem ae_endpoints :
    ∀ᵐ f ∂(law : Measure C(unitInterval, ℝ)), f 0 = 0 ∧ f 1 = 0 := by
  have hclosed : IsClosed {f : C(unitInterval, ℝ) | f 0 = 0 ∧ f 1 = 0} :=
    (isClosed_eq (continuous_eval_const 0) continuous_const).inter
      (isClosed_eq (continuous_eval_const 1) continuous_const)
  rw [coe_law, ae_map_iff measurable_path.aemeasurable hclosed.measurableSet]
  exact ae_of_all _ fun ω => ⟨path_zero ω, path_one ω⟩

/-- Each path evaluation is a finite linear combination of Brownian evaluations. -/
theorem isGaussianProcess_path :
    IsGaussianProcess (fun t ω => path ω t) gaussianLimit := by
  apply isGaussianProcess_brownian.of_isGaussianProcess
  intro t
  refine ⟨{time t, 0, 1},
    { toFun := fun x => x ⟨time t, by simp⟩ - x ⟨0, by simp⟩ -
        (t : ℝ) * (x ⟨1, by simp⟩ - x ⟨0, by simp⟩)
      map_add' := ?_
      map_smul' := ?_ }, ?_⟩
  · intro x y
    simp only [Pi.add_apply]
    ring
  · intro c x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  · intro ω
    rfl

/-- All finite-dimensional distributions under the constructed path law are Gaussian. -/
theorem isGaussianProcess_eval :
    IsGaussianProcess (fun t (f : C(unitInterval, ℝ)) => f t)
      (law : Measure C(unitInterval, ℝ)) where
  hasGaussianLaw J := by
    refine ⟨?_, ?_⟩
    · exact (Measurable.of_eval fun t : J =>
        ContinuousMap.measurable_eval (t : unitInterval)).aemeasurable
    · have hJ : Measurable (fun f : C(unitInterval, ℝ) => J.restrict (fun t => f t)) :=
        Measurable.of_eval fun t : J => ContinuousMap.measurable_eval (t : unitInterval)
      rw [coe_law, Measure.map_map hJ measurable_path]
      exact (isGaussianProcess_path.hasGaussianLaw J).isGaussian_map

/-- Evaluation integrability follows from the proved Gaussian finite-dimensional laws. -/
theorem integrable_eval (t : unitInterval) :
    Integrable (fun f : C(unitInterval, ℝ) => f t) (law : Measure C(unitInterval, ℝ)) :=
  (isGaussianProcess_eval.hasGaussianLaw_eval t).integrable

theorem integral_path (t : unitInterval) : ∫ ω, path ω t ∂gaussianLimit = 0 := by
  have hB := isBrownianReal_brownian.toIsPreBrownianReal
  have hsub (u : ℝ≥0) :
      Integrable (fun ω => brownian u ω - brownian 0 ω) gaussianLimit := by
    change Integrable (brownian u - brownian 0) gaussianLimit
    exact (hB.integrable_eval u).sub (hB.integrable_eval 0)
  change (∫ ω, (brownian (time t) ω - brownian 0 ω) -
    (t : ℝ) * (brownian 1 ω - brownian 0 ω) ∂gaussianLimit) = 0
  rw [integral_sub (hsub _) ((hsub 1).const_mul (t : ℝ)),
    integral_const_mul, integral_sub (hB.integrable_eval _) (hB.integrable_eval 0),
    integral_sub (hB.integrable_eval 1) (hB.integrable_eval 0)]
  simp only [hB.integral_eval, sub_zero, mul_zero]

/-- Every evaluation has mean zero under the actual bridge law. -/
theorem integral_eval (t : unitInterval) :
    ∫ f : C(unitInterval, ℝ), f t ∂(law : Measure C(unitInterval, ℝ)) = 0 := by
  calc
    _ = ∫ ω, path ω t ∂gaussianLimit :=
      (hasLaw_path.integral_comp (ContinuousMap.measurable_eval t).aestronglyMeasurable).symm
    _ = 0 := integral_path t

private theorem covariance_brownian_sub_zero (s t : ℝ≥0) :
    cov[fun ω => brownian s ω - brownian 0 ω,
      fun ω => brownian t ω - brownian 0 ω; gaussianLimit] = min (s : ℝ) (t : ℝ) := by
  have hmem (u : ℝ≥0) := (isGaussianProcess_brownian.hasGaussianLaw_eval u).memLp_two
  rw [covariance_fun_sub_fun_sub (hmem s) (hmem 0) (hmem t) (hmem 0)]
  simp [covariance_brownian]

theorem covariance_path (s t : unitInterval) :
    cov[fun ω => path ω s, fun ω => path ω t; gaussianLimit] =
      min (s : ℝ) (t : ℝ) - (s : ℝ) * (t : ℝ) := by
  have hmem (u : ℝ≥0) := (isGaussianProcess_brownian.hasGaussianLaw_eval u).memLp_two
  have hsub (u : ℝ≥0) : MemLp (fun ω => brownian u ω - brownian 0 ω) 2 gaussianLimit := by
    change MemLp (brownian u - brownian 0) 2 gaussianLimit
    exact (hmem u).sub (hmem 0)
  change cov[fun ω => (brownian (time s) ω - brownian 0 ω) -
    (s : ℝ) * (brownian 1 ω - brownian 0 ω),
    fun ω => (brownian (time t) ω - brownian 0 ω) -
    (t : ℝ) * (brownian 1 ω - brownian 0 ω); gaussianLimit] = _
  rw [covariance_fun_sub_fun_sub (hsub _) ((hsub 1).const_mul (s : ℝ))
    (hsub _) ((hsub 1).const_mul (t : ℝ))]
  simp only [covariance_const_mul_left, covariance_const_mul_right,
    covariance_brownian_sub_zero, NNReal.coe_one, coe_time]
  rw [min_eq_left (unitInterval.le_one s), min_eq_right (unitInterval.le_one t), min_self]
  ring

/-- The standard unit-bridge covariance, transported through the genuine measurable path map. -/
theorem covariance_eval (s t : unitInterval) :
    cov[fun f : C(unitInterval, ℝ) => f s, fun f : C(unitInterval, ℝ) => f t;
      (law : Measure C(unitInterval, ℝ))] =
      min (s : ℝ) (t : ℝ) - (s : ℝ) * (t : ℝ) := by
  calc
    _ = cov[fun ω => path ω s, fun ω => path ω t; gaussianLimit] :=
      (hasLaw_path.covariance_fun_comp (ContinuousMap.measurable_eval s).aemeasurable
        (ContinuousMap.measurable_eval t).aemeasurable).symm
    _ = _ := covariance_path s t

end BGW.ContinuumTrees.BrownianBridge
