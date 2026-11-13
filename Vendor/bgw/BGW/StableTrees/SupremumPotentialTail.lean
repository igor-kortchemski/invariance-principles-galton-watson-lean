/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialDensity
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuity of the exponential supremum tail

Atomlessness gives continuity by dominated convergence. The tail tends to zero
at infinity and is constant on the negative half-line, hence is uniformly continuous.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The negative extension of the tail agrees with the actual exponential-clock probability. -/
theorem supExpTail_eq_measureReal {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) (x : ℝ) :
    supExpTail θ q x = ((expClockLaw θ q).map
      (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal)).real (Ici x) := by
  let := isProbabilityMeasure_expClockLaw θ hq
  rw [Measure.real, Measure.map_apply measurable_supRunning_expTime measurableSet_Ici]
  unfold supExpTail
  split_ifs with hx
  · have he : expClockLaw θ q {p | x ≤ supRunning p.1 p.2.toNNReal} = 1 := by
      have hae := (ae_nonneg_supRunning_supReflected_expTime hθ hq).mono (fun _ hp =>
        le_trans hx.le hp.1)
      have hset : {p : DLoc × ℝ | x ≤ supRunning p.1 p.2.toNNReal} =ᵐ[expClockLaw θ q] univ := by
        filter_upwards [hae] with p hp
        change (x ≤ supRunning p.1 p.2.toNNReal) = True
        exact eq_true hp
      rw [measure_congr hset, measure_univ]
    rw [show (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal) ⁻¹' Ici x =
      {p | x ≤ supRunning p.1 p.2.toNNReal} from rfl, he, ENNReal.toReal_one]
  · rfl

private theorem supExpTail_eq_integral_indicator {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q : ℝ} (hq : 0 < q) (x : ℝ) :
    supExpTail θ q x = ∫ y, (Ici x).indicator (fun _ => (1 : ℝ)) y
      ∂(expClockLaw θ q).map (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal) := by
  rw [integral_indicator measurableSet_Ici, setIntegral_const, smul_eq_mul, mul_one,
    supExpTail_eq_measureReal hθ hq]

private theorem tail_indicator_norm_le (x y : ℝ) :
    ‖(Ici x).indicator (fun _ => (1 : ℝ)) y‖ ≤ 1 := by
  by_cases h : x ≤ y <;> simp [mem_Ici, h]

/-- Continuity on all of `ℝ`, including the negative extension at zero. -/
theorem continuous_supExpTail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    Continuous (supExpTail θ q) := by
  let := isProbabilityMeasure_expClockLaw θ hq
  let μ := (expClockLaw θ q).map (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal)
  have he : supExpTail θ q = fun x => ∫ y, (Ici x).indicator (fun _ => (1 : ℝ)) y ∂μ :=
    funext (supExpTail_eq_integral_indicator hθ hq)
  rw [he, continuous_iff_continuousAt]
  intro x
  have hz : μ {x} = 0 := by
    rw [Measure.map_apply measurable_supRunning_expTime (measurableSet_singleton x)]
    exact expClockLaw_supRunning_eq hθ hq x
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · exact Eventually.of_forall (fun z =>
      (measurable_const.indicator measurableSet_Ici).aestronglyMeasurable)
  · exact Eventually.of_forall (fun z => ae_of_all _ (fun y => tail_indicator_norm_le z y))
  · exact integrable_const _
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with y hy
    have hne : y ≠ x := hy
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hh : Tendsto (fun z => (Ici z).indicator (fun _ => (1 : ℝ)) y) (𝓝 x) (𝓝 0) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_gt_nhds hlt] with z hz
        simp [mem_Ici, not_le.mpr hz]
      simpa only [indicator_of_notMem (show y ∉ Ici x from not_le.mpr hlt)] using hh
    · have hh : Tendsto (fun z => (Ici z).indicator (fun _ => (1 : ℝ)) y) (𝓝 x) (𝓝 1) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_lt_nhds hgt] with z hz
        simp [mem_Ici, hz.le]
      simpa only [indicator_of_mem (show y ∈ Ici x from hgt.le)] using hh

private theorem tendsto_supExpTail_atTop {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    Tendsto (supExpTail θ q) atTop (𝓝 0) := by
  let := isProbabilityMeasure_expClockLaw θ hq
  let μ := (expClockLaw θ q).map (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal)
  have he : supExpTail θ q = fun x => ∫ y, (Ici x).indicator (fun _ => (1 : ℝ)) y ∂μ :=
    funext (supExpTail_eq_integral_indicator hθ hq)
  rw [he]
  have ht : Tendsto (fun x => ∫ y, (Ici x).indicator (fun _ => (1 : ℝ)) y ∂μ) atTop
      (𝓝 (∫ _y, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · exact Eventually.of_forall (fun z =>
      (measurable_const.indicator measurableSet_Ici).aestronglyMeasurable)
    · exact Eventually.of_forall (fun z => ae_of_all _ (fun y => tail_indicator_norm_le z y))
    · exact integrable_const _
    · filter_upwards with y
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop y] with z hz
      simp [mem_Ici, not_le.mpr hz]
  simpa using ht

/-- Uniform continuity of the exponential supremum tail over the whole real line. -/
theorem uniformContinuous_supExpTail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    UniformContinuous (supExpTail θ q) := by
  have hc : Continuous (fun x : ℝ => supExpTail θ q ‖x‖) :=
    (continuous_supExpTail hθ hq).comp continuous_norm
  have ht : Tendsto (fun x : ℝ => supExpTail θ q ‖x‖) (cocompact ℝ) (𝓝 0) :=
    (tendsto_supExpTail_atTop hθ hq).comp tendsto_norm_cocompact_atTop
  have hu := hc.uniformContinuous_of_tendsto_cocompact ht
  have hm : UniformContinuous (fun x : ℝ => max x 0) :=
    (LipschitzWith.id.max_const 0).uniformContinuous
  have he : (fun x : ℝ => supExpTail θ q ‖max x 0‖) = supExpTail θ q := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right x 0)]
    by_cases hx : 0 ≤ x
    · rw [max_eq_left hx]
    · rw [max_eq_right (not_le.mp hx).le, supExpTail_zero hθ hq]
      simp [supExpTail, not_le.mp hx]
  rw [← he]
  exact hu.comp hm

end BGW.StableTrees
