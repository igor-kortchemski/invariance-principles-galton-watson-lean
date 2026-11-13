/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Weak convergence under perturbations on varying probability spaces

Adapted from `Freezing2/Probability/WeakPerturbation.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).

The finite-tree laws change with the horizon. The bounded-Lipschitz estimate
below therefore keeps the probability measure indexed by the horizon rather
than requiring all random variables to live under one fixed measure.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace BGW.MetricMeasure

/-- An error vanishing in probability preserves weak convergence of laws, also
on varying probability spaces. The strict tail convention matches the sampled
distance-matrix estimates. -/
theorem tendsto_probabilityMap_of_error_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n)) {F G : (n : ℕ) → Ω n → E}
    {ν : ProbabilityMeasure E} (hF : ∀ n, Measurable (F n))
    (hG : ∀ n, Measurable (G n))
    (herr : ∀ ε > 0, Tendsto (fun n ↦
      (μ n : Measure (Ω n)).real {ω | ε < dist (F n ω) (G n ω)}) atTop (𝓝 0))
    (hlim : Tendsto (fun n ↦ (μ n).map (G n)) atTop (𝓝 ν)) :
    Tendsto (fun n ↦ (μ n).map (F n)) atTop (𝓝 ν) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro φ hbounded hlipschitz
  obtain ⟨L, hL⟩ := hlipschitz
  obtain ⟨M, hM⟩ := hbounded
  let Φ : E →ᵇ ℝ :=
    { toFun := φ, continuous_toFun := hL.continuous, map_bounded' := ⟨M, hM⟩ }
  have hIntF (n : ℕ) : Integrable (fun ω ↦ φ (F n ω)) (μ n : Measure (Ω n)) :=
    (Φ.integrable ((μ n : Measure (Ω n)).map (F n))).comp_measurable (hF n)
  have hIntG (n : ℕ) : Integrable (fun ω ↦ φ (G n ω)) (μ n : Measure (Ω n)) :=
    (Φ.integrable ((μ n : Measure (Ω n)).map (G n))).comp_measurable (hG n)
  let B := max M 0
  have hbound (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
      |(∫ t, φ t ∂((μ n).map (F n))) - ∫ t, φ t ∂((μ n).map (G n))| ≤
        (L : ℝ) * δ + B * (μ n : Measure (Ω n)).real
          {ω | δ < dist (F n ω) (G n ω)} := by
    let A := {ω | δ < dist (F n ω) (G n ω)}
    have hA : MeasurableSet A := measurableSet_lt measurable_const ((hF n).dist (hG n))
    have hI : Integrable (fun ω ↦ (L : ℝ) * δ + A.indicator (fun _ ↦ B) ω)
        (μ n : Measure (Ω n)) :=
      integrable_const _ |>.add ((integrable_const B).indicator hA)
    have hpt (ω : Ω n) : ‖φ (F n ω) - φ (G n ω)‖ ≤
        (L : ℝ) * δ + A.indicator (fun _ ↦ B) ω := by
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω]
        have hb : ‖φ (F n ω) - φ (G n ω)‖ ≤ B := by
          simpa only [dist_eq_norm] using (hM (F n ω) (G n ω)).trans (le_max_left M 0)
        exact hb.trans (le_add_of_nonneg_left (mul_nonneg L.coe_nonneg hδ.le))
      · rw [Set.indicator_of_notMem hω, add_zero]
        have hd : dist (F n ω) (G n ω) ≤ δ := le_of_not_gt hω
        simpa only [dist_eq_norm] using
          (hL.dist_le_mul (F n ω) (G n ω)).trans
            (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
      integral_map (hF n).aemeasurable hL.continuous.aestronglyMeasurable,
      integral_map (hG n).aemeasurable hL.continuous.aestronglyMeasurable,
      ← integral_sub (hIntF n) (hIntG n), ← Real.norm_eq_abs]
    calc
      ‖∫ ω, φ (F n ω) - φ (G n ω) ∂(μ n : Measure (Ω n))‖ ≤
          ∫ ω, ‖φ (F n ω) - φ (G n ω)‖ ∂(μ n : Measure (Ω n)) :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ ω, (L : ℝ) * δ + A.indicator (fun _ ↦ B) ω ∂(μ n : Measure (Ω n)) :=
        integral_mono ((hIntF n).sub (hIntG n)).norm hI hpt
      _ = (L : ℝ) * δ + B * (μ n : Measure (Ω n)).real A := by
        rw [integral_add (integrable_const _) ((integrable_const B).indicator hA),
          integral_indicator_const B hA]
        simp [smul_eq_mul, mul_comm]
  have hd : Tendsto (fun n ↦ (∫ t, φ t ∂((μ n).map (F n))) -
      ∫ t, φ t ∂((μ n).map (G n))) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let δ := ε / (2 * ((L : ℝ) + 1))
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hsmall : (L : ℝ) * δ < ε / 2 := by
      dsimp [δ]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 2 * ((L : ℝ) + 1))]
      nlinarith
    have htail := (herr δ hδ).const_mul B
    have htail' : ∀ᶠ n in atTop, B * (μ n : Measure (Ω n)).real
        {ω | δ < dist (F n ω) (G n ω)} < ε / 2 := by
      apply htail.eventually_lt_const
      simpa using (half_pos hε)
    filter_upwards [htail'] with n hn
    rw [Real.dist_eq, sub_zero]
    exact (hbound n hδ).trans_lt (by linarith)
  have hg := tendsto_iff_forall_lipschitz_integral_tendsto.mp hlim φ ⟨M, hM⟩ ⟨L, hL⟩
  convert hd.add hg using 1 <;> simp

end BGW.MetricMeasure
