/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Quantitative comparison of pushed probability measures

Uniformly close random points have close laws in the Lévy–Prokhorov metric.
A nonexpansive map contracts this metric, and weak convergence on a separable
metric space implies convergence in Lévy–Prokhorov distance.

Adapted from `Freezing2/Probability/ProkhorovBounds.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal Topology

namespace BGW.MetricMeasure

/-- A common coupling with a deterministic distance bound gives the same
Lévy–Prokhorov bound for its two marginals. -/
theorem levyProkhorovDist_map_le_of_dist_le
    {Ω Y : Type*} [MeasurableSpace Ω] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F G : Ω → Y}
    (hF : Measurable F) (hG : Measurable G) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ ω, dist (F ω) (G ω) ≤ δ) :
    levyProkhorovDist (μ.map F) (μ.map G) ≤ δ := by
  apply levyProkhorovDist_le_of_forall_le _ _ hδ
  intro ε B hδε hB
  rw [Measure.map_apply hF hB, Measure.map_apply hG isOpen_thickening.measurableSet]
  apply (measure_mono (μ := μ) ?_).trans le_self_add
  intro ω hω
  apply mem_thickening_iff.mpr
  exact ⟨F ω, hω, by simpa only [dist_comm] using (hclose ω).trans_lt hδε⟩

/-- The extended Lévy–Prokhorov distance contracts under a nonexpansive map. -/
theorem levyProkhorovEDist_map_le
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : X → Y} (hf : LipschitzWith 1 f) :
    levyProkhorovEDist (μ.map f) (ν.map f) ≤ levyProkhorovEDist μ ν := by
  apply levyProkhorovEDist_le_of_forall_le
  intro ε B hε hεtop hB
  rw [Measure.map_apply hf.continuous.measurable hB,
    Measure.map_apply hf.continuous.measurable isOpen_thickening.measurableSet]
  have hb := left_measure_le_of_levyProkhorovEDist_lt hε
    (hB.preimage hf.continuous.measurable)
  apply hb.trans
  apply add_le_add _ le_rfl
  apply measure_mono
  intro x hx
  obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.mp hx
  apply mem_thickening_iff.mpr
  refine ⟨f z, hz, ?_⟩
  have hd : dist (f x) (f z) ≤ dist x z := by simpa using hf.dist_le_mul x z
  exact hd.trans_lt hxz

/-- Lévy–Prokhorov distance between probability measures contracts under a
nonexpansive map. -/
theorem levyProkhorovDist_map_le
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : X → Y} (hf : LipschitzWith 1 f) :
    levyProkhorovDist (μ.map f) (ν.map f) ≤ levyProkhorovDist μ ν :=
  ENNReal.toReal_mono (levyProkhorovEDist_ne_top μ ν) (levyProkhorovEDist_map_le μ ν hf)

/-- Weak convergence of probability measures on a separable metric space gives
convergence in Lévy–Prokhorov distance. -/
theorem tendsto_levyProkhorovDist_of_tendsto
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
    {μ : ℕ → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (h : Filter.Tendsto μ Filter.atTop (𝓝 ν)) :
    Filter.Tendsto (fun n ↦ levyProkhorovDist (μ n : Measure X) (ν : Measure X))
      Filter.atTop (𝓝 0) := by
  have hl := (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto ν).comp h
  have hd := hl.dist (tendsto_const_nhds : Filter.Tendsto
    (fun _ : ℕ ↦ LevyProkhorov.ofMeasure ν) Filter.atTop (𝓝 (LevyProkhorov.ofMeasure ν)))
  simpa only [dist_self, Function.comp_def, LevyProkhorov.dist_probabilityMeasure_def] using hd

end BGW.MetricMeasure
