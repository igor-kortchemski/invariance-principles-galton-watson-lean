/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.RootedGHP
import Mathlib.Tactic.Linarith

/-!
# GHP bounds from a common probability source

Two measurable surjections from one probability space give a correspondence
between the entire target carriers and a coupling of their image measures.
If their distortion is at most twice a positive radius, approximate metric
gluing bounds both Hausdorff and Lévy–Prokhorov distance by that radius.
Paired source points can also serve as roots, with the same bound on their
distance in the gluing.

The source needs only a measurable-space structure. Neither target measure
is required to have full support. This extracts the common-source argument
used in `BGW.ContinuumTrees.CodingStability` for reuse with spatial scaling.
-/

@[expose] public section

open MeasureTheory Metric Set

universe u v

namespace BGW.MetricMeasure

variable {S : Type v} {X Y : Type u} [MeasurableSpace S]
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

private theorem distances_map_le_of_distortion
    (μ : Measure S) [IsProbabilityMeasure μ] (p : S → X) (q : S → Y)
    (hp : Measurable p) (hq : Measurable q)
    (hps : Function.Surjective p) (hqs : Function.Surjective q)
    {ε : ℝ} (hε : 0 < ε)
    (hdis : ∀ s t, |dist (p s) (p t) - dist (q s) (q t)| ≤ 2 * ε) :
    ghpDistance (μ.map p) (μ.map q) ≤ 2 * ε ∧
      ∀ s₀, rootedGHPDistance (μ.map p) (μ.map q) (p s₀) (q s₀) ≤ 3 * ε := by
  let : Nonempty S := nonempty_of_isProbabilityMeasure μ
  let m : MetricSpace (X ⊕ Y) := glueMetricApprox p q ε hε hdis
  let := m
  let : TopologicalSpace (X ⊕ Y) := m.toUniformSpace.toTopologicalSpace
  let : MeasurableSpace (X ⊕ Y) := borel _
  let : BorelSpace (X ⊕ Y) := ⟨rfl⟩
  have hl : Isometry (@Sum.inl X Y) := Isometry.of_dist_eq fun _ _ => rfl
  have hr : Isometry (@Sum.inr X Y) := Isometry.of_dist_eq fun _ _ => rfl
  have hglue (s : S) : dist (Sum.inl (p s) : X ⊕ Y) (Sum.inr (q s)) = ε :=
    glueDist_glued_points p q ε s
  have hH : hausdorffDist (range (@Sum.inl X Y)) (range (@Sum.inr X Y)) ≤ ε := by
    apply hausdorffDist_le_of_mem_dist hε.le
    · rintro _ ⟨x, rfl⟩
      obtain ⟨s, rfl⟩ := hps x
      exact ⟨Sum.inr (q s), mem_range_self _, (hglue s).le⟩
    · rintro _ ⟨y, rfl⟩
      obtain ⟨s, rfl⟩ := hqs y
      refine ⟨Sum.inl (p s), mem_range_self _, ?_⟩
      simpa only [dist_comm] using (hglue s).le
  have hP : levyProkhorovDist
      ((μ.map p).map (@Sum.inl X Y)) ((μ.map q).map (@Sum.inr X Y)) ≤ ε := by
    rw [Measure.map_map hl.continuous.measurable hp,
      Measure.map_map hr.continuous.measurable hq]
    exact levyProkhorovDist_map_le_of_dist_le μ
      (hl.continuous.measurable.comp hp) (hr.continuous.measurable.comp hq)
      hε.le (fun s => (hglue s).le)
  constructor
  · have hu := ghpDistance_le_of_isometries (μ.map p) (μ.map q)
      (X ⊕ Y) Sum.inl Sum.inr hl hr
    linarith
  · intro s₀
    have hr := rootedGHPDistance_le_of_isometries (μ.map p) (μ.map q) (p s₀) (q s₀)
      (X ⊕ Y) Sum.inl Sum.inr hl hr
    have hroot := hglue s₀
    linarith

/-- Surjective common-source maps with distortion at most `2 * ε` give GHP at most `2 * ε`. -/
theorem ghpDistance_map_le_of_distortion
    (μ : Measure S) [IsProbabilityMeasure μ] (p : S → X) (q : S → Y)
    (hp : Measurable p) (hq : Measurable q)
    (hps : Function.Surjective p) (hqs : Function.Surjective q)
    {ε : ℝ} (hε : 0 < ε)
    (hdis : ∀ s t, |dist (p s) (p t) - dist (q s) (q t)| ≤ 2 * ε) :
    ghpDistance (μ.map p) (μ.map q) ≤ 2 * ε :=
  (distances_map_le_of_distortion μ p q hp hq hps hqs hε hdis).1

/-- Pairing the roots at one source point adds at most one more gluing radius. -/
theorem rootedGHPDistance_map_le_of_distortion
    (μ : Measure S) [IsProbabilityMeasure μ] (p : S → X) (q : S → Y)
    (hp : Measurable p) (hq : Measurable q)
    (hps : Function.Surjective p) (hqs : Function.Surjective q)
    {ε : ℝ} (hε : 0 < ε)
    (hdis : ∀ s t, |dist (p s) (p t) - dist (q s) (q t)| ≤ 2 * ε) (s₀ : S) :
    rootedGHPDistance (μ.map p) (μ.map q) (p s₀) (q s₀) ≤ 3 * ε :=
  (distances_map_le_of_distortion μ p q hp hq hps hqs hε hdis).2 s₀

end BGW.MetricMeasure
