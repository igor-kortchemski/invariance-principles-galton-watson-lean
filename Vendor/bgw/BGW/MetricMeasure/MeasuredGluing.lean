/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.ProkhorovBounds
public import Mathlib.Topology.MetricSpace.Gluing
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# A common metric realization of measured approximations

A map of small distortion produces isometric embeddings into a common metric
space. These embeddings control both Hausdorff distance between the whole
images and Lévy–Prokhorov distance between the pushed probability measures.

Adapted from `Freezing2/Geometry/MeasuredGluing.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped Topology

namespace BGW.MetricMeasure

/-- Small distortion, a dense image and close pushed measures give a common
metric space with simultaneous Hausdorff and Lévy–Prokhorov bounds. -/
theorem exists_measured_gluing
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Nonempty Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → Y) (hf : Measurable f) {δ r p : ℝ} (hδ : 0 < δ)
    (hdis : ∀ x x', |dist x x' - dist (f x) (f x')| ≤ 2 * δ)
    (hdense : ∀ y, ∃ x, dist y (f x) ≤ r)
    (hprob : levyProkhorovDist (μ.map f) ν ≤ p) :
    ∃ m : MetricSpace (X ⊕ Y),
      letI := m
      letI : TopologicalSpace (X ⊕ Y) := m.toUniformSpace.toTopologicalSpace
      letI : MeasurableSpace (X ⊕ Y) := borel (X ⊕ Y)
      Isometry (@Sum.inl X Y) ∧ Isometry (@Sum.inr X Y) ∧
        hausdorffDist (range (@Sum.inl X Y)) (range (@Sum.inr X Y)) ≤ δ + r ∧
        levyProkhorovDist (μ.map (@Sum.inl X Y)) (ν.map (@Sum.inr X Y)) ≤ δ + p := by
  let m : MetricSpace (X ⊕ Y) := glueMetricApprox id f δ hδ hdis
  refine ⟨m, ?_⟩
  let := m
  let : TopologicalSpace (X ⊕ Y) := m.toUniformSpace.toTopologicalSpace
  let : MeasurableSpace (X ⊕ Y) := borel (X ⊕ Y)
  let : BorelSpace (X ⊕ Y) := ⟨rfl⟩
  have hl : Isometry (@Sum.inl X Y) := Isometry.of_dist_eq fun _ _ ↦ rfl
  have hr : Isometry (@Sum.inr X Y) := Isometry.of_dist_eq fun _ _ ↦ rfl
  have hglue (x : X) : dist (Sum.inl x : X ⊕ Y) (Sum.inr (f x)) = δ :=
    glueDist_glued_points id f δ x
  have hr0 : 0 ≤ r := by
    obtain ⟨y⟩ := ‹Nonempty Y›
    obtain ⟨x, hx⟩ := hdense y
    exact dist_nonneg.trans hx
  refine ⟨hl, hr, ?_, ?_⟩
  · apply hausdorffDist_le_of_mem_dist (add_nonneg hδ.le hr0)
    · rintro _ ⟨x, rfl⟩
      exact ⟨Sum.inr (f x), mem_range_self _, by rw [hglue]; linarith⟩
    · rintro _ ⟨y, rfl⟩
      obtain ⟨x, hx⟩ := hdense y
      refine ⟨Sum.inl x, mem_range_self _, ?_⟩
      have ht := dist_triangle (Sum.inr y : X ⊕ Y) (Sum.inr (f x)) (Sum.inl x)
      rw [hr.dist_eq, dist_comm (Sum.inr (f x)), hglue] at ht
      linarith
  · have hnear : levyProkhorovDist (μ.map (@Sum.inl X Y))
        (μ.map (fun x ↦ (Sum.inr (f x) : X ⊕ Y))) ≤ δ :=
      levyProkhorovDist_map_le_of_dist_le μ hl.continuous.measurable
        (hr.continuous.measurable.comp hf) hδ.le (fun x ↦ (hglue x).le)
    have he : μ.map (fun x ↦ (Sum.inr (f x) : X ⊕ Y)) = (μ.map f).map (@Sum.inr X Y) :=
      (Measure.map_map hr.continuous.measurable hf).symm
    rw [he] at hnear
    have hfar := (levyProkhorovDist_map_le (μ.map f) ν hr.lipschitzWith).trans hprob
    have ht := levyProkhorovDist_triangle (μ.map (@Sum.inl X Y))
      ((μ.map f).map (@Sum.inr X Y)) (ν.map (@Sum.inr X Y))
    exact ht.trans (add_le_add hnear hfar)

end BGW.MetricMeasure
