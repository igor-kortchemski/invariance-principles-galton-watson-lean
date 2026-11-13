/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.RootedGHPTriangle

/-!
# Transport of the rooted GHP infimum

Precomposing an ambient realization by a surjective isometry preserves its
whole image, pushed measure and distinguished point. Thus the entire set of
rooted costs is invariant under transport of both the measure and the root.

This extends `BGW.MetricMeasure.GHPTransport`, adapted from
`Freezing2/Geometry/GHPTransport.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Metric Set

universe u

namespace BGW.MetricMeasure

variable {X X' Y : Type u}
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MetricSpace X'] [MeasurableSpace X'] [BorelSpace X'] [CompactSpace X']
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

theorem rootedGHPCosts_map_isometryEquiv_subset (μ : Measure X) (ν : Measure Y)
    (e : X ≃ᵢ X') (x : X) (y : Y) :
    rootedGHPCosts (μ.map e) ν (e x) y ⊆ rootedGHPCosts μ ν x y := by
  rintro r ⟨C, hr⟩
  refine ⟨⟨C.ambient, C.metric, C.left ∘ e, C.right,
    C.left_isometry.comp e.isometry, C.right_isometry⟩, ?_⟩
  change r = dist (C.left (e x)) (C.right y) +
    (levyProkhorovDist ((μ.map e).map C.left) (ν.map C.right) +
      hausdorffDist (range C.left) (range C.right)) at hr
  change r = dist (C.left (e x)) (C.right y) +
    (levyProkhorovDist (μ.map (C.left ∘ e)) (ν.map C.right) +
      hausdorffDist (range (C.left ∘ e)) (range C.right))
  rw [Measure.map_map C.left_isometry.continuous.measurable e.continuous.measurable] at hr
  rw [e.surjective.range_comp C.left]
  exact hr

/-- Transport preserves the complete set of rooted ambient costs. -/
theorem rootedGHPCosts_map_isometryEquiv (μ : Measure X) (ν : Measure Y)
    (e : X ≃ᵢ X') (x : X) (y : Y) :
    rootedGHPCosts (μ.map e) ν (e x) y = rootedGHPCosts μ ν x y := by
  apply Set.Subset.antisymm (rootedGHPCosts_map_isometryEquiv_subset μ ν e x y)
  have h := rootedGHPCosts_map_isometryEquiv_subset (μ.map e) ν e.symm (e x) y
  have he : (μ.map e).map e.symm = μ := by
    rw [Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
    simp only [Function.comp_def, e.symm_apply_apply, Measure.map_id']
  simpa only [he, e.symm_apply_apply] using h

theorem rootedGHPDistance_map_isometryEquiv (μ : Measure X) (ν : Measure Y)
    (e : X ≃ᵢ X') (x : X) (y : Y) :
    rootedGHPDistance (μ.map e) ν (e x) y = rootedGHPDistance μ ν x y := by
  simp only [rootedGHPDistance, rootedGHPCosts_map_isometryEquiv μ ν e x y]

theorem rootedGHPDistance_map_isometryEquiv_right (ν : Measure Y) (μ : Measure X)
    (e : X ≃ᵢ X') (y : Y) (x : X) :
    rootedGHPDistance ν (μ.map e) y (e x) = rootedGHPDistance ν μ y x := by
  rw [rootedGHPDistance_comm ν, rootedGHPDistance_map_isometryEquiv,
    rootedGHPDistance_comm μ]

/-- A measured isometry preserving the root gives zero rooted distance. -/
theorem rootedGHPDistance_eq_zero_of_measured_isometry (μ : Measure X) (ν : Measure Y)
    (x : X) (y : Y) (e : X ≃ᵢ Y)
    (hμ : μ.map e = ν) (hroot : e x = y) :
    rootedGHPDistance μ ν x y = 0 := by
  rw [← hμ, ← hroot, rootedGHPDistance_map_isometryEquiv_right, rootedGHPDistance_self]

end BGW.MetricMeasure
