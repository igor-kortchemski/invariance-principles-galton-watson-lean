/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.RootedGHP
public import BGW.MetricMeasure.GHPTriangle

/-!
# Triangle inequality for the rooted GHP infimum

The existing gluing of two ambient realizations identifies the whole middle
carrier. In particular, both images of its root agree. The ordinary distance
triangle inequality controls the root contribution, alongside the existing
Hausdorff and Lévy–Prokhorov estimates.

The proof extends `BGW.MetricMeasure.GHPTriangle`, adapted from
`Freezing2/Geometry/GHPTriangle.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
No quotient metric or separation theorem is asserted in this module.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped Classical

universe u

namespace BGW.MetricMeasure

variable {X Y Z : Type u}
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
  [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z] [CompactSpace Z]

/-- Glue two rooted ambient costs along the whole middle compact space. -/
theorem rootedGHPDistance_le_add_of_costs (μ : Measure X) (ν : Measure Y) (κ : Measure Z)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    (x : X) (y : Y) (z : Z) {a b : ℝ}
    (ha : a ∈ rootedGHPCosts μ ν x y) (hb : b ∈ rootedGHPCosts ν κ y z) :
    rootedGHPDistance μ κ x z ≤ a + b := by
  let : Nonempty X := ⟨x⟩
  let : Nonempty Y := ⟨y⟩
  let : Nonempty Z := ⟨z⟩
  obtain ⟨A, rfl⟩ := ha
  obtain ⟨B, rfl⟩ := hb
  let W := GlueSpace A.right_isometry B.left_isometry
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  let p : A.ambient → W := toGlueL A.right_isometry B.left_isometry
  let q : B.ambient → W := toGlueR A.right_isometry B.left_isometry
  have hp : Isometry p := toGlueL_isometry A.right_isometry B.left_isometry
  have hq : Isometry q := toGlueR_isometry A.right_isometry B.left_isometry
  have hmiddle : p ∘ A.right = q ∘ B.left :=
    toGlue_commute A.right_isometry B.left_isometry
  have hleft : levyProkhorovDist (μ.map (p ∘ A.left)) (ν.map (p ∘ A.right)) ≤
      levyProkhorovDist (μ.map A.left) (ν.map A.right) := by
    rw [← Measure.map_map hp.continuous.measurable A.left_isometry.continuous.measurable,
      ← Measure.map_map hp.continuous.measurable A.right_isometry.continuous.measurable]
    exact levyProkhorovDist_map_le _ _ hp.lipschitzWith
  have hright : levyProkhorovDist (ν.map (p ∘ A.right)) (κ.map (q ∘ B.right)) ≤
      levyProkhorovDist (ν.map B.left) (κ.map B.right) := by
    rw [hmiddle, ← Measure.map_map hq.continuous.measurable B.left_isometry.continuous.measurable,
      ← Measure.map_map hq.continuous.measurable B.right_isometry.continuous.measurable]
    exact levyProkhorovDist_map_le _ _ hq.lipschitzWith
  have hprob : levyProkhorovDist (μ.map (p ∘ A.left)) (κ.map (q ∘ B.right)) ≤
      levyProkhorovDist (μ.map A.left) (ν.map A.right) +
        levyProkhorovDist (ν.map B.left) (κ.map B.right) :=
    (levyProkhorovDist_triangle _ (ν.map (p ∘ A.right)) _).trans (add_le_add hleft hright)
  have hHleft : hausdorffDist (range (p ∘ A.left)) (range (p ∘ A.right)) =
      hausdorffDist (range A.left) (range A.right) := by
    rw [range_comp, range_comp, hausdorffDist_image hp]
  have hHright : hausdorffDist (range (p ∘ A.right)) (range (q ∘ B.right)) =
      hausdorffDist (range B.left) (range B.right) := by
    rw [hmiddle, range_comp, range_comp, hausdorffDist_image hq]
  have hfinite : hausdorffEDist (range (p ∘ A.left)) (range (p ∘ A.right)) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _)
      (isCompact_range (hp.continuous.comp A.left_isometry.continuous)).isBounded
      (isCompact_range (hp.continuous.comp A.right_isometry.continuous)).isBounded
  have hhaus : hausdorffDist (range (p ∘ A.left)) (range (q ∘ B.right)) ≤
      hausdorffDist (range A.left) (range A.right) +
        hausdorffDist (range B.left) (range B.right) := by
    simpa only [hHleft, hHright] using
      (hausdorffDist_triangle (u := range (q ∘ B.right)) hfinite)
  have hrootleft : dist ((p ∘ A.left) x) ((p ∘ A.right) y) =
      dist (A.left x) (A.right y) := hp.dist_eq _ _
  have hrootright : dist ((p ∘ A.right) y) ((q ∘ B.right) z) =
      dist (B.left y) (B.right z) := by
    rw [hmiddle]
    exact hq.dist_eq _ _
  have hroot : dist ((p ∘ A.left) x) ((q ∘ B.right) z) ≤
      dist (A.left x) (A.right y) + dist (B.left y) (B.right z) := by
    simpa only [hrootleft, hrootright] using
      dist_triangle ((p ∘ A.left) x) ((p ∘ A.right) y) ((q ∘ B.right) z)
  have hcost := rootedGHPDistance_le_of_isometries μ κ x z W (p ∘ A.left) (q ∘ B.right)
    (hp.comp A.left_isometry) (hq.comp B.right_isometry)
  change rootedGHPDistance μ κ x z ≤
    (dist (A.left x) (A.right y) +
      (levyProkhorovDist (μ.map A.left) (ν.map A.right) +
        hausdorffDist (range A.left) (range A.right))) +
    (dist (B.left y) (B.right z) +
      (levyProkhorovDist (ν.map B.left) (κ.map B.right) +
        hausdorffDist (range B.left) (range B.right)))
  exact hcost.trans (by linarith)

/-- The rooted summed-cost infimum satisfies the triangle inequality. -/
theorem rootedGHPDistance_triangle (μ : Measure X) (ν : Measure Y) (κ : Measure Z)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    (x : X) (y : Y) (z : Z) :
    rootedGHPDistance μ κ x z ≤
      rootedGHPDistance μ ν x y + rootedGHPDistance ν κ y z := by
  by_contra! h
  let ε : ℝ := (rootedGHPDistance μ κ x z -
    (rootedGHPDistance μ ν x y + rootedGHPDistance ν κ y z)) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨a, ha, ha'⟩ := exists_lt_of_csInf_lt (rootedGHPCosts_nonempty μ ν x y)
    (show sInf (rootedGHPCosts μ ν x y) < rootedGHPDistance μ ν x y + ε by
      change rootedGHPDistance μ ν x y < _; linarith)
  obtain ⟨b, hb, hb'⟩ := exists_lt_of_csInf_lt (rootedGHPCosts_nonempty ν κ y z)
    (show sInf (rootedGHPCosts ν κ y z) < rootedGHPDistance ν κ y z + ε by
      change rootedGHPDistance ν κ y z < _; linarith)
  have hbound := rootedGHPDistance_le_add_of_costs μ ν κ x y z ha hb
  dsimp [ε] at ha' hb'
  linarith

/-- A rooted compact probability space has zero distance from itself. -/
theorem rootedGHPDistance_self (μ : Measure X) (x : X) :
    rootedGHPDistance μ μ x x = 0 := by
  apply le_antisymm _ (rootedGHPDistance_nonneg μ μ x x)
  have h := rootedGHPDistance_le_of_isometries μ μ x x X id id isometry_id isometry_id
  have hb : borel X = ‹MeasurableSpace X› := BorelSpace.measurable_eq.symm
  simpa only [hb, id_eq, dist_self, Measure.map_id, levyProkhorovDist_self,
    hausdorffDist_self_zero, add_zero, zero_add] using h

end BGW.MetricMeasure
