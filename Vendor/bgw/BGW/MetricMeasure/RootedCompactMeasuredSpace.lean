/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.RootedGHPTriangle
public import BGW.MetricMeasure.CompactMeasuredSpace

/-!
# Represented rooted compact metric probability spaces

The bundle adds just a point to the existing compact measured space. The root
may lie outside the measure support. The represented distance is the actual
ambient rooted GHP infimum. No quotient or metric-space instance on represented
spaces is introduced here.
-/

@[expose] public section

open MeasureTheory

universe u

namespace BGW.MetricMeasure

/-- A compact metric probability space together with one distinguished point. -/
structure RootedCompactMeasuredSpace where
  /-- The underlying compact metric probability space. -/
  space : CompactMeasuredSpace.{u}
  /-- The distinguished point of the whole carrier, with no support requirement. -/
  root : space

namespace RootedCompactMeasuredSpace

/-- Root distance plus Hausdorff and Lévy–Prokhorov costs, minimized over common realizations. -/
noncomputable def distance (X Y : RootedCompactMeasuredSpace.{u}) : ℝ :=
  rootedGHPDistance (X.space.law : Measure X.space) (Y.space.law : Measure Y.space)
    X.root Y.root

theorem distance_nonneg (X Y : RootedCompactMeasuredSpace.{u}) : 0 ≤ distance X Y :=
  rootedGHPDistance_nonneg _ _ _ _

theorem distance_comm (X Y : RootedCompactMeasuredSpace.{u}) :
    distance X Y = distance Y X :=
  rootedGHPDistance_comm _ _ _ _

theorem distance_self (X : RootedCompactMeasuredSpace.{u}) : distance X X = 0 :=
  rootedGHPDistance_self _ _

theorem distance_triangle (X Y Z : RootedCompactMeasuredSpace.{u}) :
    distance X Z ≤ distance X Y + distance Y Z :=
  rootedGHPDistance_triangle _ _ _ _ _ _

/-- Forgetting the distinguished point does not increase distance. -/
theorem distance_space_le (X Y : RootedCompactMeasuredSpace.{u}) :
    CompactMeasuredSpace.distance X.space Y.space ≤ distance X Y :=
  ghpDistance_le_rootedGHPDistance _ _ _ _

end RootedCompactMeasuredSpace
end BGW.MetricMeasure
