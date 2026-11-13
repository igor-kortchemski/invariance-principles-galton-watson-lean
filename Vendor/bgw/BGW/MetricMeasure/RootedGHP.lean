/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.GHPSeparation

/-!
# The rooted Gromov–Hausdorff–Prokhorov infimum

A rooted ambient cost is the distance between the embedded roots plus the
existing Lévy–Prokhorov and whole-carrier Hausdorff cost. In particular, the
root contribution is an actual distance, not the Prokhorov distance between
Dirac measures. Roots need not belong to the support of the measure.

All carriers and ambient realizations lie in the same universe. As for the
unrooted infimum, the raw definitions accept arbitrary measures; the intended
metric setting consists of compact nonempty Borel probability spaces.

This extends the existing `GHPCoupling` and unrooted infimum, adapted from
`Freezing2/Geometry/GHPSeparation.lean` and `GromovHausdorffProkhorov.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Metric Set

universe u

namespace BGW.MetricMeasure

namespace GHPCoupling

variable {X Y : Type u} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y]

/-- Root distance plus the existing summed measured GHP cost. -/
noncomputable def rootedCost (C : GHPCoupling X Y) (μ : Measure X) (ν : Measure Y)
    (x : X) (y : Y) : ℝ :=
  dist (C.left x) (C.right y) + C.cost μ ν

theorem rootedCost_nonneg (C : GHPCoupling X Y) (μ : Measure X) (ν : Measure Y)
    (x : X) (y : Y) : 0 ≤ C.rootedCost μ ν x y :=
  add_nonneg dist_nonneg (add_nonneg ENNReal.toReal_nonneg hausdorffDist_nonneg)

end GHPCoupling

variable {X Y : Type u} [MetricSpace X] [MeasurableSpace X]
  [MetricSpace Y] [MeasurableSpace Y]

/-- Costs of common ambient isometric realizations, including the distance between roots.

The compactness and Borel assumptions are not used by the formula; they fix its domain.
Compactness of both carriers, together with their nonemptiness (automatic for the carriers of
probability measures, as in `RootedCompactMeasuredSpace`), makes the Hausdorff distance between the
embedded carriers finite. Compactness alone does not exclude an empty carrier facing a nonempty
one, in which case Mathlib's real `hausdorffDist` takes its default value `0`. The Borel
assumptions make the isometric embeddings measurable, so that the pushforward measures in the
Lévy–Prokhorov term are meaningful (`Measure.map` of a non-measurable map is `0`); they play no
role in the finiteness of the Hausdorff term. -/
@[nolint unusedArguments]
def rootedGHPCosts [CompactSpace X] [BorelSpace X] [CompactSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) (x : X) (y : Y) : Set ℝ :=
  {r | ∃ C : GHPCoupling X Y, r = C.rootedCost μ ν x y}

/-- The rooted GHP infimum on represented compact measured spaces. Its compactness and Borel
assumptions fix the domain, as explained for `rootedGHPCosts`. -/
noncomputable def rootedGHPDistance
    [CompactSpace X] [BorelSpace X] [CompactSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) (x : X) (y : Y) : ℝ :=
  sInf (rootedGHPCosts μ ν x y)

variable [CompactSpace X] [BorelSpace X] [CompactSpace Y] [BorelSpace Y]

theorem rootedGHPCosts_bddBelow (μ : Measure X) (ν : Measure Y) (x : X) (y : Y) :
    BddBelow (rootedGHPCosts μ ν x y) := by
  refine ⟨0, ?_⟩
  rintro r ⟨C, rfl⟩
  exact C.rootedCost_nonneg μ ν x y

theorem rootedGHPCosts_nonempty (μ : Measure X) (ν : Measure Y) (x : X) (y : Y) :
    (rootedGHPCosts μ ν x y).Nonempty := by
  let : MetricSpace (X ⊕ Y) := metricSpaceSum
  let C : GHPCoupling X Y :=
    ⟨X ⊕ Y, inferInstance, Sum.inl, Sum.inr,
      Isometry.of_dist_eq (fun _ _ ↦ rfl), Isometry.of_dist_eq (fun _ _ ↦ rfl)⟩
  exact ⟨C.rootedCost μ ν x y, C, rfl⟩

theorem rootedGHPDistance_nonneg (μ : Measure X) (ν : Measure Y) (x : X) (y : Y) :
    0 ≤ rootedGHPDistance μ ν x y := by
  apply le_csInf (rootedGHPCosts_nonempty μ ν x y)
  rintro r ⟨C, rfl⟩
  exact C.rootedCost_nonneg μ ν x y

/-- Every actual ambient realization gives an upper bound for the rooted infimum. -/
theorem rootedGHPDistance_le_of_coupling (μ : Measure X) (ν : Measure Y)
    (x : X) (y : Y) (C : GHPCoupling X Y) :
    rootedGHPDistance μ ν x y ≤ C.rootedCost μ ν x y := by
  apply csInf_le (rootedGHPCosts_bddBelow μ ν x y)
  exact ⟨C, rfl⟩

/-- A common ambient pair of isometries bounds the rooted GHP distance. -/
theorem rootedGHPDistance_le_of_isometries (μ : Measure X) (ν : Measure Y)
    (x : X) (y : Y) (Z : Type u) [MetricSpace Z] (i : X → Z) (j : Y → Z)
    (hi : Isometry i) (hj : Isometry j) :
    letI : MeasurableSpace Z := borel Z
    rootedGHPDistance μ ν x y ≤ dist (i x) (j y) +
      (levyProkhorovDist (μ.map i) (ν.map j) + hausdorffDist (range i) (range j)) := by
  exact rootedGHPDistance_le_of_coupling μ ν x y
    ⟨Z, inferInstance, i, j, hi, hj⟩

theorem rootedGHPCosts_comm (μ : Measure X) (ν : Measure Y) (x : X) (y : Y) :
    rootedGHPCosts μ ν x y = rootedGHPCosts ν μ y x := by
  apply Set.Subset.antisymm
  · rintro r ⟨C, rfl⟩
    refine ⟨⟨C.ambient, C.metric, C.right, C.left, C.right_isometry, C.left_isometry⟩, ?_⟩
    simp only [GHPCoupling.rootedCost, GHPCoupling.cost, dist_comm,
      levyProkhorovDist_comm, hausdorffDist_comm]
  · rintro r ⟨C, rfl⟩
    refine ⟨⟨C.ambient, C.metric, C.right, C.left, C.right_isometry, C.left_isometry⟩, ?_⟩
    simp only [GHPCoupling.rootedCost, GHPCoupling.cost, dist_comm,
      levyProkhorovDist_comm, hausdorffDist_comm]

theorem rootedGHPDistance_comm (μ : Measure X) (ν : Measure Y) (x : X) (y : Y) :
    rootedGHPDistance μ ν x y = rootedGHPDistance ν μ y x := by
  simp only [rootedGHPDistance, rootedGHPCosts_comm μ ν x y]

/-- Forgetting the roots can only decrease the represented distance. -/
theorem ghpDistance_le_rootedGHPDistance (μ : Measure X) (ν : Measure Y)
    (x : X) (y : Y) : ghpDistance μ ν ≤ rootedGHPDistance μ ν x y := by
  apply le_csInf (rootedGHPCosts_nonempty μ ν x y)
  rintro r ⟨C, rfl⟩
  have h := ghpDistance_le_of_isometries μ ν C.ambient C.left C.right
    C.left_isometry C.right_isometry
  exact h.trans (le_add_of_nonneg_left dist_nonneg)

end BGW.MetricMeasure
