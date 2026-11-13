/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.CodingRealTree
public import BGW.MetricMeasure.RootedCompactMeasuredSpace
public import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Root and mass measure of a continuously coded tree

The root is the image of time zero. The mass measure is the pushforward of Mathlib's
Lebesgue probability measure on the unit interval through the continuous projection.
The coding quotient receives its Borel structure once, and the actual pushforward is bundled
as a probability measure and as the project's compact measured and rooted measured spaces.

These constructions are defined for every continuous real coding function. For a nonnegative
function vanishing at zero, distance from the root is its value. If it also vanishes at one,
the two endpoint times project to the same root. Nonnegativity is retained in this last claim:
equal zero endpoint values alone do not exclude a negative interior minimum.
-/

@[expose] public section

open MeasureTheory

namespace BGW.ContinuumTrees.Coding

noncomputable instance (g : C(unitInterval, ℝ)) : MeasurableSpace (Space g) := borel (Space g)

instance (g : C(unitInterval, ℝ)) : BorelSpace (Space g) := ⟨rfl⟩

/-- The distinguished point represented by time zero. -/
noncomputable def root (g : C(unitInterval, ℝ)) : Space g := projection g 0

theorem measurable_projection (g : C(unitInterval, ℝ)) : Measurable (projection g) :=
  (continuous_projection g).measurable

/-- The pushforward of Lebesgue probability on the unit interval. -/
noncomputable def mass (g : C(unitInterval, ℝ)) : ProbabilityMeasure (Space g) :=
  ⟨Measure.map (projection g) (volume : Measure unitInterval), inferInstance⟩

@[simp] theorem coe_mass (g : C(unitInterval, ℝ)) :
    (mass g : Measure (Space g)) = Measure.map (projection g) (volume : Measure unitInterval) := rfl

/-- The mass measure is the genuine pushforward, with measurable projection. -/
theorem mass_apply (g : C(unitInterval, ℝ)) {A : Set (Space g)} (hA : MeasurableSet A) :
    (mass g : Measure (Space g)) A = volume ((projection g) ⁻¹' A) :=
  Measure.map_apply (measurable_projection g) hA

/-- The coded tree with its natural probability mass measure, on the whole metric carrier. -/
noncomputable def compactMeasuredSpace (g : C(unitInterval, ℝ)) :
    BGW.MetricMeasure.CompactMeasuredSpace :=
  BGW.MetricMeasure.CompactMeasuredSpace.of (Space g) (mass g)

/-- The coded compact measured tree rooted at the image of time zero. -/
noncomputable def rootedCompactMeasuredSpace (g : C(unitInterval, ℝ)) :
    BGW.MetricMeasure.RootedCompactMeasuredSpace where
  space := compactMeasuredSpace g
  root := root g

/-- A nonnegative coding function vanishing at zero gives distance from the root directly. -/
theorem dist_root_projection (g : C(unitInterval, ℝ)) (hg : ∀ t, 0 ≤ g t)
    (h0 : g 0 = 0) (t : unitInterval) : dist (root g) (projection g t) = g t := by
  have hm : intervalMin g 0 t = 0 := by
    apply le_antisymm
    · exact (intervalMin_le_left g 0 t).trans_eq h0
    · exact le_intervalMin g 0 t (fun r _ => hg r)
  rw [root, dist_projection, codingDist, h0, hm]
  simp

/-- The endpoint times coincide in the quotient for a nonnegative function with zero endpoints. -/
theorem projection_zero_eq_one (g : C(unitInterval, ℝ)) (hg : ∀ t, 0 ≤ g t)
    (h0 : g 0 = 0) (h1 : g 1 = 0) : projection g 0 = projection g 1 := by
  change root g = projection g 1
  apply dist_eq_zero.mp
  rw [dist_root_projection g hg h0, h1]

end BGW.ContinuumTrees.Coding
