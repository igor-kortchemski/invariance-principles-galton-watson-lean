/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.Coding
public import Mathlib.Topology.MetricSpace.Basic

/-!
# The compact metric quotient of a continuous coding function

`Point g` is a fresh copy of the time interval carrying the coding pseudometric. Its topology
is the one supplied by that pseudometric; no metric or topology on `unitInterval` is replaced.
`Space g` uses Mathlib's separation quotient and its canonical metric, identifying exactly the
pairs of times at coding distance zero. The projection from the usual compact time interval
is continuous and onto, so the quotient is compact and nonempty.

These results hold for any continuous real coding function. They do not yet assert the
real-tree property, which requires separate proofs of the four-point and midpoint properties.
-/

@[expose] public section

namespace BGW.ContinuumTrees.Coding

/-- A fresh carrier for the coding pseudometric, distinct from the usual metric time interval. -/
structure Point (g : C(unitInterval, ℝ)) where
  /-- The time parameter represented by this point of the coding pseudometric. -/
  time : unitInterval

instance (g : C(unitInterval, ℝ)) : Nonempty (Point g) := ⟨⟨0⟩⟩

noncomputable instance (g : C(unitInterval, ℝ)) : PseudoMetricSpace (Point g) where
  dist s t := codingDist g s.time t.time
  dist_self s := codingDist_self g s.time
  dist_comm s t := codingDist_comm g s.time t.time
  dist_triangle s t u := codingDist_triangle g s.time t.time u.time

/-- The standard metric quotient of the coding pseudometric. Its metric is supplied by Mathlib. -/
abbrev Space (g : C(unitInterval, ℝ)) : Type := SeparationQuotient (Point g)

/-- The canonical projection from times, using the ordinary topology on the source interval. -/
noncomputable def projection (g : C(unitInterval, ℝ)) (t : unitInterval) : Space g :=
  SeparationQuotient.mk (⟨t⟩ : Point g)

theorem projection_surjective (g : C(unitInterval, ℝ)) : Function.Surjective (projection g) := by
  intro x
  obtain ⟨p, rfl⟩ := SeparationQuotient.surjective_mk x
  exact ⟨p.time, rfl⟩

@[simp] theorem dist_projection (g : C(unitInterval, ℝ)) (s t : unitInterval) :
    dist (projection g s) (projection g t) = codingDist g s t := rfl

/-- The quotient relation is exactly zero coding distance. -/
theorem projection_eq_iff (g : C(unitInterval, ℝ)) (s t : unitInterval) :
    projection g s = projection g t ↔ codingDist g s t = 0 := by
  rw [← dist_eq_zero, dist_projection]

/-- Continuity uses the usual time topology, not the topology of the coding pseudometric. -/
theorem continuous_projection (g : C(unitInterval, ℝ)) : Continuous (projection g) := by
  rw [continuous_iff_continuous_dist]
  simpa only [dist_projection] using continuous_codingDist g

instance (g : C(unitInterval, ℝ)) : CompactSpace (Space g) :=
  Function.Surjective.compactSpace (continuous_projection g) (projection_surjective g)

end BGW.ContinuumTrees.Coding
