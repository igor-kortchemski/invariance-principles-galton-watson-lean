/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.RootedMeasuredGHSpace
public import BGW.MetricMeasure.GHPUnderlyingProjection
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Underlying Gromov--Hausdorff classes of rooted measured spaces

Forgetting the root and the measure is continuous, and therefore transports weakly convergent
probability laws. The declarations remain in their historical `Coding` namespace for API
compatibility, although they do not depend on continuum-tree coding.
-/

@[expose] public section

open Filter MeasureTheory GromovHausdorff
open scoped Topology
open BGW.MetricMeasure

universe u

namespace BGW.ContinuumTrees.Coding

/-- Local Borel structure on `GHSpace`, as in `measurable_underlyingGH`. -/
noncomputable local instance ghMeasurableSpace : MeasurableSpace GHSpace := borel GHSpace

local instance : BorelSpace GHSpace := ⟨rfl⟩

/-- Forget root and measure: the GH class of a rooted measured class. -/
noncomputable def forgetToGH : RootedMeasuredGHSpace.{u} → GHSpace :=
  MeasuredGHSpace.underlyingGH ∘ RootedMeasuredGHSpace.forgetRoot

/-- Forgetting root and measure is continuous for the GHP and GH topologies. -/
theorem continuous_forgetToGH : Continuous forgetToGH.{u} :=
  MeasuredGHSpace.continuous_underlyingGH.comp RootedMeasuredGHSpace.continuous_forgetRoot

/-- Weak convergence of laws of rooted measured classes gives weak convergence of the laws of
the underlying GH classes.  The laws on `GHSpace` use its Borel σ-algebra (`borel GHSpace`), which
callers must provide locally (`letI := borel GHSpace`), as in `measurable_underlyingGH`. -/
theorem tendsto_map_forgetToGH {ι : Type*} {L : Filter ι}
    (P : ι → ProbabilityMeasure RootedMeasuredGHSpace.{u})
    {Q : ProbabilityMeasure RootedMeasuredGHSpace.{u}} (h : Tendsto P L (𝓝 Q)) :
    Tendsto (fun i => (P i).map forgetToGH.{u})
      L (𝓝 (Q.map forgetToGH.{u})) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ h continuous_forgetToGH

end BGW.ContinuumTrees.Coding
