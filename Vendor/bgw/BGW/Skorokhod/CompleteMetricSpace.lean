/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.CompleteMetricComparison

/-!
# Billingsley's metric on the Skorokhod space

The type synonym carries the metric defined by logarithmic time-change cost.
-/

@[expose] public section

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- The Skorokhod space carrying Billingsley's metric `d°` (a type synonym of `D T E`). -/
def DComplete (T : ℝ) (E : Type*) [TopologicalSpace E] : Type _ := D T E

/-- The metric space structure of `d°` on `DComplete T E`. -/
noncomputable instance instMetricSpaceDComplete [MetricSpace E] : MetricSpace (DComplete T E) :=
  { dist := j1CompleteDist
    dist_self := j1CompleteDist_self
    dist_comm := j1CompleteDist_comm
    dist_triangle := j1CompleteDist_triangle
    eq_of_dist_eq_zero := eq_of_j1CompleteDist_eq_zero }

end BGW.Skorokhod
