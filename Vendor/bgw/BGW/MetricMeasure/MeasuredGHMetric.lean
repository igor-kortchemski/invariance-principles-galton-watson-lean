/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.MeasuredGHSpace
public import BGW.MetricMeasure.GHPSeparation

/-!
# The genuine GHP metric on whole-space measured isometry classes

The already constructed quotient and its topology are unchanged. Zero exact
GHP distance forces a measure-preserving isometry, so the existing
pseudometric is a metric. Completeness and separability remain separate.

Adapted from `Freezing2/Geometry/MeasuredGHMetric.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory

universe u

namespace BGW.MetricMeasure.MeasuredGHSpace

/-- Separation upgrades the exact existing quotient pseudometric. Its distance,
uniformity, topology and Borel structure are preserved definitionally. -/
noncomputable instance : MetricSpace MeasuredGHSpace.{u} where
  toPseudoMetricSpace := instPseudoMetricSpace
  eq_of_dist_eq_zero := by
    intro X Y h
    induction X using Quotient.inductionOn with
    | _ X =>
      induction Y using Quotient.inductionOn with
      | _ Y =>
        apply Quotient.sound
        exact (ghpDistance_eq_zero_iff_measured_isometry (X.law : Measure X)
          (Y.law : Measure Y)).mp h

end BGW.MetricMeasure.MeasuredGHSpace
