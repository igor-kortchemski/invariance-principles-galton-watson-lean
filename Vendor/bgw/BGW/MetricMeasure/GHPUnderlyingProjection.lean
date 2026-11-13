/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.MeasuredGHSpace
public import BGW.MetricMeasure.GHPUnderlyingGH

/-!
# The continuous underlying GH projection

Forgetting the measure is well-defined on the source whole-space measured
isometry classes. The actual GH≤GHP inequality makes this projection
nonexpansive, so it is continuous and Borel measurable. No assumption about
Polishness or the Gromov--Prokhorov quotient is needed.

Adapted from `Freezing2/Geometry/GHPUnderlyingProjection.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory GromovHausdorff

universe u

namespace BGW.MetricMeasure.MeasuredGHSpace

/-- Forget the measure while retaining the entire underlying compact space. -/
noncomputable def underlyingGH : MeasuredGHSpace.{u} → GHSpace :=
  Quotient.lift (fun X : CompactMeasuredSpace.{u} ↦ toGHSpace X) (by
    intro X Y h
    obtain ⟨e, _⟩ := h
    exact toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr ⟨e⟩)

@[simp] theorem underlyingGH_toMeasuredGHSpace (X : CompactMeasuredSpace.{u}) :
    underlyingGH (toMeasuredGHSpace X) = toGHSpace X := rfl

/-- The source's underlying-space projection cannot increase distances. -/
theorem lipschitzWith_underlyingGH : LipschitzWith 1 underlyingGH.{u} := by
  apply LipschitzWith.mk_one
  intro X Y
  induction X using Quotient.inductionOn with
  | _ X =>
    induction Y using Quotient.inductionOn with
    | _ Y => exact ghDist_le_ghpDistance (X.law : Measure X) (Y.law : Measure Y)

theorem continuous_underlyingGH : Continuous underlyingGH.{u} :=
  lipschitzWith_underlyingGH.continuous

/-- With the usual Borel structure on GHSpace, the source projection is
measurable as asserted in the topology appendix. -/
theorem measurable_underlyingGH :
    letI : MeasurableSpace GHSpace := borel GHSpace
    Measurable underlyingGH.{u} := by
  let : MeasurableSpace GHSpace := borel GHSpace
  let : BorelSpace GHSpace := ⟨rfl⟩
  exact continuous_underlyingGH.measurable

end BGW.MetricMeasure.MeasuredGHSpace

