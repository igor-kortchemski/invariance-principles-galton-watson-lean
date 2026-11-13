/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.RootedCompactMeasuredSpace
public import BGW.MetricMeasure.RootedGHPSeparation
public import BGW.MetricMeasure.MeasuredGHMetric

/-!
# The metric quotient of rooted compact probability spaces

The equivalence relation is a single whole-carrier isometry preserving both
the probability measure and the distinguished point. The actual rooted GHP
infimum descends to a metric because its root-preserving separation theorem
has already been proved. Its topology and Borel structure are induced by this
one metric instance. Completeness and separability are not asserted here.

Forgetting the root maps to the existing unrooted quotient and is 1-Lipschitz.
This construction follows the existing unrooted quotient in
`BGW.MetricMeasure.MeasuredGHSpace`, adapted from
`Freezing2/Geometry/MeasuredGHSpace.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory

universe u

namespace BGW.MetricMeasure

namespace RootedCompactMeasuredSpace

/-- A whole-carrier isometry preserving the measure and the distinguished point. -/
def MeasuredIsometry (X Y : RootedCompactMeasuredSpace.{u}) : Prop :=
  ∃ e : X.space ≃ᵢ Y.space,
    (X.space.law : Measure X.space).map e = (Y.space.law : Measure Y.space) ∧
      e X.root = Y.root

theorem measuredIsometry_refl (X : RootedCompactMeasuredSpace.{u}) :
    MeasuredIsometry X X :=
  ⟨IsometryEquiv.refl X.space, Measure.map_id, rfl⟩

theorem measuredIsometry_symm {X Y : RootedCompactMeasuredSpace.{u}}
    (h : MeasuredIsometry X Y) : MeasuredIsometry Y X := by
  obtain ⟨e, he, hroot⟩ := h
  refine ⟨e.symm, ?_, ?_⟩
  · rw [← he, Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
    simp only [Function.comp_def, e.symm_apply_apply, Measure.map_id']
  · rw [← hroot, e.symm_apply_apply]

theorem measuredIsometry_trans {X Y Z : RootedCompactMeasuredSpace.{u}}
    (hXY : MeasuredIsometry X Y) (hYZ : MeasuredIsometry Y Z) :
    MeasuredIsometry X Z := by
  obtain ⟨e, he, heroot⟩ := hXY
  obtain ⟨f, hf, hfroot⟩ := hYZ
  refine ⟨e.trans f, ?_, ?_⟩
  · change (X.space.law : Measure X.space).map (f ∘ e) = _
    rw [← Measure.map_map f.continuous.measurable e.continuous.measurable, he, hf]
  · change f (e X.root) = Z.root
    rw [heroot, hfroot]

/-- Root- and measure-preserving isometry is the equivalence relation used for the quotient. -/
def measuredIsometrySetoid : Setoid RootedCompactMeasuredSpace.{u} where
  r := MeasuredIsometry
  iseqv := ⟨measuredIsometry_refl, measuredIsometry_symm, measuredIsometry_trans⟩

theorem distance_congr {X Y X' Y' : RootedCompactMeasuredSpace.{u}}
    (hX : MeasuredIsometry X X') (hY : MeasuredIsometry Y Y') :
    distance X Y = distance X' Y' := by
  obtain ⟨e, he, heroot⟩ := hX
  obtain ⟨f, hf, hfroot⟩ := hY
  unfold distance
  rw [← he, ← hf, ← heroot, ← hfroot,
    rootedGHPDistance_map_isometryEquiv, rootedGHPDistance_map_isometryEquiv_right]

end RootedCompactMeasuredSpace

/-- Rooted compact metric probability spaces modulo whole-carrier measured rooted isometry. -/
def RootedMeasuredGHSpace : Type (u + 1) :=
  Quotient RootedCompactMeasuredSpace.measuredIsometrySetoid.{u}

/-- Take the class under whole-carrier isometries preserving the root and measure. -/
def toRootedMeasuredGHSpace (X : RootedCompactMeasuredSpace.{u}) : RootedMeasuredGHSpace.{u} :=
  Quotient.mk RootedCompactMeasuredSpace.measuredIsometrySetoid X

namespace RootedMeasuredGHSpace

/-- The metric is the literal rooted ambient infimum descended to isometry classes. -/
noncomputable instance : MetricSpace RootedMeasuredGHSpace.{u} where
  dist := Quotient.lift₂ RootedCompactMeasuredSpace.distance
    (fun _ _ _ _ hX hY ↦ RootedCompactMeasuredSpace.distance_congr hX hY)
  dist_self X := by
    induction X using Quotient.inductionOn with
    | _ X => exact RootedCompactMeasuredSpace.distance_self X
  dist_comm X Y := by
    induction X using Quotient.inductionOn with
    | _ X =>
      induction Y using Quotient.inductionOn with
      | _ Y => exact RootedCompactMeasuredSpace.distance_comm X Y
  dist_triangle X Y Z := by
    induction X using Quotient.inductionOn with
    | _ X =>
      induction Y using Quotient.inductionOn with
      | _ Y =>
        induction Z using Quotient.inductionOn with
        | _ Z => exact RootedCompactMeasuredSpace.distance_triangle X Y Z
  eq_of_dist_eq_zero := by
    intro X Y h
    induction X using Quotient.inductionOn with
    | _ X =>
      induction Y using Quotient.inductionOn with
      | _ Y =>
        apply Quotient.sound
        exact (rootedGHPDistance_eq_zero_iff_measured_isometry
          (X.space.law : Measure X.space) (Y.space.law : Measure Y.space) X.root Y.root).mp h

noncomputable instance : MeasurableSpace RootedMeasuredGHSpace.{u} := borel _
instance : BorelSpace RootedMeasuredGHSpace.{u} := ⟨rfl⟩

/-- Quotient distances agree definitionally with the represented rooted GHP infimum. -/
theorem dist_toRootedMeasuredGHSpace (X Y : RootedCompactMeasuredSpace.{u}) :
    dist (toRootedMeasuredGHSpace X) (toRootedMeasuredGHSpace Y) =
      RootedCompactMeasuredSpace.distance X Y := rfl

/-- Equality remembers the root and the measure on the entire compact carrier. -/
theorem toRootedMeasuredGHSpace_eq_iff (X Y : RootedCompactMeasuredSpace.{u}) :
    toRootedMeasuredGHSpace X = toRootedMeasuredGHSpace Y ↔
      RootedCompactMeasuredSpace.MeasuredIsometry X Y :=
  Quotient.eq

/-- Forget the root while keeping the whole compact measured space. -/
def forgetRoot : RootedMeasuredGHSpace.{u} → MeasuredGHSpace.{u} :=
  Quotient.lift (fun X : RootedCompactMeasuredSpace.{u} ↦ toMeasuredGHSpace X.space) (by
    intro X Y h
    obtain ⟨e, he, -⟩ := h
    exact Quotient.sound ⟨e, he⟩)

@[simp] theorem forgetRoot_toRootedMeasuredGHSpace (X : RootedCompactMeasuredSpace.{u}) :
    forgetRoot (toRootedMeasuredGHSpace X) = toMeasuredGHSpace X.space := rfl

theorem lipschitzWith_forgetRoot : LipschitzWith 1 forgetRoot.{u} := by
  apply LipschitzWith.mk_one
  intro X Y
  induction X using Quotient.inductionOn with
  | _ X =>
    induction Y using Quotient.inductionOn with
    | _ Y => exact RootedCompactMeasuredSpace.distance_space_le X Y

theorem continuous_forgetRoot : Continuous forgetRoot.{u} :=
  lipschitzWith_forgetRoot.continuous

theorem measurable_forgetRoot : Measurable forgetRoot.{u} :=
  continuous_forgetRoot.measurable

end RootedMeasuredGHSpace
end BGW.MetricMeasure
