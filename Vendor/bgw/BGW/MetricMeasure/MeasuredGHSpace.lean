/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.CompactMeasuredSpace
public import BGW.MetricMeasure.GHPTriangle

/-!
# The GHP topology on measured isometry classes

The equivalence relation identifies the entire compact metric space by a
measure-preserving isometry, with the whole carrier retained. The ambient-isometry GHP
infimum descends to this quotient and satisfies the pseudometric axioms.
Its topology and Borel structure are therefore available for weak convergence.
Separation, completeness, and separability are separate background results;
none is assumed in this construction or the deterministic-limit argument.

Adapted from `Freezing2/Geometry/MeasuredGHSpace.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory

universe u

namespace BGW.MetricMeasure
namespace CompactMeasuredSpace

/-- Measure-preserving isometry of the whole compact space. Null-measure
points are retained, unlike a quotient identifying only the measure supports. -/
def MeasuredIsometry (X Y : CompactMeasuredSpace.{u}) : Prop :=
  ∃ e : X ≃ᵢ Y, (X.law : Measure X).map e = (Y.law : Measure Y)

theorem measuredIsometry_refl (X : CompactMeasuredSpace.{u}) : MeasuredIsometry X X := by
  refine ⟨IsometryEquiv.refl X, ?_⟩
  exact Measure.map_id

theorem measuredIsometry_symm {X Y : CompactMeasuredSpace.{u}}
    (h : MeasuredIsometry X Y) : MeasuredIsometry Y X := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  rw [← he, Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
  simp only [Function.comp_def, e.symm_apply_apply, Measure.map_id']

theorem measuredIsometry_trans {X Y Z : CompactMeasuredSpace.{u}}
    (hXY : MeasuredIsometry X Y) (hYZ : MeasuredIsometry Y Z) : MeasuredIsometry X Z := by
  obtain ⟨e, he⟩ := hXY
  obtain ⟨f, hf⟩ := hYZ
  refine ⟨e.trans f, ?_⟩
  change (X.law : Measure X).map (f ∘ e) = _
  rw [← Measure.map_map f.continuous.measurable e.continuous.measurable, he, hf]

/-- The whole-space measured-isometry equivalence relation on compact measured spaces. -/
def measuredIsometrySetoid : Setoid CompactMeasuredSpace.{u} where
  r := MeasuredIsometry
  iseqv := ⟨measuredIsometry_refl, measuredIsometry_symm, measuredIsometry_trans⟩

theorem distance_congr {X Y X' Y' : CompactMeasuredSpace.{u}}
    (hX : MeasuredIsometry X X') (hY : MeasuredIsometry Y Y') :
    distance X Y = distance X' Y' := by
  obtain ⟨e, he⟩ := hX
  obtain ⟨f, hf⟩ := hY
  unfold distance
  rw [ghpDistance_eq_of_isometryEquiv (X.law : Measure X) (X'.law : Measure X')
    (Y.law : Measure Y) e he, ← hf, ghpDistance_map_isometryEquiv_right]

end CompactMeasuredSpace

/-- Compact measured spaces modulo measure-preserving isometry of the whole
space, equipped below with the GHP topology. -/
def MeasuredGHSpace : Type (u + 1) := Quotient CompactMeasuredSpace.measuredIsometrySetoid.{u}

/-- Take the class of a compact measured space under whole-space measured isometry. -/
def toMeasuredGHSpace (X : CompactMeasuredSpace.{u}) : MeasuredGHSpace.{u} :=
  Quotient.mk CompactMeasuredSpace.measuredIsometrySetoid X

namespace MeasuredGHSpace

noncomputable instance : PseudoMetricSpace MeasuredGHSpace.{u} where
  dist := Quotient.lift₂ CompactMeasuredSpace.distance
    (fun _ _ _ _ hX hY ↦ CompactMeasuredSpace.distance_congr hX hY)
  dist_self X := by
    induction X using Quotient.inductionOn with
    | _ X => exact ghpDistance_self (X.law : Measure X)
  dist_comm X Y := by
    induction X using Quotient.inductionOn with
    | _ X =>
      induction Y using Quotient.inductionOn with
      | _ Y => exact CompactMeasuredSpace.distance_comm X Y
  dist_triangle X Y Z := by
    induction X using Quotient.inductionOn with
    | _ X =>
      induction Y using Quotient.inductionOn with
      | _ Y =>
        induction Z using Quotient.inductionOn with
        | _ Z =>
          exact ghpDistance_triangle (X.law : Measure X) (Y.law : Measure Y) (Z.law : Measure Z)

noncomputable instance : MeasurableSpace MeasuredGHSpace.{u} := borel _
instance : BorelSpace MeasuredGHSpace.{u} := ⟨rfl⟩

/-- Distances in the quotient are literally the original ambient infima. -/
theorem dist_toMeasuredGHSpace (X Y : CompactMeasuredSpace.{u}) :
    dist (toMeasuredGHSpace X) (toMeasuredGHSpace Y) = CompactMeasuredSpace.distance X Y := rfl

/-- Equality in this quotient means whole-space measured isometry, including
points outside the measure support. -/
theorem toMeasuredGHSpace_eq_iff (X Y : CompactMeasuredSpace.{u}) :
    toMeasuredGHSpace X = toMeasuredGHSpace Y ↔ CompactMeasuredSpace.MeasuredIsometry X Y :=
  Quotient.eq

end MeasuredGHSpace
end BGW.MetricMeasure
