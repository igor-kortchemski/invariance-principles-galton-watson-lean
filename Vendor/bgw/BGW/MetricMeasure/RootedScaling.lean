/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.RootedMeasuredGHSpace
public import BGW.MetricMeasure.RootedScalingBase

/-!
# Positive spatial scaling of rooted compact probability spaces

Only distances are multiplied by the positive factor. Probability measures
and roots are transported by the canonical equivalence to `ScaledMetric`.
The GHP comparison uses `max factor 1`; the probability-error part of the
Lévy–Prokhorov metric is not homogeneous under spatial scaling.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

universe u

namespace BGW.MetricMeasure

namespace ScaledMetric

variable (c : Set.Ioi (0 : ℝ)) {X Y : Type u}

/-- Transport a map to the two scaled carriers. -/
def map (f : X → Y) : ScaledMetric c X → ScaledMetric c Y :=
  fun x => toScaled c (f (ofScaled c x))

@[simp] theorem map_toScaled (f : X → Y) (x : X) :
    map c f (toScaled c x) = toScaled c (f x) := rfl

theorem measurable_map [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} (hf : Measurable f) : Measurable (map c f) :=
  (measurable_toScaled c).comp (hf.comp (measurable_ofScaled c))

theorem isometry_map [MetricSpace X] [MetricSpace Y] {f : X → Y}
    (hf : Isometry f) : Isometry (map c f) := by
  apply Isometry.of_dist_eq
  intro x y
  change (c : ℝ) * dist (f (ofScaled c x)) (f (ofScaled c y)) =
    (c : ℝ) * dist (ofScaled c x) (ofScaled c y)
  rw [hf.dist_eq]

/-- An isometry equivalence transports to the scaled carriers. -/
def isometryEquiv [MetricSpace X] [MetricSpace Y] (e : X ≃ᵢ Y) :
    ScaledMetric c X ≃ᵢ ScaledMetric c Y :=
  ⟨(equiv c X).symm.trans (e.toEquiv.trans (equiv c Y)),
    isometry_map c (X := X) (Y := Y) (f := (e : X → Y)) e.isometry⟩

@[simp] theorem isometryEquiv_toScaled [MetricSpace X] [MetricSpace Y]
    (e : X ≃ᵢ Y) (x : X) :
    isometryEquiv c e (toScaled c x) = toScaled c (e x) := rfl

theorem map_measure_toScaled [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {f : X → Y} (hf : Measurable f) :
    (μ.map (toScaled c)).map (map c f) = (μ.map f).map (toScaled c) := by
  rw [Measure.map_map (measurable_map c hf) (measurable_toScaled c),
    Measure.map_map (measurable_toScaled c) hf]
  rfl

theorem range_map (f : X → Y) :
    range (map c f) = toScaled c '' range f := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨f (ofScaled c x), ⟨ofScaled c x, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨toScaled c x, rfl⟩

end ScaledMetric

namespace CompactMeasuredSpace

/-- Multiply distances by `factor > 0`, transporting the unchanged probability measure. -/
noncomputable def scale (factor : ℝ) (hfactor : 0 < factor) (X : CompactMeasuredSpace.{u}) :
    CompactMeasuredSpace.{u} :=
  of (ScaledMetric ⟨factor, hfactor⟩ X)
    (X.law.map (ScaledMetric.toScaled ⟨factor, hfactor⟩))

end CompactMeasuredSpace

namespace RootedCompactMeasuredSpace

/-- Positive spatial scaling, with the distinguished point transported to the new carrier. -/
noncomputable def scale (factor : ℝ) (hfactor : 0 < factor) (X : RootedCompactMeasuredSpace.{u}) :
    RootedCompactMeasuredSpace.{u} where
  space := X.space.scale factor hfactor
  root := ScaledMetric.toScaled ⟨factor, hfactor⟩ X.root

/-- Whole-carrier measured rooted isometries remain so after positive scaling. -/
theorem measuredIsometry_scale (factor : ℝ) (hfactor : 0 < factor)
    {X Y : RootedCompactMeasuredSpace.{u}} (h : MeasuredIsometry X Y) :
    MeasuredIsometry (scale factor hfactor X) (scale factor hfactor Y) := by
  obtain ⟨e, he, hroot⟩ := h
  let c : Set.Ioi (0 : ℝ) := ⟨factor, hfactor⟩
  refine ⟨ScaledMetric.isometryEquiv c (X := X.space) (Y := Y.space) e, ?_, ?_⟩
  · change ((X.space.law : Measure X.space).map (ScaledMetric.toScaled c)).map
      (ScaledMetric.map c e) = (Y.space.law : Measure Y.space).map (ScaledMetric.toScaled c)
    rw [ScaledMetric.map_measure_toScaled c _ e.continuous.measurable, he]
  · change ScaledMetric.toScaled c (e X.root) = ScaledMetric.toScaled c Y.root
    rw [hroot]

end RootedCompactMeasuredSpace

namespace GHPCoupling

variable {X Y : Type u} [MetricSpace X] [MetricSpace Y]

/-- Scale the two carriers and the actual common ambient realization by the same factor. -/
def scale (c : Set.Ioi (0 : ℝ)) (C : GHPCoupling X Y) :
    GHPCoupling (ScaledMetric c X) (ScaledMetric c Y) where
  ambient := ScaledMetric c C.ambient
  metric := inferInstance
  left := ScaledMetric.map c C.left
  right := ScaledMetric.map c C.right
  left_isometry := ScaledMetric.isometry_map c C.left_isometry
  right_isometry := ScaledMetric.isometry_map c C.right_isometry

/-- Each scaled ambient cost is at most `max c 1` times its original rooted cost. -/
theorem rootedCost_scale_le
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (c : Set.Ioi (0 : ℝ)) (C : GHPCoupling X Y) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (x : X) (y : Y) :
    (C.scale c).rootedCost (μ.map (ScaledMetric.toScaled c)) (ν.map (ScaledMetric.toScaled c))
      (ScaledMetric.toScaled c x) (ScaledMetric.toScaled c y) ≤
        max (c : ℝ) 1 * C.rootedCost μ ν x y := by
  let : Nonempty X := ⟨x⟩
  let : Nonempty Y := ⟨y⟩
  have hP := levyProkhorovDist_map_le_mul (μ.map C.left) (ν.map C.right)
    (ScaledMetric.lipschitzWith_toScaled c (X := C.ambient))
  have hH := hausdorffDist_image_le_mul_of_lipschitz
    (ScaledMetric.lipschitzWith_toScaled c (X := C.ambient))
    (isCompact_range C.left_isometry.continuous) (isCompact_range C.right_isometry.continuous)
    (range_nonempty C.left) (range_nonempty C.right)
  change levyProkhorovDist
    ((μ.map C.left).map (ScaledMetric.toScaled c))
    ((ν.map C.right).map (ScaledMetric.toScaled c)) ≤
      max (c : ℝ) 1 * levyProkhorovDist (μ.map C.left) (ν.map C.right) at hP
  change hausdorffDist (ScaledMetric.toScaled c '' range C.left)
    (ScaledMetric.toScaled c '' range C.right) ≤
      (c : ℝ) * hausdorffDist (range C.left) (range C.right) at hH
  change dist (ScaledMetric.toScaled c (C.left x)) (ScaledMetric.toScaled c (C.right y)) +
    (levyProkhorovDist
      ((μ.map (ScaledMetric.toScaled c)).map (ScaledMetric.map c C.left))
      ((ν.map (ScaledMetric.toScaled c)).map (ScaledMetric.map c C.right)) +
      hausdorffDist (range (ScaledMetric.map c C.left)) (range (ScaledMetric.map c C.right))) ≤
    max (c : ℝ) 1 * (dist (C.left x) (C.right y) +
      (levyProkhorovDist (μ.map C.left) (ν.map C.right) +
        hausdorffDist (range C.left) (range C.right)))
  rw [ScaledMetric.dist_toScaled,
    ScaledMetric.map_measure_toScaled c μ C.left_isometry.continuous.measurable,
    ScaledMetric.map_measure_toScaled c ν C.right_isometry.continuous.measurable,
    ScaledMetric.range_map, ScaledMetric.range_map]
  have hr := mul_le_mul_of_nonneg_right (le_max_left (c : ℝ) 1)
    (show 0 ≤ dist (C.left x) (C.right y) from dist_nonneg)
  have hh := mul_le_mul_of_nonneg_right (le_max_left (c : ℝ) 1)
    (show 0 ≤ hausdorffDist (range C.left) (range C.right) from hausdorffDist_nonneg)
  nlinarith

end GHPCoupling

namespace RootedCompactMeasuredSpace

/-- Positive scaling is Lipschitz for the represented rooted GHP distance. -/
theorem distance_scale_le (factor : ℝ) (hfactor : 0 < factor)
    (X Y : RootedCompactMeasuredSpace.{u}) :
    distance (scale factor hfactor X) (scale factor hfactor Y) ≤
      max factor 1 * distance X Y := by
  let c : Set.Ioi (0 : ℝ) := ⟨factor, hfactor⟩
  have hM : 0 < max factor 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hdiv : distance (scale factor hfactor X) (scale factor hfactor Y) / max factor 1 ≤
      distance X Y := by
    apply le_csInf (rootedGHPCosts_nonempty (X.space.law : Measure X.space)
      (Y.space.law : Measure Y.space) X.root Y.root)
    rintro r ⟨C, rfl⟩
    apply (div_le_iff₀ hM).mpr
    have hbound := C.rootedCost_scale_le c (X.space.law : Measure X.space)
      (Y.space.law : Measure Y.space) X.root Y.root
    have hreal := rootedGHPDistance_le_of_coupling
      ((X.space.law : Measure X.space).map (ScaledMetric.toScaled c))
      ((Y.space.law : Measure Y.space).map (ScaledMetric.toScaled c))
      (ScaledMetric.toScaled c X.root) (ScaledMetric.toScaled c Y.root) (C.scale c)
    exact (hreal.trans hbound).trans_eq (mul_comm _ _)
  simpa only [mul_comm] using (div_le_iff₀ hM).mp hdiv

/-- Scaling by one preserves the represented rooted measured isometry class. -/
theorem measuredIsometry_scale_one (X : RootedCompactMeasuredSpace.{u}) :
    MeasuredIsometry (scale 1 zero_lt_one X) X := by
  let c : Set.Ioi (0 : ℝ) := ⟨1, zero_lt_one⟩
  let e : (scale 1 zero_lt_one X).space ≃ᵢ X.space :=
    { toEquiv := (ScaledMetric.equiv c X.space).symm
      isometry_toFun := by
        apply Isometry.of_dist_eq
        intro x y
        change @dist X.space X.space.metric.toPseudoMetricSpace.toDist
            (ScaledMetric.ofScaled c (X := X.space) x)
            (ScaledMetric.ofScaled c (X := X.space) y) =
          (1 : ℝ) * @dist X.space X.space.metric.toPseudoMetricSpace.toDist
            (ScaledMetric.ofScaled c (X := X.space) x)
            (ScaledMetric.ofScaled c (X := X.space) y)
        rw [one_mul] }
  refine ⟨e, ?_, ?_⟩
  · change ((X.space.law : Measure X.space).map (ScaledMetric.toScaled c)).map
      (ScaledMetric.ofScaled c) = (X.space.law : Measure X.space)
    exact ScaledMetric.map_ofScaled_map_toScaled c _
  · rfl

/-- Scaling by the positive reciprocal cancels the first scaling, including measure and root. -/
theorem measuredIsometry_scale_inv (factor : ℝ) (hfactor : 0 < factor)
    (X : RootedCompactMeasuredSpace.{u}) :
    MeasuredIsometry (scale factor⁻¹ (inv_pos.mpr hfactor) (scale factor hfactor X)) X := by
  let c : Set.Ioi (0 : ℝ) := ⟨factor, hfactor⟩
  let ci : Set.Ioi (0 : ℝ) := ⟨factor⁻¹, inv_pos.mpr hfactor⟩
  let e : (scale factor⁻¹ (inv_pos.mpr hfactor) (scale factor hfactor X)).space ≃ᵢ X.space :=
    { toEquiv := (ScaledMetric.equiv ci (ScaledMetric c X.space)).symm.trans
        (ScaledMetric.equiv c X.space).symm
      isometry_toFun := by
        apply Isometry.of_dist_eq
        intro x y
        change @dist X.space X.space.metric.toPseudoMetricSpace.toDist
            (ScaledMetric.ofScaled c (X := X.space)
              (ScaledMetric.ofScaled ci (X := ScaledMetric c X.space) x))
            (ScaledMetric.ofScaled c (X := X.space)
              (ScaledMetric.ofScaled ci (X := ScaledMetric c X.space) y)) =
          factor⁻¹ * (factor * @dist X.space X.space.metric.toPseudoMetricSpace.toDist
            (ScaledMetric.ofScaled c (X := X.space)
              (ScaledMetric.ofScaled ci (X := ScaledMetric c X.space) x))
            (ScaledMetric.ofScaled c (X := X.space)
              (ScaledMetric.ofScaled ci (X := ScaledMetric c X.space) y)))
        rw [← mul_assoc, inv_mul_cancel₀ hfactor.ne', one_mul] }
  refine ⟨e, ?_, ?_⟩
  · change (((X.space.law : Measure X.space).map (ScaledMetric.toScaled c)).map
      (ScaledMetric.toScaled ci)).map (ScaledMetric.ofScaled c ∘ ScaledMetric.ofScaled ci) =
        (X.space.law : Measure X.space)
    rw [← Measure.map_map (ScaledMetric.measurable_ofScaled c)
      (ScaledMetric.measurable_ofScaled ci), ScaledMetric.map_ofScaled_map_toScaled,
      ScaledMetric.map_ofScaled_map_toScaled]
  · rfl

/-- The inverse scaling gives the lower bound with factor `min factor 1`. -/
theorem min_mul_distance_le_scale (factor : ℝ) (hfactor : 0 < factor)
    (X Y : RootedCompactMeasuredSpace.{u}) :
    min factor 1 * distance X Y ≤ distance (scale factor hfactor X) (scale factor hfactor Y) := by
  have hInv := distance_scale_le factor⁻¹ (inv_pos.mpr hfactor)
    (scale factor hfactor X) (scale factor hfactor Y)
  rw [distance_congr (measuredIsometry_scale_inv factor hfactor X)
    (measuredIsometry_scale_inv factor hfactor Y)] at hInv
  rcases le_total factor 1 with hf | hf
  · rw [min_eq_left hf]
    rw [max_eq_left ((one_le_inv₀ hfactor).mpr hf)] at hInv
    calc factor * distance X Y ≤ factor *
        (factor⁻¹ * distance (scale factor hfactor X) (scale factor hfactor Y)) :=
          mul_le_mul_of_nonneg_left hInv hfactor.le
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hfactor.ne', one_mul]
  · rw [min_eq_right hf, one_mul]
    rw [max_eq_right ((inv_le_one₀ hfactor).mpr hf), one_mul] at hInv
    exact hInv

end RootedCompactMeasuredSpace

namespace RootedMeasuredGHSpace

/-- Positive spatial scaling on whole-carrier rooted measured isometry classes. -/
noncomputable def scale (factor : ℝ) (hfactor : 0 < factor) :
    RootedMeasuredGHSpace.{u} → RootedMeasuredGHSpace.{u} :=
  Quotient.map (RootedCompactMeasuredSpace.scale factor hfactor)
    (fun _ _ h => RootedCompactMeasuredSpace.measuredIsometry_scale factor hfactor h)

@[simp] theorem scale_toRootedMeasuredGHSpace (factor : ℝ) (hfactor : 0 < factor)
    (X : RootedCompactMeasuredSpace.{u}) :
    scale factor hfactor (toRootedMeasuredGHSpace X) =
      toRootedMeasuredGHSpace (RootedCompactMeasuredSpace.scale factor hfactor X) := rfl

@[simp] theorem scale_one (X : RootedMeasuredGHSpace.{u}) : scale 1 zero_lt_one X = X := by
  induction X using Quotient.inductionOn with
  | _ X => exact Quotient.sound (RootedCompactMeasuredSpace.measuredIsometry_scale_one X)

@[simp] theorem scale_inv (factor : ℝ) (hfactor : 0 < factor) (X : RootedMeasuredGHSpace.{u}) :
    scale factor⁻¹ (inv_pos.mpr hfactor) (scale factor hfactor X) = X := by
  induction X using Quotient.inductionOn with
  | _ X => exact Quotient.sound (RootedCompactMeasuredSpace.measuredIsometry_scale_inv factor hfactor X)

theorem dist_scale_le (factor : ℝ) (hfactor : 0 < factor) (X Y : RootedMeasuredGHSpace.{u}) :
    dist (scale factor hfactor X) (scale factor hfactor Y) ≤ max factor 1 * dist X Y := by
  induction X using Quotient.inductionOn with
  | _ X =>
    induction Y using Quotient.inductionOn with
    | _ Y => exact RootedCompactMeasuredSpace.distance_scale_le factor hfactor X Y

theorem min_mul_dist_le_scale (factor : ℝ) (hfactor : 0 < factor)
    (X Y : RootedMeasuredGHSpace.{u}) :
    min factor 1 * dist X Y ≤ dist (scale factor hfactor X) (scale factor hfactor Y) := by
  induction X using Quotient.inductionOn with
  | _ X =>
    induction Y using Quotient.inductionOn with
    | _ Y => exact RootedCompactMeasuredSpace.min_mul_distance_le_scale factor hfactor X Y

theorem lipschitzWith_scale (factor : ℝ) (hfactor : 0 < factor) :
    LipschitzWith ⟨max factor 1, zero_le_one.trans (le_max_right _ _)⟩
      (scale factor hfactor : RootedMeasuredGHSpace.{u} → RootedMeasuredGHSpace.{u}) :=
  lipschitzWith_iff_dist_le_mul.mpr (dist_scale_le factor hfactor)

theorem continuous_scale (factor : ℝ) (hfactor : 0 < factor) :
    Continuous (scale factor hfactor : RootedMeasuredGHSpace.{u} → RootedMeasuredGHSpace.{u}) :=
  (lipschitzWith_scale factor hfactor).continuous

theorem measurable_scale (factor : ℝ) (hfactor : 0 < factor) :
    Measurable (scale factor hfactor : RootedMeasuredGHSpace.{u} → RootedMeasuredGHSpace.{u}) :=
  (continuous_scale factor hfactor).measurable

end RootedMeasuredGHSpace

end BGW.MetricMeasure
