/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.CodingStability
public import BGW.MetricMeasure.RootedScaling
import Mathlib.Tactic.Ring

/-!
# Spatial scaling of continuously coded trees

Multiplying a coding function by a nonnegative constant multiplies its
pseudodistance by that constant. For a positive constant, this identifies the
coded tree with the spatially scaled original tree by a genuine isometry
preserving the root and the Lebesgue pushforward mass.

This is an identity between scaled spaces. It does not assert homogeneity of
GHP distance between two spaces, whose Prokhorov term also measures mass error.
-/

@[expose] public section

open MeasureTheory BGW.MetricMeasure

namespace BGW.ContinuumTrees.Coding

/-- Nonnegative multiplication commutes with the attained interval minimum. -/
theorem intervalMin_smul (g : C(unitInterval, ℝ)) (factor : ℝ) (hf : 0 ≤ factor)
    (s t : unitInterval) :
    intervalMin (factor • g) s t = factor * intervalMin g s t := by
  obtain ⟨v, hv, hmin⟩ := exists_intervalMin g s t
  apply le_antisymm
  · calc
      intervalMin (factor • g) s t ≤ (factor • g) v := intervalMin_le _ _ _ hv
      _ = factor * intervalMin g s t := by
        rw [ContinuousMap.smul_apply, smul_eq_mul, hmin]
  · apply le_intervalMin
    intro v hv
    change factor * intervalMin g s t ≤ factor * g v
    exact mul_le_mul_of_nonneg_left (intervalMin_le g s t hv) hf

/-- The coding pseudodistance is homogeneous under nonnegative multiplication. -/
theorem codingDist_smul (g : C(unitInterval, ℝ)) (factor : ℝ) (hf : 0 ≤ factor)
    (s t : unitInterval) :
    codingDist (factor • g) s t = factor * codingDist g s t := by
  rw [codingDist, intervalMin_smul g factor hf]
  change factor * g s + factor * g t - 2 * (factor * intervalMin g s t) =
    factor * (g s + g t - 2 * intervalMin g s t)
  ring

/-- The map between coding quotients represented by keeping the same time. -/
noncomputable def scalingMap (g : C(unitInterval, ℝ)) (factor : ℝ) (hf : 0 ≤ factor) :
    Space g → Space (factor • g) :=
  SeparationQuotient.lift (fun x : Point g => projection (factor • g) x.time) (by
    intro x y hxy
    apply dist_eq_zero.mp
    rw [dist_projection, codingDist_smul g factor hf]
    have hz : codingDist g x.time y.time = 0 := Metric.inseparable_iff.mp hxy
    rw [hz, mul_zero])

@[simp] theorem scalingMap_projection (g : C(unitInterval, ℝ)) (factor : ℝ) (hf : 0 ≤ factor)
    (t : unitInterval) :
    scalingMap g factor hf (projection g t) = projection (factor • g) t := rfl

theorem dist_scalingMap (g : C(unitInterval, ℝ)) (factor : ℝ) (hf : 0 ≤ factor)
    (x y : Space g) :
    dist (scalingMap g factor hf x) (scalingMap g factor hf y) = factor * dist x y := by
  obtain ⟨s, rfl⟩ := projection_surjective g x
  obtain ⟨t, rfl⟩ := projection_surjective g y
  simp only [scalingMap_projection, dist_projection, codingDist_smul g factor hf]

theorem scalingMap_surjective (g : C(unitInterval, ℝ)) (factor : ℝ) (hf : 0 ≤ factor) :
    Function.Surjective (scalingMap g factor hf) := by
  intro x
  obtain ⟨t, rfl⟩ := projection_surjective (factor • g) x
  exact ⟨projection g t, rfl⟩

/-- The same-time map is an isometry when its source carries the positively scaled metric. -/
theorem isometry_scalingMap_ofScaled (g : C(unitInterval, ℝ)) (factor : ℝ)
    (hf : 0 < factor) :
    Isometry (fun x : ScaledMetric ⟨factor, hf⟩ (Space g) =>
      scalingMap g factor hf.le (ScaledMetric.ofScaled ⟨factor, hf⟩ (X := Space g) x)) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_scalingMap]
  have h := ScaledMetric.dist_toScaled ⟨factor, hf⟩ (X := Space g)
    (ScaledMetric.ofScaled ⟨factor, hf⟩ (X := Space g) x)
    (ScaledMetric.ofScaled ⟨factor, hf⟩ (X := Space g) y)
  simpa only [ScaledMetric.toScaled_ofScaled] using h.symm

/-- The spatially scaled coded tree is isometric to the tree coded by the scaled function. -/
noncomputable def scalingIsometry (g : C(unitInterval, ℝ)) (factor : ℝ) (hf : 0 < factor) :
    ScaledMetric ⟨factor, hf⟩ (Space g) ≃ᵢ Space (factor • g) where
  toEquiv := Equiv.ofBijective
    (fun x => scalingMap g factor hf.le (ScaledMetric.ofScaled ⟨factor, hf⟩ (X := Space g) x))
    ⟨(isometry_scalingMap_ofScaled g factor hf).injective, by
      intro y
      obtain ⟨x, hx⟩ := scalingMap_surjective g factor hf.le y
      exact ⟨ScaledMetric.toScaled ⟨factor, hf⟩ x, hx⟩⟩
  isometry_toFun := isometry_scalingMap_ofScaled g factor hf

@[simp] theorem scalingIsometry_projection (g : C(unitInterval, ℝ)) (factor : ℝ)
    (hf : 0 < factor) (t : unitInterval) :
    scalingIsometry g factor hf (ScaledMetric.toScaled ⟨factor, hf⟩ (projection g t)) =
      projection (factor • g) t := rfl

/-- The natural isometry preserves the actual Lebesgue pushforward mass. -/
theorem map_mass_scalingIsometry (g : C(unitInterval, ℝ)) (factor : ℝ) (hf : 0 < factor) :
    ((mass g : Measure (Space g)).map (ScaledMetric.toScaled ⟨factor, hf⟩)).map
      (scalingIsometry g factor hf) = (mass (factor • g) : Measure (Space (factor • g))) := by
  rw [coe_mass, coe_mass,
    Measure.map_map (ScaledMetric.measurable_toScaled _) (measurable_projection g),
    Measure.map_map (scalingIsometry g factor hf).continuous.measurable
      ((ScaledMetric.measurable_toScaled _).comp (measurable_projection g))]
  congr 1

/-- Scaling the function scales the entire rooted measured tree, without changing mass. -/
theorem measuredIsometry_scaling (g : C(unitInterval, ℝ)) (factor : ℝ) (hf : 0 < factor) :
    RootedCompactMeasuredSpace.MeasuredIsometry
      (RootedCompactMeasuredSpace.scale factor hf (rootedCompactMeasuredSpace g))
      (rootedCompactMeasuredSpace (factor • g)) := by
  refine ⟨scalingIsometry g factor hf, ?_, ?_⟩
  · exact map_mass_scalingIsometry g factor hf
  · exact scalingIsometry_projection g factor hf 0

/-- Equality of the corresponding rooted measured isometry classes. -/
theorem rootedMeasuredGHSpace_smul (g : C(unitInterval, ℝ)) (factor : ℝ) (hf : 0 < factor) :
    RootedMeasuredGHSpace.scale factor hf (rootedMeasuredGHSpace g) =
      rootedMeasuredGHSpace (factor • g) :=
  Quotient.sound (measuredIsometry_scaling g factor hf)

end BGW.ContinuumTrees.Coding
