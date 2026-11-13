/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.CodingMeasure
public import BGW.MetricMeasure.RootedMeasuredGHSpace
public import BGW.MetricMeasure.RootedCommonSource
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Tactic.Linarith

/-!
# Stability of continuously coded measured trees

Uniform distance between coding functions bounds the distance between their interval minima
and the distortion between the quotient projections. Gluing the two coded spaces along their
common time parameter bounds Hausdorff distance, Lévy–Prokhorov distance and root distance
simultaneously. With the project's sum convention, the resulting bounds are four times the
uniform norm in GHP and six times that norm in rooted GHP.

The map to rooted measured isometry classes is therefore Lipschitz, continuous and measurable.
All results hold for arbitrary continuous real coding functions, without sign or endpoint
conditions. The common-source GHP bound uses Mathlib's approximate metric gluing;
no measurable choice of time representatives is needed.
-/

@[expose] public section

open MeasureTheory Metric Set
open BGW.MetricMeasure

namespace BGW.ContinuumTrees.Coding

/-- The interval minimum changes by at most the uniform norm of the change in coding function. -/
theorem abs_intervalMin_sub_le_norm (g h : C(unitInterval, ℝ)) (s t : unitInterval) :
    |intervalMin g s t - intervalMin h s t| ≤ ‖g - h‖ := by
  have hpoint (r : unitInterval) : |g r - h r| ≤ ‖g - h‖ := by
    simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs] using (g - h).norm_coe_le_norm r
  obtain ⟨r, hr, hgr⟩ := exists_intervalMin g s t
  obtain ⟨v, hv, hhv⟩ := exists_intervalMin h s t
  have hgv := intervalMin_le g s t hv
  have hhr := intervalMin_le h s t hr
  have hpr := abs_le.mp (hpoint r)
  have hpv := abs_le.mp (hpoint v)
  apply abs_le.mpr
  constructor <;> linarith

/-- The correspondence given by common times has distortion at most four uniform norms. -/
theorem abs_codingDist_sub_le_norm (g h : C(unitInterval, ℝ)) (s t : unitInterval) :
    |codingDist g s t - codingDist h s t| ≤ 4 * ‖g - h‖ := by
  have hs : |g s - h s| ≤ ‖g - h‖ := by
    simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs] using (g - h).norm_coe_le_norm s
  have ht : |g t - h t| ≤ ‖g - h‖ := by
    simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs] using (g - h).norm_coe_le_norm t
  have hm := abs_le.mp (abs_intervalMin_sub_le_norm g h s t)
  obtain ⟨hs₁, hs₂⟩ := abs_le.mp hs
  obtain ⟨ht₁, ht₂⟩ := abs_le.mp ht
  unfold codingDist
  apply abs_le.mpr
  constructor <;> linarith

private theorem distance_le_of_distortion (g h : C(unitInterval, ℝ)) {ε : ℝ}
    (hε : 0 < ε)
    (hdis : ∀ s t, |codingDist g s t - codingDist h s t| ≤ 2 * ε) :
    CompactMeasuredSpace.distance (compactMeasuredSpace g) (compactMeasuredSpace h) ≤ 2 * ε ∧
      RootedCompactMeasuredSpace.distance
        (rootedCompactMeasuredSpace g) (rootedCompactMeasuredSpace h) ≤ 3 * ε := by
  have hdis' : ∀ s t,
      |dist (projection g s) (projection g t) - dist (projection h s) (projection h t)| ≤
        2 * ε := by
    intro s t
    simpa only [dist_projection] using hdis s t
  constructor
  · change ghpDistance (mass g : Measure (Space g)) (mass h : Measure (Space h)) ≤ 2 * ε
    rw [coe_mass, coe_mass]
    exact ghpDistance_map_le_of_distortion (volume : Measure unitInterval)
      (projection g) (projection h) (measurable_projection g) (measurable_projection h)
      (projection_surjective g) (projection_surjective h) hε hdis'
  · change rootedGHPDistance (mass g : Measure (Space g)) (mass h : Measure (Space h))
      (root g) (root h) ≤ 3 * ε
    rw [coe_mass, coe_mass]
    exact rootedGHPDistance_map_le_of_distortion (volume : Measure unitInterval)
      (projection g) (projection h) (measurable_projection g) (measurable_projection h)
      (projection_surjective g) (projection_surjective h) hε hdis' 0

/-- Stability in the summed GHP distance, with the entire coded carriers retained. -/
theorem compactMeasuredSpace_distance_le (g h : C(unitInterval, ℝ)) :
    CompactMeasuredSpace.distance (compactMeasuredSpace g) (compactMeasuredSpace h) ≤
      4 * ‖g - h‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hn := norm_nonneg (g - h)
  have hgap : 0 < 2 * ‖g - h‖ + ε / 2 := by linarith
  have hb := (distance_le_of_distortion g h hgap (fun s t =>
    (abs_codingDist_sub_le_norm g h s t).trans (by linarith))).1
  linarith

/-- Stability in rooted GHP, using the sum of root, Hausdorff and Lévy–Prokhorov costs. -/
theorem rootedCompactMeasuredSpace_distance_le (g h : C(unitInterval, ℝ)) :
    RootedCompactMeasuredSpace.distance
      (rootedCompactMeasuredSpace g) (rootedCompactMeasuredSpace h) ≤ 6 * ‖g - h‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hn := norm_nonneg (g - h)
  have hgap : 0 < 2 * ‖g - h‖ + ε / 3 := by linarith
  have hb := (distance_le_of_distortion g h hgap (fun s t =>
    (abs_codingDist_sub_le_norm g h s t).trans (by linarith))).2
  linarith

/-- The rooted measured isometry class of the coded tree. -/
noncomputable def rootedMeasuredGHSpace (g : C(unitInterval, ℝ)) : RootedMeasuredGHSpace :=
  toRootedMeasuredGHSpace (rootedCompactMeasuredSpace g)

theorem lipschitzWith_rootedMeasuredGHSpace : LipschitzWith 6 rootedMeasuredGHSpace := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  simpa only [rootedMeasuredGHSpace,
    RootedMeasuredGHSpace.dist_toRootedMeasuredGHSpace, dist_eq_norm, NNReal.coe_ofNat] using
    rootedCompactMeasuredSpace_distance_le g h

theorem continuous_rootedMeasuredGHSpace : Continuous rootedMeasuredGHSpace :=
  lipschitzWith_rootedMeasuredGHSpace.continuous

theorem measurable_rootedMeasuredGHSpace : Measurable rootedMeasuredGHSpace :=
  continuous_rootedMeasuredGHSpace.measurable

end BGW.ContinuumTrees.Coding
