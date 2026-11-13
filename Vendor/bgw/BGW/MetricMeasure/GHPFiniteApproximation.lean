/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.GromovHausdorffProkhorov

/-!
# Finite measured approximations in the exact GHP distance

A finite cover of the entire compact carrier gives a measurable finite-valued
map by testing its balls one at a time. Its pushforward supplies the finite
weights; no support or positivity condition on those weights is imposed.
The common ambient space is the original carrier, and both the Hausdorff and
Prokhorov contributions are bounded by the covering radius.

Adapted from `Freezing2/Geometry/GHPFiniteApproximation.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Metric Set

universe u

namespace BGW.MetricMeasure

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Finite ball tests give a measurable choice on the part covered by a finite
set. Outside the cover the default value is immaterial. -/
theorem exists_measurable_finite_ball_selector (s : Finset X) (a : X) (ε : ℝ) :
    ∃ f : X → X, Measurable f ∧ ∀ x,
      (∃ y ∈ s, dist x y < ε) → f x ∈ s ∧ dist x (f x) < ε := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨fun _ ↦ a, measurable_const, ?_⟩
      simp
  | @insert b s hb ih =>
      obtain ⟨f, hf, hselect⟩ := ih
      refine ⟨fun x ↦ if dist x b < ε then b else f x, ?_, ?_⟩
      · exact measurable_const.ite
          (measurableSet_lt (continuous_id.dist continuous_const).measurable
            measurable_const) hf
      · intro x hx
        by_cases hxb : dist x b < ε
        · simp only [ite_eq_left hxb]
          exact ⟨Finset.mem_insert_self _ _, hxb⟩
        · obtain ⟨y, hy, hxy⟩ := hx
          have hys : y ∈ s := by
            rcases Finset.mem_insert.mp hy with rfl | hys
            · exact (hxb hxy).elim
            · exact hys
          obtain ⟨hmem, hdist⟩ := hselect x ⟨y, hys, hxy⟩
          simp only [ite_eq_right hxb]
          exact ⟨Finset.mem_insert_of_mem hmem, hdist⟩

/-- A measurable choice of a covering center, constructed by finitely many
measurable tests rather than by an assumed selection principle. -/
theorem exists_measurable_net_projection [Nonempty X] (s : Finset X) {ε : ℝ}
    (hcover : ∀ x, ∃ y ∈ s, dist x y < ε) :
    ∃ q : X → ↥s, Measurable q ∧ ∀ x, dist x (q x : X) < ε := by
  classical
  obtain ⟨f, hf, hselect⟩ :=
    exists_measurable_finite_ball_selector s (Classical.arbitrary X) ε
  let q : X → ↥s := fun x ↦ ⟨f x, (hselect x (hcover x)).1⟩
  exact ⟨q, hf.subtype_mk, fun x ↦ (hselect x (hcover x)).2⟩

/-- Every nonempty compact carrier has a nonempty finite net and a measurable
projection to it. The coverage statement includes points of zero measure. -/
theorem exists_finite_measurable_net [Nonempty X] [CompactSpace X] {ε : ℝ}
    (hε : 0 < ε) :
    ∃ s : Finset X, s.Nonempty ∧ ∃ q : X → ↥s,
      Measurable q ∧ ∀ x, dist x (q x : X) < ε := by
  classical
  obtain ⟨t, _, ht, hcover⟩ := finite_cover_balls_of_compact
    (isCompact_univ : IsCompact (univ : Set X)) hε
  have hnet : ∀ x, ∃ y ∈ ht.toFinset, dist x y < ε := by
    intro x
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
    exact ⟨y, ht.mem_toFinset.mpr hy, hxy⟩
  obtain ⟨q, hq, hclose⟩ := exists_measurable_net_projection ht.toFinset hnet
  refine ⟨ht.toFinset, ?_, q, hq, hclose⟩
  obtain ⟨y, hy, _⟩ := hnet (Classical.arbitrary X)
  exact ⟨y, hy⟩

/-- The exact pushforward to a finite net approximates the original probability
measure in the manuscript's summed GHP distance. Centers of zero pushforward
mass are retained in the finite metric space. -/
theorem ghpDistance_finite_projection_le [CompactSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : Finset X)
    (q : X → ↥s) (hq : Measurable q) {ε : ℝ} (hε : 0 ≤ ε)
    (hclose : ∀ x, dist x (q x : X) ≤ ε) :
    ghpDistance μ (μ.map q) ≤ 2 * ε := by
  classical
  have hH : hausdorffDist (range (id : X → X))
      (range (fun y : ↥s ↦ (y : X))) ≤ ε := by
    apply hausdorffDist_le_of_mem_dist hε
    · intro x _
      exact ⟨q x, ⟨q x, rfl⟩, hclose x⟩
    · intro y _
      exact ⟨y, ⟨y, rfl⟩, by simpa using hε⟩
  have hP : levyProkhorovDist (μ.map (id : X → X))
      ((μ.map q).map (fun y : ↥s ↦ (y : X))) ≤ ε := by
    rw [Measure.map_map measurable_subtype_coe hq]
    exact levyProkhorovDist_map_le_of_dist_le μ measurable_id
      (measurable_subtype_coe.comp hq) hε hclose
  have hG := ghpDistance_le_of_isometries μ (μ.map q) X id
    (fun y : ↥s ↦ (y : X)) isometry_id (Isometry.of_dist_eq fun _ _ ↦ rfl)
  have hb : borel X = ‹MeasurableSpace X› := BorelSpace.measurable_eq.symm
  apply hG.trans
  calc
    _ ≤ ε + ε := by
      convert add_le_add hP hH using 1
      rw [hb]
    _ = 2 * ε := by ring

/-- Finite measured spaces are dense for the exact GHP distance, with the
measure given explicitly by the measurable projection's pushforward. -/
theorem exists_finite_ghp_approximation [Nonempty X] [CompactSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset X, s.Nonempty ∧ ∃ q : X → ↥s,
      Measurable q ∧ IsProbabilityMeasure (μ.map q) ∧
        (∀ x, dist x (q x : X) < ε) ∧ ghpDistance μ (μ.map q) ≤ 2 * ε := by
  obtain ⟨s, hs, q, hq, hclose⟩ := exists_finite_measurable_net (X := X) hε
  exact ⟨s, hs, q, hq, inferInstance, hclose,
    ghpDistance_finite_projection_le μ s q hq hε.le (fun x ↦ (hclose x).le)⟩

end BGW.MetricMeasure

