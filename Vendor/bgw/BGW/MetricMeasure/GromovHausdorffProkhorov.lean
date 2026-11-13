/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.MeasuredGluing

/-!
# The Gromov–Hausdorff–Prokhorov infimum

The cost is the sum of Lévy–Prokhorov and Hausdorff distances after isometric
embeddings into one ambient metric space. Hausdorff distance uses the images
of the whole carriers, with no full-support assumption on the measures. The
spaces and ambient realizations lie in the same universe.

The intended GHP setting is nonempty compact metric spaces with Borel probability
measures. The raw infimum below also accepts arbitrary measures, as in the source.
This module supplies nonnegativity and upper bounds on represented spaces;
the triangle inequality, separation and passage to isometry classes are separate
obligations.

Adapted from `Freezing2/Geometry/GromovHausdorffProkhorov.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped Topology

universe u

namespace BGW.MetricMeasure

variable {X Y : Type u} [MetricSpace X] [MeasurableSpace X]
  [MetricSpace Y] [MeasurableSpace Y]

/-- The costs of all common ambient realizations in the same universe, with
their Borel measurable structures and isometric embeddings of the whole carriers.

The compactness and Borel assumptions are not used by the formula; they fix its domain.
Compactness of both carriers, together with their nonemptiness (automatic for the carriers of
probability measures, as in `CompactMeasuredSpace`), makes the Hausdorff distance between the
embedded carriers finite. Compactness alone does not exclude an empty carrier facing a nonempty
one, in which case Mathlib's real `hausdorffDist` takes its default value `0`. The Borel
assumptions make the isometric embeddings measurable, so that the pushforward measures in the
Lévy–Prokhorov term are meaningful (`Measure.map` of a non-measurable map is `0`); they play no
role in the finiteness of the Hausdorff term. -/
@[nolint unusedArguments]
def ghpCosts [CompactSpace X] [BorelSpace X] [CompactSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) : Set ℝ :=
  {r | ∃ Z : Type u, ∃ m : MetricSpace Z,
    letI := m
    letI : TopologicalSpace Z := m.toUniformSpace.toTopologicalSpace
    letI : MeasurableSpace Z := borel Z
    ∃ i : X → Z, ∃ j : Y → Z, Isometry i ∧ Isometry j ∧
      r = levyProkhorovDist (μ.map i) (ν.map j) + hausdorffDist (range i) (range j)}

/-- The GHP infimum on represented compact measured spaces, before passage to
measure-preserving isometry classes. Its compactness and Borel assumptions fix the domain, as
explained for `ghpCosts`: they are what makes the costs meaningful, for nonempty carriers. -/
noncomputable def ghpDistance [CompactSpace X] [BorelSpace X] [CompactSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) : ℝ := sInf (ghpCosts μ ν)

variable [CompactSpace X] [BorelSpace X] [CompactSpace Y] [BorelSpace Y]

theorem ghpCosts_bddBelow (μ : Measure X) (ν : Measure Y) : BddBelow (ghpCosts μ ν) := by
  refine ⟨0, ?_⟩
  rintro r ⟨Z, m, i, j, hi, hj, rfl⟩
  exact add_nonneg ENNReal.toReal_nonneg hausdorffDist_nonneg

theorem ghpCosts_nonempty (μ : Measure X) (ν : Measure Y) : (ghpCosts μ ν).Nonempty := by
  let : MetricSpace (X ⊕ Y) := metricSpaceSum
  let : MeasurableSpace (X ⊕ Y) := borel (X ⊕ Y)
  refine ⟨_, X ⊕ Y, inferInstance, @Sum.inl X Y, @Sum.inr X Y, ?_, ?_, rfl⟩
  · exact Isometry.of_dist_eq fun _ _ ↦ rfl
  · exact Isometry.of_dist_eq fun _ _ ↦ rfl

theorem ghpDistance_nonneg (μ : Measure X) (ν : Measure Y) : 0 ≤ ghpDistance μ ν := by
  apply le_csInf (ghpCosts_nonempty μ ν)
  rintro r ⟨Z, m, i, j, hi, hj, rfl⟩
  exact add_nonneg ENNReal.toReal_nonneg hausdorffDist_nonneg

/-- Any common ambient realization gives an upper bound for the GHP infimum. -/
theorem ghpDistance_le_of_isometries (μ : Measure X) (ν : Measure Y)
    (Z : Type u) [MetricSpace Z] (i : X → Z) (j : Y → Z)
    (hi : Isometry i) (hj : Isometry j) :
    letI : MeasurableSpace Z := borel Z
    ghpDistance μ ν ≤ levyProkhorovDist (μ.map i) (ν.map j) +
      hausdorffDist (range i) (range j) := by
  apply csInf_le (ghpCosts_bddBelow μ ν)
  exact ⟨Z, inferInstance, i, j, hi, hj, rfl⟩

/-- A measurable map with small distortion, dense image and close pushed
measure gives a quantitative GHP upper bound. -/
theorem ghpDistance_le_of_approx [Nonempty X] [Nonempty Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → Y) (hf : Measurable f) {δ r p : ℝ} (hδ : 0 < δ)
    (hdis : ∀ x x', |dist x x' - dist (f x) (f x')| ≤ 2 * δ)
    (hdense : ∀ y, ∃ x, dist y (f x) ≤ r)
    (hprob : levyProkhorovDist (μ.map f) ν ≤ p) :
    ghpDistance μ ν ≤ 2 * δ + r + p := by
  obtain ⟨m, hl, hr, hH, hP⟩ := exists_measured_gluing μ ν f hf hδ hdis hdense hprob
  let := m
  let : TopologicalSpace (X ⊕ Y) := m.toUniformSpace.toTopologicalSpace
  let : MeasurableSpace (X ⊕ Y) := borel (X ⊕ Y)
  have h := ghpDistance_le_of_isometries μ ν (X ⊕ Y) (@Sum.inl X Y) (@Sum.inr X Y) hl hr
  calc
    _ ≤ levyProkhorovDist (μ.map (@Sum.inl X Y)) (ν.map (@Sum.inr X Y)) +
        hausdorffDist (range (@Sum.inl X Y)) (range (@Sum.inr X Y)) := h
    _ ≤ (δ + p) + (δ + r) := add_le_add hP hH
    _ = 2 * δ + r + p := by ring

end BGW.MetricMeasure
