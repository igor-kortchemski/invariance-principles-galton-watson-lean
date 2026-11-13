/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.GromovHausdorffProkhorov

/-!
# Transport of the GHP infimum by measured isometries

Precomposition by a surjective isometry preserves each ambient cost, including
the pushed measure and the entire embedded image. Hence the infimum is invariant
under measure-preserving isometry equivalences and symmetric in its arguments.

Adapted from `Freezing2/Geometry/GHPTransport.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Metric Set

universe u

namespace BGW.MetricMeasure

variable {X X' Y : Type u}
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MetricSpace X'] [MeasurableSpace X'] [BorelSpace X'] [CompactSpace X']
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

theorem ghpCosts_map_isometryEquiv_subset (μ : Measure X) (ν : Measure Y) (e : X ≃ᵢ X') :
    ghpCosts (μ.map e) ν ⊆ ghpCosts μ ν := by
  rintro r ⟨Z, m, i, j, hi, hj, hr⟩
  let := m
  let : TopologicalSpace Z := m.toUniformSpace.toTopologicalSpace
  let : MeasurableSpace Z := borel Z
  let : BorelSpace Z := ⟨rfl⟩
  refine ⟨Z, m, i ∘ e, j, hi.comp e.isometry, hj, ?_⟩
  rw [Measure.map_map hi.continuous.measurable e.continuous.measurable] at hr
  rw [e.surjective.range_comp i]
  exact hr

/-- Isometry transport preserves the complete set of ambient costs. The Borel
structure in each witness is induced by that witness's metric. -/
theorem ghpCosts_map_isometryEquiv (μ : Measure X) (ν : Measure Y) (e : X ≃ᵢ X') :
    ghpCosts (μ.map e) ν = ghpCosts μ ν := by
  apply Set.Subset.antisymm (ghpCosts_map_isometryEquiv_subset μ ν e)
  have h := ghpCosts_map_isometryEquiv_subset (μ.map e) ν e.symm
  have he : (μ.map e).map e.symm = μ := by
    rw [Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
    simp only [Function.comp_def, e.symm_apply_apply, Measure.map_id']
  rwa [he] at h

theorem ghpDistance_map_isometryEquiv (μ : Measure X) (ν : Measure Y) (e : X ≃ᵢ X') :
    ghpDistance (μ.map e) ν = ghpDistance μ ν := by
  simp only [ghpDistance, ghpCosts_map_isometryEquiv μ ν e]

/-- A measure-preserving isometry equivalence preserves the represented GHP
distance. -/
theorem ghpDistance_eq_of_isometryEquiv (μ : Measure X) (μ' : Measure X')
    (ν : Measure Y) (e : X ≃ᵢ X') (hμ : μ.map e = μ') :
    ghpDistance μ ν = ghpDistance μ' ν := by
  rw [← hμ, ghpDistance_map_isometryEquiv]

theorem ghpCosts_comm (μ : Measure X) (ν : Measure Y) : ghpCosts μ ν = ghpCosts ν μ := by
  apply Set.Subset.antisymm
  · rintro r ⟨Z, m, i, j, hi, hj, hr⟩
    refine ⟨Z, m, j, i, hj, hi, ?_⟩
    simpa only [levyProkhorovDist_comm, hausdorffDist_comm] using hr
  · rintro r ⟨Z, m, i, j, hi, hj, hr⟩
    refine ⟨Z, m, j, i, hj, hi, ?_⟩
    simpa only [levyProkhorovDist_comm, hausdorffDist_comm] using hr

theorem ghpDistance_comm (μ : Measure X) (ν : Measure Y) :
    ghpDistance μ ν = ghpDistance ν μ := by
  simp only [ghpDistance, ghpCosts_comm μ ν]

/-- Isometry transport in the right argument also preserves the distance. -/
theorem ghpDistance_map_isometryEquiv_right (ν : Measure Y) (μ : Measure X) (e : X ≃ᵢ X') :
    ghpDistance ν (μ.map e) = ghpDistance ν μ := by
  rw [ghpDistance_comm ν, ghpDistance_map_isometryEquiv, ghpDistance_comm μ]

end BGW.MetricMeasure
