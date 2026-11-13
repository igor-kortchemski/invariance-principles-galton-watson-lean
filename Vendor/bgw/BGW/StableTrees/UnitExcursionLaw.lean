/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionLawSupport

/-! # Unit excursion law, lifetime/shape identity, path mixture and endpoint support

Main results:

* `unitExcursionLaw`, `tailExcursionLaw`: the unit and tail excursion laws, and `levyExcLaw`,
  `tailLevyExcLaw` their images as laws on Skorokhod space.
* `excursionAt`: the family of scaled unit excursions, with exact scaling
  (`map_excursionScale_excursionAt`).
* `shapeLifetime_map_excursionMeasure`: under the excursion measure, lifetime and normalized shape
  form a product.
* `excursionMeasure_eq_lifetime_mixture`, `lintegral_excursionMeasure_eq_mixture`: the excursion
  measure is the mixture of the scaled unit excursions over the lifetime.
* `excursionMeasure_unique_of_scaling`: uniqueness of the excursion measure from scaling.
* `levyExcLaw_endpoints_pos` and its `Excursion`-level version: endpoint and positivity statements.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VIII.
* T. Duquesne and J.-F. Le Gall, *Random Trees, Lévy Processes and Spatial Branching Processes*,
  Astérisque 281 (2002).
* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Endpoints and positivity for the unit excursion**: almost surely
`e 0 = 0`, `e t > 0` on `(0,1)`, `e 1 = 0` and the left limit at `1` is `0`. -/
theorem levyExcLaw_endpoints_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ x ∂(levyExcLaw θ).toMeasure,
      (x : D 1 ℝ) ⟨0, by norm_num, zero_le_one⟩ = 0 ∧
      (∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < x t) ∧
      x ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
      Function.leftLim (x : Set.Icc (0 : ℝ) 1 → ℝ) ⟨1, zero_le_one, le_rfl⟩ = 0 := by
  let E : Set Excursion := {e | e.lifetime = 1}
  have hE : MeasurableSet E :=
    measurableSet_eq_fun measurable_excursion_lifetime measurable_const
  let : StandardBorelSpace E := hE.standardBorel
  let f : E → D 1 ℝ := fun e => excursionRestrict 1 e.1
  have hf : Measurable f := (measurable_excursionRestrict 1).comp measurable_subtype_coe
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      funext t
      change x.1.path.1 t = y.1.path.1 t
      by_cases ht : t ≤ 1
      · exact congrArg (fun z : D 1 ℝ => z ⟨(t : ℝ), t.2, by exact_mod_cast ht⟩) hxy
      · calc
          _ = 0 := x.1.2.2.2 t
            (by change x.1.lifetime ≤ t; rw [x.2]; exact le_of_not_ge ht)
          _ = _ := (y.1.2.2.2 t
            (by change y.1.lifetime ≤ t; rw [y.2]; exact le_of_not_ge ht)).symm
    · apply Subtype.ext
      exact x.2.trans y.2.symm
  have hμ : ((unitExcursionLaw θ : Measure Excursion).comap (Subtype.val : E → Excursion)).map
      Subtype.val = (unitExcursionLaw θ : Measure Excursion) := by
    rw [map_comap_subtype_coe hE]
    exact Measure.restrict_eq_self_of_ae_mem (ae_lifetime_unitExcursionLaw hθ)
  have hm : (levyExcLaw θ : Measure (D 1 ℝ)) =
      ((unitExcursionLaw θ : Measure Excursion).comap (Subtype.val : E → Excursion)).map f := by
    calc
      _ = (unitExcursionLaw θ : Measure Excursion).map (excursionRestrict 1) := rfl
      _ = (((unitExcursionLaw θ : Measure Excursion).comap
          (Subtype.val : E → Excursion)).map Subtype.val).map (excursionRestrict 1) :=
        congrArg (fun μ : Measure Excursion => μ.map (excursionRestrict 1)) hμ.symm
      _ = _ := by
        rw [Measure.map_map (measurable_excursionRestrict 1) measurable_subtype_coe]
        rfl
  rw [hm, (hf.measurableEmbedding hinj).ae_map_iff]
  have hg := ae_of_ae_map (μ := (unitExcursionLaw θ : Measure Excursion).comap
    (Subtype.val : E → Excursion)) measurable_subtype_coe.aemeasurable
    (show ∀ᵐ e ∂(((unitExcursionLaw θ : Measure Excursion).comap
      (Subtype.val : E → Excursion)).map Subtype.val),
      e.path.1 0 = 0 ∧ (∀ t : ℝ≥0, 0 < t → t < 1 → 0 < e.path.1 t) ∧
        Function.leftLim e.path.1 1 = 0 from by
      rw [hμ]
      exact ae_unitExcursionLaw_positive hθ)
  filter_upwards [hg] with e he
  refine ⟨he.1, ?_, ?_, ?_⟩
  · intro t ht htl
    exact he.2.1 ⟨t, t.2.1⟩ (by exact_mod_cast ht) (by exact_mod_cast htl)
  · exact e.1.2.2.2 1 (by change e.1.lifetime ≤ 1; rw [e.2])
  · let top : Icc (0 : ℝ) 1 := ⟨1, zero_le_one, le_rfl⟩
    let inc : Icc (0 : ℝ) 1 → ℝ≥0 := fun t => ⟨t, t.2.1⟩
    have hc : Continuous inc := continuous_subtype_val.subtype_mk fun t => t.2.1
    let : NeBot (𝓝[<] top) := nhdsLT_neBot_of_exists_lt
      ⟨⟨0, le_rfl, zero_le_one⟩, by change (0 : ℝ) < 1; norm_num⟩
    apply leftLim_eq_of_tendsto
    have hmap : Tendsto inc (𝓝[<] top) (𝓝[<] (1 : ℝ≥0)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact ht
    have hl := e.1.path.2.tendsto_nhdsLT_leftLim (1 : ℝ≥0)
    rw [he.2.2] at hl
    exact hl.comp hmap

end BGW.StableTrees
