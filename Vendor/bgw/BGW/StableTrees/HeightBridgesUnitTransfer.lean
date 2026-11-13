/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridgesCompact
public import BGW.StableTrees.GammaIdentity

/-!
# Transfer of height approximation limits to the unit excursion law

The unit prefix density transfers existence of an approximation limit. A measurable
prefix representative is extracted from convergence in measure before changing the law.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- Unit prefixes are absolutely continuous with respect to the corresponding surviving
excursion prefixes. -/
theorem unitPrefix_absolutelyContinuous_excursion {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (t : ℝ≥0) (ht0 : 0 < t) (ht1 : t < 1) :
    unitPrefix θ t ≪
      ((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime}).map
        (excursionRestrict t) := by
  have htail : (tailExcursionLaw θ : Measure Excursion) ≪
      (excursionMeasure θ).restrict {e : Excursion | t < e.lifetime} := by
    rw [coe_tailExcursionLaw hθ, tailExcursionMeasure]
    apply Measure.smul_absolutelyContinuous.trans
    apply Measure.absolutelyContinuous_of_le
    exact Measure.restrict_mono_set _ (fun _ he => ht1.trans he)
  have hprefix : tailPrefix θ t ≪
      ((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime}).map
        (excursionRestrict t) := by
    apply Measure.AbsolutelyContinuous.mk
    intro A hA hnull
    rw [Measure.map_apply (measurable_excursionRestrict t) hA] at hnull
    rw [tailPrefix, Measure.map_apply (measurable_excursionRestrict t) hA]
    exact htail hnull
  rw [levyExcLaw_prefix_eq_withDensity_tail hθ t ⟨ht0, ht1⟩]
  exact (withDensity_absolutelyContinuous _ _).trans hprefix

/-- Existence of an excursion approximation limit implies existence of a unit-law limit.
The excursion convergence hypothesis remains an independent obligation. -/
theorem exists_heightApprox_tendstoInMeasure_unit_of_excursion {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) (ht0 : 0 < t) (ht1 : t < 1)
    (hN : ∃ L : Excursion → ℝ, Measurable L ∧ TendstoInMeasure
      ((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime})
      (fun (ε : ℝ) (e : Excursion) => heightApprox ε e.path t) (𝓝[>] (0 : ℝ)) L) :
    ∃ L : Excursion → ℝ, Measurable L ∧ TendstoInMeasure
      (unitExcursionLaw θ : Measure Excursion)
      (fun (ε : ℝ) (e : Excursion) => heightApprox ε e.path t) (𝓝[>] (0 : ℝ)) L := by
  obtain ⟨L, _, hconv⟩ := hN
  have hbase : TendstoInMeasure
      ((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime})
      (fun ε e => horizonHeightApprox ε t (excursionRestrict t e)) (𝓝[>] (0 : ℝ)) L := by
    simpa only [excursionRestrict, horizonHeightApprox_restrict] using hconv
  obtain ⟨L', hL', hconv'⟩ := exists_tendstoInMeasure_of_prefix_absolutelyContinuous
    (measurable_excursionRestrict t) (fun ε => measurable_horizonHeightApprox ε t) hbase
    (unitPrefix_absolutelyContinuous_excursion hθ t ht0 ht1)
  refine ⟨L', hL', ?_⟩
  simpa only [excursionRestrict, horizonHeightApprox_restrict] using hconv'

end BGW.StableTrees
