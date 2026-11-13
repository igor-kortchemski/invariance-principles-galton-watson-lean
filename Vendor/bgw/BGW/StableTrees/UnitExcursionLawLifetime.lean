/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionLawBasic

/-! # Lifetime marginal and atomlessness of normalized tail laws

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The lifetime density defines a sigma-finite measure for every index. -/
theorem sigmaFinite_lifetimeLaw (θ : ℝ) : SigmaFinite (lifetimeLaw θ) := by
  let : SigmaFinite volIoi := sigmaFinite_volIoi
  unfold lifetimeLaw lifetimeDensity
  exact SigmaFinite.withDensity_ofReal _

/-- **Lifetime marginal on the positive half-line**: `(lifetimePos)_* N = lifetimeLaw`. -/
theorem map_lifetimePos_excursionMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (excursionMeasure θ).map Excursion.lifetimePos = lifetimeLaw θ := by
  ext B hB
  let C : Set ℝ := Subtype.val '' B
  have hC : MeasurableSet C :=
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi).measurableSet_image.mpr hB
  let S : Set ℝ≥0 := ((↑) : ℝ≥0 → ℝ) ⁻¹' C
  have hS : MeasurableSet S := hC.preimage measurable_subtype_coe
  have hpre : Excursion.lifetime ⁻¹' S = Excursion.lifetimePos ⁻¹' B := by
    ext e
    change (e.lifetime : ℝ) ∈ Subtype.val '' B ↔ e.lifetimePos ∈ B
    exact Subtype.coe_injective.mem_set_image (s := B) (a := e.lifetimePos)
  rw [Measure.map_apply measurable_lifetimePos hB, ← hpre,
    ← Measure.map_apply measurable_excursion_lifetime hS,
    excursionMeasure_lifetime_density hθ, withDensity_apply _ hS,
    lifetimeLaw, withDensity_apply _ hB]
  change (∫⁻ u in S, lifetimeDensity θ u ∂volume.comap ((↑) : ℝ≥0 → ℝ)) =
    ∫⁻ u in B, lifetimeDensity θ u ∂volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)
  have hi : (∫⁻ u in S, lifetimeDensity θ u ∂volume.comap ((↑) : ℝ≥0 → ℝ)) =
      ∫⁻ u in ((↑) : ℝ≥0 → ℝ) '' S, lifetimeDensity θ u :=
    setLIntegral_subtype (μ := volume) measurableSet_Ici S (lifetimeDensity θ)
  rw [hi, setLIntegral_subtype measurableSet_Ioi B (lifetimeDensity θ)]
  have hset : ((↑) : ℝ≥0 → ℝ) '' S = Subtype.val '' B := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, u.2.le⟩, ⟨u, hu, rfl⟩, rfl⟩
  rw [hset]

/-- No positive lifetime is charged by `N`. -/
theorem excursionMeasure_lifetime_eq_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ) (ha : 0 < a) :
    excursionMeasure θ {e : Excursion | (e.lifetime : ℝ) = a} = 0 := by
  have hm := congrArg (fun μ : Measure ℝ≥0 => μ {a.toNNReal})
    (excursionMeasure_lifetime_density hθ)
  rw [Measure.map_apply measurable_excursion_lifetime (measurableSet_singleton _)] at hm
  have hz : lebNN {a.toNNReal} = 0 := by
    change volume.comap ((↑) : ℝ≥0 → ℝ) {a.toNNReal} = 0
    have hi : volume.comap ((↑) : ℝ≥0 → ℝ) {a.toNNReal} =
        volume (((↑) : ℝ≥0 → ℝ) '' {a.toNNReal}) :=
      comap_subtype_coe_apply measurableSet_Ici volume ({a.toNNReal} : Set ℝ≥0)
    rw [hi]
    simp
  have hn := withDensity_absolutelyContinuous lebNN
    (fun t : ℝ≥0 => ENNReal.ofReal ((1 / θ) / Real.Gamma (1 - 1 / θ) *
      (t : ℝ) ^ (-1 - 1 / θ))) hz
  rw [hn] at hm
  convert hm using 2
  ext e
  simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff]
  exact ⟨fun h => NNReal.eq (by simpa [Real.coe_toNNReal _ ha.le] using h),
    fun h => by rw [h, Real.coe_toNNReal _ ha.le]⟩

/-- No lifetime is charged by the tail law. -/
theorem tailExcursionLaw_lifetime_eq_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ) :
    (tailExcursionLaw θ : Measure Excursion) {e : Excursion | (e.lifetime : ℝ) = a} = 0 := by
  rw [coe_tailExcursionLaw hθ, tailExcursionMeasure, Measure.smul_apply, smul_eq_mul]
  have hz : excursionMeasure θ {e : Excursion | (e.lifetime : ℝ) = a} = 0 := by
    by_cases ha : 0 < a
    · exact excursionMeasure_lifetime_eq_zero hθ a ha
    · have hempty : {e : Excursion | (e.lifetime : ℝ) = a} = ∅ := by
        ext e
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        intro he
        exact ha (he ▸ NNReal.coe_pos.mpr e.lifetime_pos)
      rw [hempty, measure_empty]
  have hr : excursionTail θ 1 {e : Excursion | (e.lifetime : ℝ) = a} = 0 := by
    rw [excursionTail, Measure.restrict_apply
      (measurableSet_eq_fun measurable_excursion_lifetime.coe_nnreal_real measurable_const)]
    exact measure_mono_null inter_subset_left hz
  rw [hr, mul_zero]

end BGW.StableTrees
