/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionLawJoint

/-! # Path and integral mixtures over every positive lifetime

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Reconstructing the lifetime/shape product recovers the excursion measure. -/
theorem map_fromShapeLifetime_product {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ((lifetimeLaw θ).prod (unitExcursionLaw θ : Measure Excursion)).map
      (fromShapeLifetime θ) = excursionMeasure θ := by
  rw [← shapeLifetime_map_excursionMeasure hθ,
    Measure.map_map (measurable_fromShapeLifetime θ) (measurable_shapeLifetime θ),
    show fromShapeLifetime θ ∘ shapeLifetime θ = id from
      funext (fromShapeLifetime_shapeLifetime θ), Measure.map_id]

/-- **Nonnegative mixture**: `∫⁻ F dN = ∫⁻ u>0, (∫⁻ F dN_{(u)}) · density(u) du` for measurable
`F : Excursion → ℝ≥0∞`. -/
theorem lintegral_excursionMeasure_eq_mixture {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {F : Excursion → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ e, F e ∂(excursionMeasure θ) =
      ∫⁻ u, (∫⁻ e, F e ∂(excursionAt θ u)) * lifetimeDensity θ u ∂volIoi := by
  rw [← map_fromShapeLifetime_product hθ,
    lintegral_map hF (measurable_fromShapeLifetime θ),
    lintegral_prod (fun p => F (fromShapeLifetime θ p))
      (hF.comp (measurable_fromShapeLifetime θ)).aemeasurable]
  have hi : (fun u : Ioi (0 : ℝ) => ∫⁻ e, F (fromShapeLifetime θ (u, e))
      ∂(unitExcursionLaw θ : Measure Excursion)) =
      fun u => ∫⁻ e, F e ∂excursionAt θ u := by
    funext u
    exact (lintegral_map hF (measurable_excursionScale θ u)).symm
  rw [hi, lifetimeLaw, lintegral_withDensity_eq_lintegral_mul _
    (measurable_lifetimeDensity θ)]
  · exact lintegral_congr fun u => mul_comm _ _
  · rw [← hi]
    exact (hF.comp (measurable_fromShapeLifetime θ)).lintegral_prod_right'

/-- **Path-only mixture**: for measurable `A`,
`N(A) = ∫⁻ u>0, (S_u)_* unitExcursionLaw (A) · (1/θ)/Γ(1-1/θ) u^{-1-1/θ} du`. -/
theorem excursionMeasure_eq_lifetime_mixture {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {A : Set Excursion}
    (hA : MeasurableSet A) :
    excursionMeasure θ A =
      ∫⁻ u, excursionAt θ u A * lifetimeDensity θ u ∂volIoi := by
  simpa only [lintegral_indicator_fun_one hA] using
    lintegral_excursionMeasure_eq_mixture hθ
      ((measurable_const : Measurable (fun _ : Excursion => (1 : ℝ≥0∞))).indicator hA)

/-- **Restricted nonnegative mixture** over long excursions `{ζ > a}`, `a ≥ 0`. -/
theorem setLIntegral_excursionMeasure_eq_mixture {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {F : Excursion → ℝ≥0∞} (hF : Measurable F) (a : ℝ) (ha : 0 ≤ a) :
    ∫⁻ e in {e : Excursion | a < (e.lifetime : ℝ)}, F e ∂(excursionMeasure θ) =
      ∫⁻ u in {u : Set.Ioi (0 : ℝ) | a < (u : ℝ)},
        (∫⁻ e, F e ∂(excursionAt θ u)) * lifetimeDensity θ u ∂volIoi := by
  -- `ha` is part of the stated interface; the identity holds for every threshold `a`.
  have _ha := ha
  have htail : MeasurableSet {e : Excursion | a < (e.lifetime : ℝ)} :=
    measurableSet_lt measurable_const measurable_excursion_lifetime.coe_nnreal_real
  have hU : MeasurableSet {u : Ioi (0 : ℝ) | a < (u : ℝ)} :=
    measurableSet_lt measurable_const measurable_subtype_coe
  rw [← lintegral_indicator htail, lintegral_excursionMeasure_eq_mixture hθ (hF.indicator htail),
    ← lintegral_indicator hU]
  apply lintegral_congr
  intro u
  have hi : (∫⁻ e, {e : Excursion | a < (e.lifetime : ℝ)}.indicator F e
      ∂excursionAt θ u) =
      if a < (u : ℝ) then ∫⁻ e, F e ∂excursionAt θ u else 0 := by
    split_ifs with hu
    · apply lintegral_congr_ae
      filter_upwards [ae_lifetime_excursionAt hθ u] with e he
      exact indicator_of_mem (by simpa only [mem_ofPred_eq, he] using hu) F
    · apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [ae_lifetime_excursionAt hθ u] with e he
      exact indicator_of_notMem (by simpa only [mem_ofPred_eq, he] using hu) F
  rw [hi]
  by_cases hu : a < (u : ℝ) <;> simp [hu]

private theorem gamma_mul_density {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (u : Ioi (0 : ℝ)) :
    ENNReal.ofReal (Real.Gamma (1 - 1 / θ)) * lifetimeDensity θ u =
      ENNReal.ofReal ((1 / θ) * (u : ℝ) ^ (-1 - 1 / θ)) := by
  have hG : 0 < Real.Gamma (1 - 1 / θ) :=
    Real.Gamma_pos_of_pos (sub_pos.mpr ((div_lt_one (by linarith)).mpr hθ.1))
  rw [lifetimeDensity, ← ENNReal.ofReal_mul hG.le]
  congr 1
  field_simp [hG.ne']

/-- **Mixture for the tail law**: under `N(· | ζ > 1)` the lifetime has density
`α u^{-1-α}` on `u > 1`; for measurable `A ⊆ Excursion`. -/
theorem tailExcursionLaw_eq_mixture {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {A : Set Excursion}
    (hA : MeasurableSet A) :
    (tailExcursionLaw θ : Measure Excursion) A =
      ∫⁻ u, excursionAt θ u A *
        ({u : Set.Ioi (0 : ℝ) | 1 < (u : ℝ)}.indicator
          (fun u => ENNReal.ofReal ((1 / θ) * (u : ℝ) ^ (-1 - 1 / θ))) u) ∂volIoi := by
  have hU : MeasurableSet {u : Ioi (0 : ℝ) | 1 < (u : ℝ)} :=
    measurableSet_lt measurable_const measurable_subtype_coe
  have hi := setLIntegral_excursionMeasure_eq_mixture hθ
    ((measurable_const : Measurable (fun _ : Excursion => (1 : ℝ≥0∞))).indicator hA)
    1 zero_le_one
  simp only [lintegral_indicator_fun_one hA] at hi
  rw [coe_tailExcursionLaw hθ, tailExcursionMeasure, Measure.smul_apply, smul_eq_mul,
    excursionTail, hi, ← lintegral_const_mul _
      (show Measurable (fun u : Ioi (0 : ℝ) => excursionAt θ u A * lifetimeDensity θ u) from
        (measurable_excursionAt_apply θ hA).mul (measurable_lifetimeDensity θ))]
  rw [← lintegral_indicator hU]
  apply lintegral_congr
  intro u
  by_cases hu : 1 < (u : ℝ)
  · simp only [indicator, mem_ofPred_eq, hu, ↓reduceIte]
    rw [mul_left_comm, gamma_mul_density hθ]
  · simp only [indicator, mem_ofPred_eq, hu, ↓reduceIte, mul_zero]

/-- **Tail path mixture** (C28), every horizon `T > 0` (zero continuation after `u` is built into
`excursionRestrict`): for measurable `B ⊆ D T ℝ`. -/
theorem tailLevyExcLaw_eq_mixture {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) (hT : 0 < T)
    {B : Set (D (T : ℝ) ℝ)} (hB : MeasurableSet B) :
    (tailLevyExcLaw θ T : Measure (D (T : ℝ) ℝ)) B =
      ∫⁻ u, excursionAt θ u (excursionRestrict T ⁻¹' B) *
        ({u : Set.Ioi (0 : ℝ) | 1 < (u : ℝ)}.indicator
          (fun u => ENNReal.ofReal ((1 / θ) * (u : ℝ) ^ (-1 - 1 / θ))) u) ∂volIoi := by
  -- `hT` is part of the stated interface; the identity also holds at horizon zero.
  have _hT := hT
  rw [tailLevyExcLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_excursionRestrict T) hB]
  exact tailExcursionLaw_eq_mixture hθ (hB.preimage (measurable_excursionRestrict T))

end BGW.StableTrees
