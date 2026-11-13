/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionLawBasic

/-! # Scale invariance of normalized shapes and excursion tail rectangles

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Normalization removes every positive space-time scale. -/
theorem normalizeExc_excursionScale (θ : ℝ) (c : Ioi (0 : ℝ)) (e : Excursion) :
    normalizeExc θ (excursionScale θ c e) = normalizeExc θ e := by
  unfold normalizeExc
  rw [excursionScale_mul]
  congr 1
  apply Subtype.ext
  simp only [excursionScale_lifetime]
  field_simp [c.2.ne']

private theorem measurableSet_tail (a : ℝ) :
    MeasurableSet {e : Excursion | a < (e.lifetime : ℝ)} :=
  measurableSet_lt measurable_const measurable_excursion_lifetime.coe_nnreal_real

/-- Scaling alone determines shape-tail rectangle masses from threshold one. -/
theorem shape_tail_of_scaling (θ : ℝ) (ν : Measure Excursion)
    (hν : ∀ c : Ioi (0 : ℝ),
      ν.map (excursionScale θ c) = ENNReal.ofReal ((c : ℝ) ^ (1 / θ)) • ν)
    {A : Set Excursion} (hA : MeasurableSet A) (t : ℝ) (ht : 0 < t) :
    ν ({e : Excursion | normalizeExc θ e ∈ A} ∩
      {e : Excursion | t < (e.lifetime : ℝ)}) =
    ENNReal.ofReal (t ^ (-(1 / θ))) *
      ν ({e : Excursion | normalizeExc θ e ∈ A} ∩
        {e : Excursion | 1 < (e.lifetime : ℝ)}) := by
  let c : Ioi (0 : ℝ) := ⟨t⁻¹, inv_pos.mpr ht⟩
  have hm := congrArg (fun μ : Measure Excursion =>
    μ ({e : Excursion | normalizeExc θ e ∈ A} ∩
      {e : Excursion | 1 < (e.lifetime : ℝ)})) (hν c)
  rw [Measure.map_apply (measurable_excursionScale θ c)
    (show MeasurableSet ({e : Excursion | normalizeExc θ e ∈ A} ∩
      {e : Excursion | 1 < (e.lifetime : ℝ)}) from
      (hA.preimage (measurable_normalizeExc θ)).inter (measurableSet_tail 1)),
    Measure.smul_apply, smul_eq_mul] at hm
  have hpre : excursionScale θ c ⁻¹'
      ({e : Excursion | normalizeExc θ e ∈ A} ∩
        {e : Excursion | 1 < (e.lifetime : ℝ)}) =
      {e : Excursion | normalizeExc θ e ∈ A} ∩
        {e : Excursion | t < (e.lifetime : ℝ)} := by
    ext e
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq,
      normalizeExc_excursionScale, excursionScale_lifetime]
    change (_ ∧ 1 < t⁻¹ * (e.lifetime : ℝ)) ↔ (_ ∧ t < (e.lifetime : ℝ))
    rw [← div_eq_inv_mul, lt_div_iff₀ ht, one_mul]
  rw [hpre] at hm
  simpa only [c, Real.inv_rpow ht.le, Real.rpow_neg ht.le] using hm

/-- **Shape rectangles**: `N(normalizeExc ∈ A, ζ > t) = t^{-α} N(normalizeExc ∈ A, ζ > 1)
= (t^{-α}/Γ(1-α)) · unitExcursionLaw(A)`. -/
theorem excursionMeasure_shape_tail_rectangle {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {A : Set Excursion}
    (hA : MeasurableSet A) (t : ℝ) (ht : 0 < t) :
    excursionMeasure θ ({e : Excursion | normalizeExc θ e ∈ A} ∩
        {e : Excursion | t < (e.lifetime : ℝ)}) =
      ENNReal.ofReal (t ^ (-(1 / θ)) / Real.Gamma (1 - 1 / θ)) *
        (unitExcursionLaw θ : Measure Excursion) A := by
  rw [shape_tail_of_scaling θ (excursionMeasure θ)
    (map_excursionScale_excursionMeasure hθ) hA t ht, coe_unitExcursionLaw hθ,
    unitExcursionMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_normalizeExc θ) hA, excursionTail,
    Measure.restrict_apply (hA.preimage (measurable_normalizeExc θ))]
  rw [ENNReal.ofReal_div_of_pos
    (Real.Gamma_pos_of_pos (sub_pos.mpr ((div_lt_one (by linarith)).mpr hθ.1)))]
  have hG : ENNReal.ofReal (Real.Gamma (1 - 1 / θ)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr
      (Real.Gamma_pos_of_pos (sub_pos.mpr ((div_lt_one (by linarith)).mpr hθ.1)))
  change _ = _ / ENNReal.ofReal (Real.Gamma (1 - 1 / θ)) *
    (ENNReal.ofReal (Real.Gamma (1 - 1 / θ)) *
      excursionMeasure θ ({e | normalizeExc θ e ∈ A} ∩ {e | 1 < (e.lifetime : ℝ)}))
  rw [show ∀ x y : ℝ≥0∞, x / y = x * y⁻¹ from fun _ _ => div_eq_mul_inv _ _]
  calc
    _ = ENNReal.ofReal (t ^ (-(1 / θ))) *
        ((ENNReal.ofReal (Real.Gamma (1 - 1 / θ)))⁻¹ *
          ENNReal.ofReal (Real.Gamma (1 - 1 / θ))) *
        excursionMeasure θ ({e | normalizeExc θ e ∈ A} ∩ {e | 1 < (e.lifetime : ℝ)}) := by
      rw [ENNReal.inv_mul_cancel hG ENNReal.ofReal_ne_top, mul_one]
    _ = _ := by ac_rfl

end BGW.StableTrees
