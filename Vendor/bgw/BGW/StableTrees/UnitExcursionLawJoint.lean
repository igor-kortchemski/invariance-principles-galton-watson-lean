/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionLawRectangles
public import BGW.StableTrees.UnitExcursionLawLifetime
public import BGW.StableTrees.UnitExcursionLawJointTools

/-! # Lifetime and normalized shape form a product under the excursion measure

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem gamma_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    0 < Real.Gamma (1 - 1 / θ) :=
  Real.Gamma_pos_of_pos (sub_pos.mpr ((div_lt_one (by linarith)).mpr hθ.1))

private theorem measurableSet_tail (a : ℝ) :
    MeasurableSet {e : Excursion | a < (e.lifetime : ℝ)} :=
  measurableSet_lt measurable_const measurable_excursion_lifetime.coe_nnreal_real

private theorem lifetimeLaw_tail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : Ioi (0 : ℝ)) :
    lifetimeLaw θ (Ioi t) =
      ENNReal.ofReal ((t : ℝ) ^ (-(1 / θ)) / Real.Gamma (1 - 1 / θ)) := by
  rw [← map_lifetimePos_excursionMeasure hθ, Measure.map_apply
    (show Measurable Excursion.lifetimePos from
      Measurable.subtype_mk measurable_excursion_lifetime.coe_nnreal_real) measurableSet_Ioi]
  exact excursionMeasure_lifetime_tail hθ t t.2

private theorem gamma_mul_lifetimeLaw_tail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (t : Ioi (0 : ℝ)) :
    ENNReal.ofReal (Real.Gamma (1 - 1 / θ)) * lifetimeLaw θ (Ioi t) =
      ENNReal.ofReal ((t : ℝ) ^ (-(1 / θ))) := by
  rw [lifetimeLaw_tail hθ, ENNReal.ofReal_div_of_pos (gamma_pos hθ)]
  exact ENNReal.mul_div_cancel (ENNReal.ofReal_ne_zero_iff.mpr (gamma_pos hθ))
    ENNReal.ofReal_ne_top

private theorem shapeLifetime_preimage_rectangle (θ : ℝ) (t : Ioi (0 : ℝ))
    (A : Set Excursion) :
    shapeLifetime θ ⁻¹' (Ioi t ×ˢ A) =
      {e : Excursion | normalizeExc θ e ∈ A} ∩
        {e : Excursion | (t : ℝ) < (e.lifetime : ℝ)} := by
  ext e
  change (_ ∧ _) ↔ (_ ∧ _)
  exact and_comm

/-- **Threshold independence**: for every `a > 0`, the normalized restriction of `N` to
`{ζ > a}`, pushed by `normalizeExc`, is the unit law. -/
theorem normalize_tail_independent_of_threshold {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ)
    (ha : 0 < a) :
    (excursionMeasure θ {e : Excursion | a < (e.lifetime : ℝ)})⁻¹ •
        (excursionTail θ a).map (normalizeExc θ) =
      (unitExcursionLaw θ : Measure Excursion) := by
  ext A hA
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (measurable_normalizeExc θ) hA,
    excursionTail, Measure.restrict_apply (hA.preimage (measurable_normalizeExc θ))]
  change ((excursionMeasure θ) {e | a < (e.lifetime : ℝ)})⁻¹ *
    excursionMeasure θ ({e | normalizeExc θ e ∈ A} ∩ {e | a < (e.lifetime : ℝ)}) = _
  rw [excursionMeasure_shape_tail_rectangle hθ hA a ha,
    excursionMeasure_lifetime_tail hθ a ha, ← mul_assoc]
  rw [ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr
    (div_pos (Real.rpow_pos_of_pos ha _) (gamma_pos hθ))) ENNReal.ofReal_ne_top, one_mul]

/-- **Uniqueness of scaling-consistent families**: a measure `ν` with
`(S_c)_* ν = c^{1/θ} • ν` for all `c > 0` and `ν {ζ > 1} < ∞` is determined by its unit shape
measure `(normalizeExc)_* (ν ↾ {ζ > 1})`: `(ζ, normalizeExc)_* ν =
Γ(1-1/θ) • lifetimeLaw ⊗ (normalizeExc)_* (ν ↾ {ζ > 1})`. -/
theorem shapeLifetime_map_of_scaling {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ν : Measure Excursion)
    (hν : ∀ c : Set.Ioi (0 : ℝ),
      ν.map (excursionScale θ c) = ENNReal.ofReal ((c : ℝ) ^ (1 / θ)) • ν)
    (hfin : ν {e : Excursion | 1 < (e.lifetime : ℝ)} < ⊤) :
    ν.map (shapeLifetime θ) =
      ENNReal.ofReal (Real.Gamma (1 - 1 / θ)) • (lifetimeLaw θ).prod
        ((ν.restrict {e : Excursion | 1 < (e.lifetime : ℝ)}).map (normalizeExc θ)) := by
  let η := (ν.restrict {e : Excursion | 1 < (e.lifetime : ℝ)}).map (normalizeExc θ)
  have hfinite : IsFiniteMeasure (ν.restrict {e : Excursion | 1 < (e.lifetime : ℝ)}) :=
    isFiniteMeasure_restrict.mpr hfin.ne
  let := hfinite
  have htail (t : Ioi (0 : ℝ)) (A : Set Excursion) (hA : MeasurableSet A) :
      ν.map (shapeLifetime θ) (Ioi t ×ˢ A) =
        ENNReal.ofReal ((t : ℝ) ^ (-(1 / θ))) * η A := by
    rw [Measure.map_apply (measurable_shapeLifetime θ) (measurableSet_Ioi.prod hA),
      shapeLifetime_preimage_rectangle, shape_tail_of_scaling θ ν hν hA t t.2]
    congr 1
    dsimp only [η]
    rw [Measure.map_apply (measurable_normalizeExc θ) hA,
      Measure.restrict_apply (hA.preimage (measurable_normalizeExc θ))]
    rfl
  apply measure_eq_of_lifetime_tail_rectangles
  · intro t
    rw [htail t univ MeasurableSet.univ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top η univ)
  · intro t A hA
    rw [htail t A hA, Measure.smul_apply, smul_eq_mul, Measure.prod_prod,
      ← mul_assoc, gamma_mul_lifetimeLaw_tail hθ]

/-- **Joint identity**: `(ζ, normalizeExc)_* N = lifetimeLaw ⊗ unitExcursionLaw`. -/
theorem shapeLifetime_map_excursionMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (excursionMeasure θ).map (shapeLifetime θ) =
      (lifetimeLaw θ).prod (unitExcursionLaw θ : Measure Excursion) := by
  let : IsFiniteMeasure (excursionTail θ 1) := by
    unfold excursionTail
    exact isFiniteMeasure_restrict.mpr
      (excursionMeasure_lifetime_slab_lt_top hθ (by norm_num : (0 : ℝ≥0) < 1)).ne
  rw [shapeLifetime_map_of_scaling hθ (excursionMeasure θ)
    (map_excursionScale_excursionMeasure hθ)
    (excursionMeasure_lifetime_slab_lt_top hθ (by norm_num : (0 : ℝ≥0) < 1)),
    coe_unitExcursionLaw hθ, unitExcursionMeasure, Measure.prod_smul_right]
  rfl

/-- **Joint identity on tail rectangles**: for `a > 0`,
`(ζ, normalizeExc)_* (N ↾ {ζ > a}) = (lifetime law ↾ {u > a}) ⊗ unitExcursionLaw`. -/
theorem shapeLifetime_map_excursionTail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ) (ha : 0 < a) :
    (excursionTail θ a).map (shapeLifetime θ) =
      ((lifetimeLaw θ).restrict {u : Set.Ioi (0 : ℝ) | a < (u : ℝ)}).prod
        (unitExcursionLaw θ : Measure Excursion) := by
  -- `ha` is part of the stated interface; restriction commutes with the map for every `a`.
  have _ha := ha
  let := sigmaFinite_lifetimeLaw θ
  have heq : excursionTail θ a = (excursionMeasure θ).restrict
      (shapeLifetime θ ⁻¹' ({u : Ioi (0 : ℝ) | a < (u : ℝ)} ×ˢ univ)) := by
    unfold excursionTail
    congr 1
    ext e
    change (a < (e.lifetime : ℝ)) ↔ ((a < (e.lifetime : ℝ)) ∧ True)
    simp only [and_true]
  rw [heq, ← Measure.restrict_map (measurable_shapeLifetime θ)
    ((measurableSet_lt measurable_const measurable_subtype_coe).prod MeasurableSet.univ),
    shapeLifetime_map_excursionMeasure hθ, ← Measure.prod_restrict]
  simp only [Measure.restrict_univ]

/-- **Characterization of `N`**: a scaling-consistent `ν` with `ν {ζ > 1} < ∞` and the same
unit shape measure as `N` equals `N`. -/
theorem excursionMeasure_unique_of_scaling {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ν : Measure Excursion)
    (hν : ∀ c : Set.Ioi (0 : ℝ),
      ν.map (excursionScale θ c) = ENNReal.ofReal ((c : ℝ) ^ (1 / θ)) • ν)
    (hfin : ν {e : Excursion | 1 < (e.lifetime : ℝ)} < ⊤)
    (hshape : (ν.restrict {e : Excursion | 1 < (e.lifetime : ℝ)}).map (normalizeExc θ) =
      (excursionTail θ 1).map (normalizeExc θ)) :
    ν = excursionMeasure θ := by
  have hm : ν.map (shapeLifetime θ) = (excursionMeasure θ).map (shapeLifetime θ) := by
    rw [shapeLifetime_map_of_scaling hθ ν hν hfin, hshape,
      shapeLifetime_map_of_scaling hθ (excursionMeasure θ)
        (map_excursionScale_excursionMeasure hθ)
        (excursionMeasure_lifetime_slab_lt_top hθ (by norm_num : (0 : ℝ≥0) < 1))]
    rfl
  have h := congrArg (fun μ => μ.map (fromShapeLifetime θ)) hm
  simpa only [Measure.map_map (measurable_fromShapeLifetime θ) (measurable_shapeLifetime θ),
    show fromShapeLifetime θ ∘ shapeLifetime θ = id from
      funext (fromShapeLifetime_shapeLifetime θ), Measure.map_id] using h

end BGW.StableTrees
