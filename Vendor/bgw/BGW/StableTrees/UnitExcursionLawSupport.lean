/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionLawMixture

/-! # Positivity and endpoint support of the normalized excursion laws

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Tail support**: under `N(· | ζ > 1)`, almost surely the lifetime exceeds `1`, the path is
positive on `(0, ζ)`, the tag is the actual lifetime and the terminal left limit is `0`. -/
theorem ae_tailExcursionLaw_support {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(tailExcursionLaw θ : Measure Excursion),
      1 < e.lifetime ∧
      (∀ t : ℝ≥0, 0 < t → t < e.lifetime → 0 < e.path.1 t) ∧
      e.lifetime = sSup {t : ℝ≥0 | 0 < e.path.1 t} ∧
      Function.leftLim e.path.1 e.lifetime = 0 := by
  rw [coe_tailExcursionLaw hθ, tailExcursionMeasure]
  apply Measure.ae_smul_measure
  have hs := ae_restrict_of_ae
    (s := {e : Excursion | 1 < (e.lifetime : ℝ)}) (ae_excursionMeasure_support hθ)
  filter_upwards [hs, ae_restrict_mem
    (measurableSet_lt measurable_const measurable_excursion_lifetime.coe_nnreal_real)] with e he ht
  refine ⟨by exact_mod_cast ht, he.1, he.2.1, ?_⟩
  let : NeBot (𝓝[<] e.lifetime) := nhdsLT_neBot_of_exists_lt ⟨0, e.lifetime_pos⟩
  exact leftLim_eq_of_tendsto he.2.2.2.2

private theorem unit_support_of_scaled (θ : ℝ) (u : Ioi (0 : ℝ)) (e : Excursion)
    (he : e.lifetime = 1)
    (hp : ∀ t : ℝ≥0, 0 < t → t < (excursionScale θ u e).lifetime →
      0 < (excursionScale θ u e).path.1 t)
    (hl : Tendsto (excursionScale θ u e).path.1
      (𝓝[<] (excursionScale θ u e).lifetime) (𝓝 0)) :
    e.path.1 0 = 0 ∧ (∀ t : ℝ≥0, 0 < t → t < 1 → 0 < e.path.1 t) ∧
      Function.leftLim e.path.1 1 = 0 := by
  let c := (u : ℝ).toNNReal
  have hc : 0 < c := Real.toNNReal_pos.mpr u.2
  have hζ : (excursionScale θ u e).lifetime = c := by
    apply NNReal.eq
    rw [excursionScale_lifetime, he]
    simp [c, Real.coe_toNNReal _ u.2.le]
  have hscalar : 0 < (u : ℝ) ^ (1 / θ) := Real.rpow_pos_of_pos u.2 _
  have hval (t : ℝ≥0) : (excursionScale θ u e).path.1 (c * t) =
      (u : ℝ) ^ (1 / θ) * e.path.1 t := by
    change (u : ℝ) ^ (1 / θ) * e.path.1 ((c * t) / c) = _
    rw [mul_div_cancel_left₀ _ hc.ne']
  refine ⟨e.2.1, ?_, ?_⟩
  · intro t ht htl
    have hh := hp (c * t) (mul_pos hc ht) (by rw [hζ]; simpa using mul_lt_mul_of_pos_left htl hc)
    rw [hval] at hh
    exact (mul_pos_iff_of_pos_left hscalar).mp hh
  · let : NeBot (𝓝[<] (1 : ℝ≥0)) := nhdsLT_neBot_of_exists_lt ⟨0, zero_lt_one⟩
    apply leftLim_eq_of_tendsto
    have hmap : Tendsto (fun t : ℝ≥0 => c * t) (𝓝[<] 1) (𝓝[<] c) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · have hcont : Continuous (fun t : ℝ≥0 => c * t) :=
          continuous_const.mul continuous_id
        simpa only [mul_one] using
          (hcont.continuousAt (x := (1 : ℝ≥0))).mono_left
            (nhdsWithin_le_nhds (s := Iio (1 : ℝ≥0)))
      · filter_upwards [self_mem_nhdsWithin] with t ht
        calc c * t < c * 1 := mul_lt_mul_of_pos_left ht hc
             _ = c := mul_one c
    rw [hζ] at hl
    have hh := (hl.comp hmap).const_mul ((u : ℝ) ^ (1 / θ))⁻¹
    simpa only [Function.comp_def, hval, ← mul_assoc, inv_mul_cancel₀ hscalar.ne',
      one_mul, mul_zero] using hh

/-- Endpoints and positivity at the level of `Excursion`: the same properties for
`unitExcursionLaw`, in terms of the path on `ℝ≥0`. -/
theorem ae_unitExcursionLaw_positive {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
      e.path.1 0 = 0 ∧ (∀ t : ℝ≥0, 0 < t → t < 1 → 0 < e.path.1 t) ∧
      Function.leftLim e.path.1 1 = 0 := by
  have hp := ae_of_ae_map (measurable_fromShapeLifetime θ).aemeasurable
    (show ∀ᵐ e ∂(((lifetimeLaw θ).prod (unitExcursionLaw θ : Measure Excursion)).map
        (fromShapeLifetime θ)),
      (∀ t : ℝ≥0, 0 < t → t < e.lifetime → 0 < e.path.1 t) ∧
        e.lifetime = sSup {t : ℝ≥0 | 0 < e.path.1 t} ∧
        e.path.1 0 = 0 ∧ ContinuousAt e.path.1 0 ∧
        Tendsto e.path.1 (𝓝[<] e.lifetime) (𝓝 0) from by
      rw [map_fromShapeLifetime_product hθ]
      exact ae_excursionMeasure_support hθ)
  have hne : lifetimeLaw θ ≠ 0 := by
    intro hz
    have hm := congrArg (fun μ : Measure (Ioi (0 : ℝ)) => μ (Ioi ⟨1, one_pos⟩))
      (map_lifetimePos_excursionMeasure hθ)
    rw [hz, Measure.map_apply
      measurable_lifetimePos
      measurableSet_Ioi] at hm
    simp only [Measure.coe_zero, Pi.zero_apply] at hm
    change excursionMeasure θ {e : Excursion | 1 < (e.lifetime : ℝ)} = 0 at hm
    have hg : 0 < Real.Gamma (1 - 1 / θ) :=
      Real.Gamma_pos_of_pos (sub_pos.mpr ((div_lt_one (by linarith)).mpr hθ.1))
    have hmass := excursionMeasure_lifetime_gt_one hθ
    rw [hm] at hmass
    exact (ENNReal.ofReal_ne_zero_iff.mpr (one_div_pos.mpr hg)) hmass.symm
  let : NeZero (lifetimeLaw θ) := ⟨hne⟩
  obtain ⟨u, hu⟩ := (Measure.ae_ae_of_ae_prod hp).exists
  filter_upwards [hu, ae_lifetime_unitExcursionLaw hθ] with e he hl
  exact unit_support_of_scaled θ u e hl he.1 he.2.2.2.2

end BGW.StableTrees
