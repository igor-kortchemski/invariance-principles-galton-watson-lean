/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightUnitRaw
import BGW.StableTrees.UnitExcursionLawMixture

/-!
# Continuous unit excursion height, including the terminal trace

The shape/lifetime product supplies one deterministic scale whose unit shapes have continuous
height versions. Raw scaling pulls that version back, including its zero at the lifetime.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- A version at a fixed scale pulls back whenever the raw heights obey the a.e.-age identity. -/
theorem exists_isExcursionHeightVersion_of_scale (θ : ℝ) (c : Ioi (0 : ℝ)) (e : Excursion)
    (hs : ∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ (excursionScale θ c e) g)
    (hr : ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) (e.lifetime : ℝ)),
      heightUniv θ (excursionScale θ c e).path ((c : ℝ).toNNReal * s.toNNReal) =
        (c : ℝ) ^ (1 - 1 / θ) * heightUniv θ e.path s.toNNReal) :
    ∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ e g := by
  obtain ⟨g, hg⟩ := hs
  let b : ℝ := (c : ℝ) ^ (1 - 1 / θ)
  have hb : b ≠ 0 := (Real.rpow_pos_of_pos c.2 _).ne'
  let G : C(ℝ≥0, ℝ) := ⟨fun t => b⁻¹ * g ((c : ℝ).toNNReal * t),
    continuous_const.mul (g.continuous.comp (continuous_const.mul continuous_id))⟩
  have ht : QuasiMeasurePreserving (fun s : ℝ => (c : ℝ) * s) volume volume := by
    refine ⟨measurable_const.mul measurable_id, ?_⟩
    rw [Real.map_volume_mul_left c.2.ne']
    exact Measure.smul_absolutelyContinuous
  have ht' : QuasiMeasurePreserving (fun s : ℝ => (c : ℝ) * s)
      (volume.restrict (Ioo (0 : ℝ) (e.lifetime : ℝ)))
      (volume.restrict (Ioo (0 : ℝ) ((excursionScale θ c e).lifetime : ℝ))) := by
    apply ht.restrict
    intro s hs
    rw [excursionScale_lifetime]
    exact ⟨mul_pos c.2 hs.1, mul_lt_mul_of_pos_left hs.2 c.2⟩
  have ha := ht'.ae hg.2.2
  refine ⟨G, ?_, ?_, ?_⟩
  · change b⁻¹ * g ((c : ℝ).toNNReal * 0) = 0
    simp only [mul_zero, hg.1]
  · intro t ht
    change b⁻¹ * g ((c : ℝ).toNNReal * t) = 0
    rw [hg.2.1 _ (show (c : ℝ).toNNReal * e.lifetime ≤ (c : ℝ).toNNReal * t from
      mul_le_mul_of_nonneg_left ht zero_le), mul_zero]
  · filter_upwards [ha, hr] with s hs hh
    change b⁻¹ * g ((c : ℝ).toNNReal * s.toNNReal) = _
    rw [Real.toNNReal_mul c.2.le] at hs
    rw [hs, hh, ← mul_assoc, inv_mul_cancel₀ hb, one_mul]

/-- The positive lifetime mixing measure is nonzero for a valid stable index. -/
theorem lifetimeLaw_ne_zero_of_height_index {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    lifetimeLaw θ ≠ 0 := by
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

/-- Under the unit excursion law (singular w.r.t. `N`) every excursion has an a.e.-age height
version, including the vanishing at the lifetime `1`. -/
theorem ae_exists_isExcursionHeightVersion_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
      ∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ e g := by
  let := sigmaFinite_lifetimeLaw θ
  let : NeZero (lifetimeLaw θ) := ⟨lifetimeLaw_ne_zero_of_height_index hθ⟩
  have hN : ∀ᵐ e ∂(((lifetimeLaw θ).prod (unitExcursionLaw θ : Measure Excursion)).map
      (fromShapeLifetime θ)), ∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ e g := by
    rw [map_fromShapeLifetime_product hθ]
    exact ae_exists_isExcursionHeightVersion hθ
  have hp := ae_of_ae_map (measurable_fromShapeLifetime θ).aemeasurable hN
  obtain ⟨c, hc⟩ := (MeasureTheory.Measure.ae_ae_of_ae_prod hp).exists
  filter_upwards [hc, ae_heightUniv_scale_unit_ages hθ c,
    ae_lifetime_unitExcursionLaw hθ] with e he hr hl
  apply exists_isExcursionHeightVersion_of_scale θ c e he
  simpa only [hl, NNReal.coe_one] using hr

/-- **Graph identity under the unit law**, simultaneously for all horizons `a < ζ` (`ζ = 1`
a.s.), with the same Borel map `heightPrefixAE θ a`. -/
theorem ae_heightPrefixAE_unitExcursionLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion), ∀ a : ℝ≥0, a < e.lifetime →
      ∀ t : Set.Icc (0 : ℝ) a,
        heightPrefixAE θ a (excursionRestrict a e) t = excursionHeight θ e ⟨t, t.2.1⟩ := by
  filter_upwards [ae_exists_isExcursionHeightVersion_unit hθ] with e he a ha t
  exact heightPrefixAE_excursionRestrict_of_exists θ e he ha t

end BGW.StableTrees
