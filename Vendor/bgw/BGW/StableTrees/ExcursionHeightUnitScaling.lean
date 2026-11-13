/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightUnitVersion
public import BGW.StableTrees.ExcursionHeightScaling

public import BGW.Skorokhod.PathRegularity

/-!
# Unit height scaling

Continuity reduces the all-age scaling equality to countably many rational evaluations, so
the scaling events are jointly measurable. Fubini then supplies the version with a Lebesgue
distributed positive scale. The raw fixed-scale identity and the unit continuous version
determine a version of the scaled excursion, and the jointly measurable equality event
gives the product formulation.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The all-age scaling event is jointly Borel in the scale and excursion. -/
theorem measurableSet_excursionHeight_scale (θ : ℝ) :
    MeasurableSet {p : Ioi (0 : ℝ) × Excursion | ∀ t : ℝ≥0,
      excursionHeight θ (excursionScale θ p.1 p.2) ((p.1 : ℝ).toNNReal * t) =
        (p.1 : ℝ) ^ (1 - 1 / θ) * excursionHeight θ p.2 t} := by
  have heq (p : Ioi (0 : ℝ) × Excursion) := continuous_eq_iff_rat_toNNReal
    (f := fun t => excursionHeight θ (excursionScale θ p.1 p.2)
      ((p.1 : ℝ).toNNReal * t))
    (g := fun t => (p.1 : ℝ) ^ (1 - 1 / θ) * excursionHeight θ p.2 t)
    ((excursionHeight θ (excursionScale θ p.1 p.2)).continuous.comp
      (continuous_const.mul continuous_id))
    (continuous_const.mul (excursionHeight θ p.2).continuous)
  simp_rw [heq, ofPred_forall]
  apply MeasurableSet.iInter
  intro q
  have hL : Measurable (fun p : Ioi (0 : ℝ) × Excursion =>
      excursionHeight θ (excursionScale θ p.1 p.2)
        ((p.1 : ℝ).toNNReal * (q : ℝ).toNNReal)) :=
    Measurable.comp (g := fun r : ℝ≥0 × Excursion => excursionHeight θ r.2 r.1)
      (f := fun p : Ioi (0 : ℝ) × Excursion =>
        ((p.1 : ℝ).toNNReal * (q : ℝ).toNNReal, excursionScale θ p.1 p.2))
      (measurable_excursionHeight_uncurry θ)
      (((measurable_real_toNNReal.comp (measurable_subtype_coe.comp measurable_fst)).mul
        measurable_const).prodMk (measurable_excursionScale_joint θ))
  apply measurableSet_eq_fun hL
  exact ((measurable_subtype_coe.comp measurable_fst).pow_const _).mul
    (((ContinuousMap.measurable_eval _).comp (measurable_excursionHeight θ)).comp
      measurable_snd)

/-- **Scaling with a measurable parameter**: `(Lebesgue ⊗ N)`-a.e. in `(c, e)`. -/
theorem ae_prod_excursionHeight_scale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ p ∂(volIoi.prod (excursionMeasure θ)), ∀ t : ℝ≥0,
      excursionHeight θ (excursionScale θ p.1 p.2) ((p.1 : ℝ).toNNReal * t) =
        (p.1 : ℝ) ^ (1 - 1 / θ) * excursionHeight θ p.2 t := by
  let := sigmaFinite_excursionMeasure hθ
  apply (MeasureTheory.Measure.ae_prod_iff_ae_ae
    (measurableSet_excursionHeight_scale θ)).mpr
  exact ae_of_all _ (ae_excursionHeight_scale hθ)

/-- Scaling a continuous version gives a version when the raw scaling identity holds a.e. -/
theorem isExcursionHeightVersion_scale_of_ae (θ : ℝ) (c : Ioi (0 : ℝ)) (e : Excursion)
    (g : C(ℝ≥0, ℝ)) (hg : IsExcursionHeightVersion θ e g)
    (hr : ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) (e.lifetime : ℝ)),
      heightUniv θ (excursionScale θ c e).path ((c : ℝ).toNNReal * s.toNNReal) =
        (c : ℝ) ^ (1 - 1 / θ) * heightUniv θ e.path s.toNNReal) :
    IsExcursionHeightVersion θ (excursionScale θ c e)
      ⟨fun t => (c : ℝ) ^ (1 - 1 / θ) * g (t / (c : ℝ).toNNReal),
        continuous_const.mul (g.continuous.comp (continuous_id.div_const _))⟩ := by
  have hk : 0 < (c : ℝ).toNNReal := Real.toNNReal_pos.mpr c.2
  have ht : QuasiMeasurePreserving (fun s : ℝ => (c : ℝ)⁻¹ * s) volume volume := by
    refine ⟨measurable_const.mul measurable_id, ?_⟩
    rw [Real.map_volume_mul_left (inv_ne_zero c.2.ne')]
    exact Measure.smul_absolutelyContinuous
  have ht' : QuasiMeasurePreserving (fun s : ℝ => (c : ℝ)⁻¹ * s)
      (volume.restrict (Ioo (0 : ℝ) ((excursionScale θ c e).lifetime : ℝ)))
      (volume.restrict (Ioo (0 : ℝ) (e.lifetime : ℝ))) := by
    apply ht.restrict
    intro s hs
    refine ⟨mul_pos (inv_pos.mpr c.2) hs.1, ?_⟩
    rw [excursionScale_lifetime] at hs
    calc
      (c : ℝ)⁻¹ * s < (c : ℝ)⁻¹ * ((c : ℝ) * (e.lifetime : ℝ)) :=
        mul_lt_mul_of_pos_left hs.2 (inv_pos.mpr c.2)
      _ = e.lifetime := inv_mul_cancel_left₀ c.2.ne' _
  refine ⟨?_, ?_, ?_⟩
  · change (c : ℝ) ^ (1 - 1 / θ) * g (0 / (c : ℝ).toNNReal) = 0
    simp only [zero_div, hg.1, mul_zero]
  · intro t ht
    change (c : ℝ) ^ (1 - 1 / θ) * g (t / (c : ℝ).toNNReal) = 0
    rw [hg.2.1, mul_zero]
    apply (le_div_iff₀ hk).mpr
    change (c : ℝ).toNNReal * e.lifetime ≤ t at ht
    simpa only [mul_comm] using ht
  · filter_upwards [ht'.ae hg.2.2, ht'.ae hr] with s hs hh
    have hv : ((c : ℝ)⁻¹ * s).toNNReal = s.toNNReal / (c : ℝ).toNNReal := by
      rw [Real.toNNReal_mul (inv_nonneg.mpr c.2.le), Real.toNNReal_inv,
        div_eq_mul_inv, mul_comm]
    rw [hv] at hs hh
    have hks : (c : ℝ).toNNReal * (s.toNNReal / (c : ℝ).toNNReal) = s.toNNReal :=
      mul_div_cancel₀ _ hk.ne'
    rw [hks] at hh
    change (c : ℝ) ^ (1 - 1 / θ) * g (s.toNNReal / (c : ℝ).toNNReal) = _
    rw [hs]
    exact hh.symm

/-- **Scaling under the unit law**, for each fixed `c > 0` (not implied by the `N` version: the
unit law lives on the `N`-null set `{ζ = 1}`). -/
theorem ae_excursionHeight_scale_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (c : Set.Ioi (0 : ℝ)) :
    ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion), ∀ t : ℝ≥0,
      excursionHeight θ (excursionScale θ c e) ((c : ℝ).toNNReal * t) =
        (c : ℝ) ^ (1 - 1 / θ) * excursionHeight θ e t := by
  filter_upwards [ae_exists_isExcursionHeightVersion_unit hθ,
    ae_heightUniv_scale_unit_ages hθ c, ae_lifetime_unitExcursionLaw hθ] with e he hr hl
  have hr' : ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) (e.lifetime : ℝ)),
      heightUniv θ (excursionScale θ c e).path ((c : ℝ).toNNReal * s.toNNReal) =
        (c : ℝ) ^ (1 - 1 / θ) * heightUniv θ e.path s.toNNReal := by
    simpa only [hl, NNReal.coe_one] using hr
  have hv := isExcursionHeightVersion_scale_of_ae θ c e (excursionHeight θ e)
    (isExcursionHeightVersion_excursionHeight θ e he) hr'
  have heq := excursionHeight_eq_of_isExcursionHeightVersion θ (excursionScale θ c e) _ hv
  intro t
  rw [heq]
  change (c : ℝ) ^ (1 - 1 / θ) *
    excursionHeight θ e (((c : ℝ).toNNReal * t) / (c : ℝ).toNNReal) = _
  rw [mul_div_cancel_left₀ _ (Real.toNNReal_pos.mpr c.2).ne']

/-- **Scaling with a measurable parameter** under the unit law: `(Lebesgue ⊗ unit)`-a.e. in
`(c, e)` (a form J01's common-lifetime mixture can use). -/
theorem ae_prod_excursionHeight_scale_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ p ∂(volIoi.prod (unitExcursionLaw θ : Measure Excursion)), ∀ t : ℝ≥0,
      excursionHeight θ (excursionScale θ p.1 p.2) ((p.1 : ℝ).toNNReal * t) =
        (p.1 : ℝ) ^ (1 - 1 / θ) * excursionHeight θ p.2 t := by
  apply (MeasureTheory.Measure.ae_prod_iff_ae_ae
    (measurableSet_excursionHeight_scale θ)).mpr
  exact ae_of_all _ (ae_excursionHeight_scale_unit hθ)

end BGW.StableTrees
