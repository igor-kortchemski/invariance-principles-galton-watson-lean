/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightScaling

/-!
# Identification at every positive real age

A surviving-age window supplies a good deterministic age. Dilation of its finite survival
measure transports the full-filter approximation limit to each prescribed positive age.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- Fixed-age excursion occupation approximations are measurable. -/
theorem measurable_excursion_heightApprox (ε : ℝ) (t : ℝ≥0) :
    Measurable (fun e : Excursion => heightApprox ε e.path t) :=
  measurable_heightApprox_uncurry.comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_excursion_path))

/-- At least one deterministic positive age identifies the continuous excursion height. -/
theorem exists_age_heightApprox_tendstoInMeasure_excursionHeight {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ t : ℝ≥0, 0 < t ∧ TendstoInMeasure
      ((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime})
      (fun (ε : ℝ) e => heightApprox ε e.path t) (𝓝[>] (0 : ℝ))
      (fun e => excursionHeight θ e t) := by
  let := sigmaFinite_excursionMeasure hθ
  have hm : MeasurableSet {p : ℝ × Excursion | p.1.toNNReal < p.2.lifetime →
      Tendsto (fun n : ℕ => heightApprox (heightEps θ n) p.2.path p.1.toNNReal) atTop
        (𝓝 (excursionHeight θ p.2 p.1.toNNReal))} := by
    convert measurableSet_heightExcursionAge_survival.compl.union
      (measurableSet_tendsto_fun (l := (atTop : Filter ℕ))
        (fun n => measurable_heightApprox_age_excursion (heightEps θ n))
        (measurable_excursionHeight_real_age θ)) using 1
    ext p
    exact imp_iff_not_or
  have hages : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) 1),
      ∀ᵐ e ∂excursionMeasure θ, s.toNNReal < e.lifetime →
        Tendsto (fun n : ℕ => heightApprox (heightEps θ n) e.path s.toNNReal) atTop
          (𝓝 (excursionHeight θ e s.toNNReal)) := by
    apply (MeasureTheory.Measure.ae_prod_iff_ae_ae hm).mp
    exact (ae_restrict_iff' measurableSet_heightExcursionAge_survival).mp
      (ae_tendsto_excursionHeight_ages hθ 1)
  have : NeZero (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by
    intro hz
    have hh := congrArg (fun μ : Measure ℝ => μ univ) hz
    norm_num [Measure.restrict_apply_univ, Real.volume_Ioo] at hh⟩
  obtain ⟨s, hs, hseq⟩ := (hages.and (ae_restrict_mem measurableSet_Ioo)).exists
  have ht : 0 < s.toNNReal := Real.toNNReal_pos.mpr hseq.1
  refine ⟨s.toNNReal, ht, ?_⟩
  let μ := (excursionMeasure θ).restrict {e : Excursion | s.toNNReal < e.lifetime}
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (excursionMeasure_lifetime_slab_lt_top hθ ht).ne
  have ha : ∀ᵐ e ∂μ,
      Tendsto (fun n : ℕ => heightApprox (heightEps θ n) e.path s.toNNReal) atTop
        (𝓝 (excursionHeight θ e s.toNNReal)) :=
    (ae_restrict_iff'
      (measurableSet_lt measurable_const measurable_excursion_lifetime)).mpr hs
  obtain ⟨L, _, hL⟩ := exists_heightApprox_tendstoInMeasure_excursion hθ s.toNNReal ht
  have hM := tendstoInMeasure_of_tendsto_ae
    (fun n =>
      (measurable_excursion_heightApprox (heightEps θ n) s.toNNReal).aestronglyMeasurable) ha
  exact TendstoInMeasure.congr_right
    (tendstoInMeasure_ae_unique (hL.comp (heightEps_tendsto_nhdsWithin_zero θ)) hM) hL

/-- Scaling carries a survival restriction to the scaled restriction, with the usual mass factor. -/
theorem map_excursionScale_survival {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (c : Ioi (0 : ℝ)) (t : ℝ≥0) :
    ((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime}).map
      (excursionScale θ c) = ENNReal.ofReal ((c : ℝ) ^ (1 / θ)) •
        (excursionMeasure θ).restrict
          {e : Excursion | (c : ℝ).toNNReal * t < e.lifetime} := by
  have hp : (excursionScale θ c) ⁻¹'
      {e : Excursion | (c : ℝ).toNNReal * t < e.lifetime} =
      {e : Excursion | t < e.lifetime} := by
    ext e
    change (c : ℝ).toNNReal * t < (c : ℝ).toNNReal * e.lifetime ↔ t < e.lifetime
    exact mul_lt_mul_iff_right₀ (Real.toNNReal_pos.mpr c.2)
  rw [← hp, ← Measure.restrict_map (measurable_excursionScale θ c)
    (measurableSet_lt measurable_const measurable_excursion_lifetime),
    map_excursionScale_excursionMeasure hθ c, Measure.restrict_smul]

/-- Good ages for full-filter continuous-height identification are preserved by dilation. -/
theorem heightApprox_tendstoInMeasure_excursionHeight_dilate {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (c : Ioi (0 : ℝ)) (t : ℝ≥0) (ht : 0 < t)
    (hgood : TendstoInMeasure
      ((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime})
      (fun (ε : ℝ) e => heightApprox ε e.path t) (𝓝[>] (0 : ℝ))
      (fun e => excursionHeight θ e t)) :
    TendstoInMeasure
      ((excursionMeasure θ).restrict
        {e : Excursion | (c : ℝ).toNNReal * t < e.lifetime})
      (fun (ε : ℝ) e => heightApprox ε e.path ((c : ℝ).toNNReal * t))
      (𝓝[>] (0 : ℝ)) (fun e => excursionHeight θ e ((c : ℝ).toNNReal * t)) := by
  let μ := (excursionMeasure θ).restrict {e : Excursion | t < e.lifetime}
  let ν := (excursionMeasure θ).restrict
    {e : Excursion | (c : ℝ).toNNReal * t < e.lifetime}
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (excursionMeasure_lifetime_slab_lt_top hθ ht).ne
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr
    (excursionMeasure_lifetime_slab_lt_top hθ
      (mul_pos (Real.toNNReal_pos.mpr c.2) ht)).ne
  have ha := Real.rpow_pos_of_pos c.2 (1 / θ)
  have hcut : Tendsto (fun ε : ℝ => ε / (c : ℝ) ^ (1 / θ))
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [id_eq, zero_div] using
        (tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 (0 : ℝ)) (𝓝 0)).div_const
          ((c : ℝ) ^ (1 / θ)) |>.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact div_pos hε ha
  have hM := tendstoInMeasure_continuous_comp_filter
    (fun ε => measurable_excursion_heightApprox (ε / (c : ℝ) ^ (1 / θ)) t)
    (hgood.comp hcut)
    (show Continuous (fun y : ℝ => (c : ℝ) ^ (1 - 1 / θ) * y) from
      continuous_const.mul continuous_id)
  have hleft (ε : ℝ) :
      (fun e : Excursion => (c : ℝ) ^ (1 - 1 / θ) *
        heightApprox (ε / (c : ℝ) ^ (1 / θ)) e.path t) =ᵐ[μ]
      (fun e => heightApprox ε (excursionScale θ c e).path ((c : ℝ).toNNReal * t)) :=
    ae_of_all _ fun e => (heightApprox_scaleLoc θ c e.path t ε).symm
  have hright : (fun e => (c : ℝ) ^ (1 - 1 / θ) * excursionHeight θ e t) =ᵐ[μ]
      (fun e => excursionHeight θ (excursionScale θ c e) ((c : ℝ).toNNReal * t)) :=
    (ae_restrict_of_ae (ae_excursionHeight_scale hθ c)).mono fun e he => (he t).symm
  have hmap := (tendstoInMeasure_map_iff (measurable_excursionScale θ c)
    (fun ε => measurable_excursion_heightApprox ε ((c : ℝ).toNNReal * t))
    ((ContinuousMap.measurable_eval _).comp (measurable_excursionHeight θ))).mpr
      (hM.congr hleft hright)
  rw [map_excursionScale_survival hθ c t] at hmap
  exact tendstoInMeasure_of_absolutelyContinuous
    (Measure.AbsolutelyContinuous.rfl.smul_right (ENNReal.ofReal_ne_zero_iff.mpr ha))
    (fun ε => measurable_excursion_heightApprox ε ((c : ℝ).toNNReal * t)) hmap

/-- **Identification under `N`**: for each fixed age `t > 0`, on `{t < ζ}` the approximations
converge in `N`-measure to the excursion height. -/
theorem heightApprox_tendstoInMeasure_excursionHeight {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0)
    (ht : 0 < t) :
    TendstoInMeasure ((excursionMeasure θ).restrict {e : Excursion | t < e.lifetime})
      (fun (ε : ℝ) (e : Excursion) => heightApprox ε e.path t) (𝓝[>] (0 : ℝ))
      (fun e => excursionHeight θ e t) := by
  obtain ⟨s, hs, hgood⟩ := exists_age_heightApprox_tendstoInMeasure_excursionHeight hθ
  let c : Ioi (0 : ℝ) := ⟨(t : ℝ) / (s : ℝ), div_pos ht hs⟩
  have hc : (c : ℝ).toNNReal * s = t := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, Real.coe_toNNReal _ c.2.le]
    exact div_mul_cancel₀ _ (ne_of_gt (show (0 : ℝ) < s from hs))
  simpa only [hc] using
    heightApprox_tendstoInMeasure_excursionHeight_dilate hθ c s hs hgood

end BGW.StableTrees
