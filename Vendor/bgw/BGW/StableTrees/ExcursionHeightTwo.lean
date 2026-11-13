/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightUnitScaling
import BGW.StableTrees.StableProcessBrownian

/-!
# The index-two excursion height

Brownian path continuity extends the fixed-time height formula on host paths. Excursion
locality and compensation identify the marks; the shape/lifetime law transfers the identity
to unit excursions with matching space and height exponents.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

private lemma height_continuousAt_of_restrict {f : DLoc} {t T : ℝ≥0} (htT : t < T)
    (h : ContinuousAt (DLoc.restrict T f)
      ⟨t, t.2, (show (t : ℝ) ≤ (T : ℝ) from htT.le)⟩) :
    ContinuousAt f.1 t := by
  let t' : Set.Icc (0 : ℝ) (T : ℝ) := ⟨t, t.2, htT.le⟩
  rw [Metric.continuousAt_iff] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := h ε hε
  refine ⟨min δ ((T : ℝ) - (t : ℝ)), lt_min hδ (sub_pos.mpr htT), ?_⟩
  intro u hu
  have huδ : dist u t < δ := hu.trans_le (min_le_left _ _)
  have huTdist : dist u t < (T : ℝ) - (t : ℝ) := hu.trans_le (min_le_right _ _)
  have huT : u < T := by
    have hu_abs : |(u : ℝ) - (t : ℝ)| < (T : ℝ) - (t : ℝ) := by
      simpa only [NNReal.dist_eq, Real.dist_eq] using huTdist
    have huT' : (u : ℝ) < (T : ℝ) := by
      have hh := (abs_lt.mp hu_abs).2
      linarith
    exact_mod_cast huT'
  let u' : Set.Icc (0 : ℝ) (T : ℝ) := ⟨u, u.2, huT.le⟩
  have hu' : dist u' t' < δ := by
    simpa [u', t', Subtype.dist_eq, NNReal.dist_eq, Real.dist_eq] using huδ
  exact hδf hu'

private lemma height_ae_continuous_restrict_two {T : ℝ≥0} (hT : 0 < T) :
    ∀ᵐ f ∂(stableLocalLaw 2 : Measure DLoc), Continuous (DLoc.restrict T f) := by
  have hθ : 1 < (2 : ℝ) ∧ (2 : ℝ) ≤ 2 := by norm_num
  have h := ae_mem_range_ofContinuous_stableProcessLaw_two (show 0 < (T : ℝ) from hT)
  rw [← map_restrict_stableLocalLaw hθ (by exact_mod_cast hT)] at h
  have h' := ae_of_ae_map (DLoc.measurable_restrict T).aemeasurable h
  filter_upwards [h'] with f hf
  obtain ⟨g, hg⟩ := hf
  rw [← hg]
  exact g.continuous

private lemma height_ae_continuous_two :
    ∀ᵐ f ∂(stableLocalLaw 2 : Measure DLoc), Continuous f.1 := by
  have hrestrict : ∀ n : ℕ, ∀ᵐ f ∂(stableLocalLaw 2 : Measure DLoc),
      Continuous (DLoc.restrict ((n : ℝ≥0) + 1) f) := by
    intro n
    exact height_ae_continuous_restrict_two (by positivity)
  filter_upwards [ae_all_iff.mpr hrestrict] with f hf
  rw [continuous_iff_continuousAt]
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
  have ht : t < (n : ℝ≥0) + 1 := by
    have hnt : t < (n : ℝ≥0) := by exact_mod_cast hn
    exact hnt.trans_le (le_add_right le_rfl)
  exact height_continuousAt_of_restrict ht (hf n).continuousAt

/-- **C26 (K17).**  At `θ = 2`, almost surely, the continuous height is `X - I` at every time. -/
theorem ae_heightLoc_two_for_excursion :
    ∀ᵐ f ∂(stableLocalLaw 2 : Measure DLoc), ∀ t : ℝ≥0,
      heightLoc 2 f t = f.1 t - runningInfLoc f t := by
  have hθ : 1 < (2 : ℝ) ∧ (2 : ℝ) ≤ 2 := by norm_num
  have hrat : ∀ q : ℚ, ∀ᵐ f ∂(stableLocalLaw 2 : Measure DLoc),
      heightLoc 2 f (q : ℝ).toNNReal =
        f.1 (q : ℝ).toNNReal - runningInfLoc f (q : ℝ).toNNReal := by
    intro q
    filter_upwards [ae_heightLoc_eq_height hθ (q : ℝ).toNNReal,
      ae_height_two (q : ℝ).toNNReal] with f hloc hh
    rw [hloc, hh, futureInf_zero_eq_runningInf]
  filter_upwards [ae_all_iff.mpr hrat, height_ae_continuous_two] with f hqf hf
  have hI : Continuous (runningInfLoc f) := by
    apply runningInfLoc_continuous
    intro t
    exact (hf.continuousAt.continuousWithinAt.leftLim_eq).le
  have heq : heightLoc 2 f = fun t => f.1 t - runningInfLoc f t := by
    apply Continuous.ext_on dense_isRationalTime (continuous_heightLoc 2 f) (hf.sub hI)
    intro t ht
    obtain ⟨q, hq⟩ := ht
    have hqt : (q : ℝ).toNNReal = t := by
      have hq0 : 0 ≤ (q : ℝ) := t.2.trans hq.ge
      apply NNReal.coe_injective
      rw [Real.coe_toNNReal _ hq0]
      exact hq
    rw [← hqt]
    exact hqf q
  exact congrFun heq


/-- A continuous function and a càdlàg path agree everywhere iff they agree at rational ages. -/
theorem continuous_eq_dLoc_iff_rat (g : C(ℝ≥0, ℝ)) (f : DLoc) :
    (∀ t, g t = f.1 t) ↔ ∀ q : ℚ, g (q : ℝ).toNNReal = f.1 (q : ℝ).toNNReal := by
  refine ⟨fun h q => h _, fun h t => ?_⟩
  obtain ⟨u, _, hu, hlim⟩ := dense_isRationalTime.exists_seq_strictAnti_tendsto t
  have hw : Tendsto u atTop (𝓝[>] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun n => (hu n).1⟩
  have he (n : ℕ) : g (u n) = f.1 (u n) := by
    obtain ⟨q, hq⟩ := (hu n).2
    simpa only [hq, Real.toNNReal_coe] using h q
  exact tendsto_nhds_unique (g.continuous.continuousAt.tendsto.comp hlim)
    (((f.2.isRightContinuous t).tendsto.comp hw).congr (fun n => (he n).symm))

/-- The all-age equality of the continuous height with the excursion path is Borel. -/
theorem measurableSet_excursionHeight_eq_path (θ : ℝ) :
    MeasurableSet {e : Excursion | ∀ t : ℝ≥0, excursionHeight θ e t = e.path.1 t} := by
  simp_rw [continuous_eq_dLoc_iff_rat, ofPred_forall]
  apply MeasurableSet.iInter
  intro q
  exact measurableSet_eq_fun
    ((ContinuousMap.measurable_eval _).comp (measurable_excursionHeight θ))
    (measurable_excursion_eval _)

/-- At `θ = 2` (variance-2 library process, `H = X - I`) the excursion height is the excursion
path, `N`-a.e. -/
theorem ae_excursionHeight_two :
    ∀ᵐ e ∂(excursionMeasure 2), ∀ t : ℝ≥0, excursionHeight 2 e t = e.path.1 t := by
  have hθ : 1 < (2 : ℝ) ∧ (2 : ℝ) ≤ 2 := by norm_num
  apply ae_excursionMeasure_of_ae_jumpExcursion hθ
    (measurableSet_excursionHeight_eq_path 2)
  filter_upwards [ae_heightLoc_two_for_excursion, ae_heightLoc_jumpExcursion hθ,
    ae_jumpExcursion_spec hθ, ae_eval_zero_stableLocalLaw hθ] with f hh hl hs h0
  intro x hx t
  obtain ⟨hcut, hζ, he⟩ := hs x hx
  by_cases ht : t ≤ passageTime x f - passageTimeMinus x f
  · rw [← hl x hx t ht, hh, he,
      min_eq_left (show passageTimeMinus x f + t ≤ passageTime x f from by
        simpa only [add_comm] using (le_tsub_iff_right hcut.1.le).mp ht)]
    exact (reflectedFrom_zero_apply h0 _).symm
  · have hzt : (jumpExcursion x f).lifetime ≤ t := by rw [hζ]; exact (not_le.mp ht).le
    rw [excursionHeight_eq_zero_of_lifetime_le 2 _ hzt]
    exact ((jumpExcursion x f).2.2.2 t hzt).symm

/-- At `θ = 2` the excursion height is the excursion path under the unit law (K18). -/
theorem ae_excursionHeight_two_unit :
    ∀ᵐ e ∂(unitExcursionLaw 2 : Measure Excursion), ∀ t : ℝ≥0,
      excursionHeight 2 e t = e.path.1 t := by
  have hθ : 1 < (2 : ℝ) ∧ (2 : ℝ) ≤ 2 := by norm_num
  let : NeZero (lifetimeLaw 2) := ⟨lifetimeLaw_ne_zero_of_height_index hθ⟩
  have hp : ∀ᵐ p ∂((lifetimeLaw 2).prod (unitExcursionLaw 2 : Measure Excursion)),
      ∀ t : ℝ≥0, excursionHeight 2 (excursionScale 2 p.1 p.2) t =
        (excursionScale 2 p.1 p.2).path.1 t := by
    have ha : ∀ᵐ e ∂(((lifetimeLaw 2).prod (unitExcursionLaw 2 : Measure Excursion)).map
        (fromShapeLifetime 2)), ∀ t : ℝ≥0, excursionHeight 2 e t = e.path.1 t := by
      rw [map_fromShapeLifetime_product hθ]
      exact ae_excursionHeight_two
    exact ae_of_ae_map (measurable_fromShapeLifetime 2).aemeasurable ha
  obtain ⟨c, hc⟩ := (MeasureTheory.Measure.ae_ae_of_ae_prod hp).exists
  filter_upwards [hc, ae_excursionHeight_scale_unit hθ c] with e he hs t
  have ht := he ((c : ℝ).toNNReal * t)
  rw [hs t] at ht
  change (c : ℝ) ^ (1 - 1 / (2 : ℝ)) * excursionHeight 2 e t =
    (c : ℝ) ^ (1 / (2 : ℝ)) * e.path.1 (((c : ℝ).toNNReal * t) /
      (c : ℝ).toNNReal) at ht
  rw [mul_div_cancel_left₀ _ (Real.toNNReal_pos.mpr c.2).ne'] at ht
  have hexp : 1 - 1 / (2 : ℝ) = 1 / 2 := by norm_num
  rw [hexp] at ht
  exact mul_left_cancel₀ (Real.rpow_pos_of_pos c.2 (1 / 2)).ne' ht

end BGW.StableTrees
