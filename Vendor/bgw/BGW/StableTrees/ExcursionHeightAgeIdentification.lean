/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightExcursionMeasure
import BGW.StableTrees.HeightBridgesAgeLaws
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Identification on surviving excursion age windows

The non-junk a.e.-age clause identifies the universal subsequence limit on each finite
surviving-age measure. Uniqueness then identifies the full approximation filter there.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Joint real-age evaluation of the continuous excursion height is measurable. -/
theorem measurable_excursionHeight_real_age (θ : ℝ) :
    Measurable (fun p : ℝ × Excursion => excursionHeight θ p.2 p.1.toNNReal) :=
  Measurable.comp (g := fun p : ℝ≥0 × Excursion => excursionHeight θ p.2 p.1)
    (f := fun p : ℝ × Excursion => (p.1.toNNReal, p.2))
    (measurable_excursionHeight_uncurry θ)
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)

/-- Joint real-age evaluation of the universal excursion height is measurable. -/
theorem measurable_heightUniv_excursion_real_age (θ : ℝ) :
    Measurable (fun p : ℝ × Excursion => heightUniv θ p.2.path p.1.toNNReal) :=
  Measurable.comp (g := fun p : ℝ≥0 × DLoc => heightUniv θ p.2 p.1)
    (f := fun p : ℝ × Excursion => (p.1.toNNReal, p.2.path))
    (measurable_heightUniv_uncurry θ)
    ((measurable_real_toNNReal.comp measurable_fst).prodMk
      (measurable_excursion_path.comp measurable_snd))

/-- The universal height agrees with the continuous version on surviving age windows. -/
theorem ae_heightUniv_eq_excursionHeight_ages {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (S : ℝ≥0) :
    ∀ᵐ p ∂heightExcursionAgeMeasure θ S,
      heightUniv θ p.2.path p.1.toNNReal = excursionHeight θ p.2 p.1.toNNReal := by
  let := sigmaFinite_excursionMeasure hθ
  have hm : MeasurableSet {p : ℝ × Excursion | p.1.toNNReal < p.2.lifetime →
      heightUniv θ p.2.path p.1.toNNReal = excursionHeight θ p.2 p.1.toNNReal} := by
    convert measurableSet_heightExcursionAge_survival.compl.union
      (measurableSet_eq_fun (measurable_heightUniv_excursion_real_age θ)
        (measurable_excursionHeight_real_age θ)) using 1
    ext p
    exact imp_iff_not_or
  rw [heightExcursionAgeMeasure]
  apply (ae_restrict_iff' measurableSet_heightExcursionAge_survival).mpr
  apply (MeasureTheory.Measure.ae_prod_iff_ae_ae hm).mpr
  apply (MeasureTheory.Measure.ae_ae_comm hm).mpr
  filter_upwards [ae_exists_isExcursionHeightVersion hθ] with e he
  have hh := (ae_restrict_iff' measurableSet_Ioo).mp
    (isExcursionHeightVersion_excursionHeight θ e he).2.2
  filter_upwards [ae_restrict_of_ae hh, ae_restrict_mem measurableSet_Ioo] with s hs hmem hsurv
  apply (hs ⟨hmem.1, ?_⟩).symm
  have hsreal : (s.toNNReal : ℝ) = s := Real.coe_toNNReal _ hmem.1.le
  have hlt : (s.toNNReal : ℝ) < e.lifetime := hsurv
  rwa [hsreal] at hlt

/-- Universal cutoffs converge to the continuous version on surviving age windows. -/
theorem ae_tendsto_excursionHeight_ages {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (S : ℝ≥0) :
    ∀ᵐ p ∂heightExcursionAgeMeasure θ S,
      Tendsto (fun k => heightApprox (heightEps θ k) p.2.path p.1.toNNReal) atTop
        (𝓝 (excursionHeight θ p.2 p.1.toNNReal)) := by
  let := sigmaFinite_excursionMeasure hθ
  have hconv : MeasurableSet {p : ℝ × Excursion |
      Tendsto (fun k => heightApprox (heightEps θ k) p.2.path p.1.toNNReal) atTop
        (𝓝 (heightUniv θ p.2.path p.1.toNNReal))} :=
    measurableSet_tendsto_fun (fun k => measurable_heightApprox_age_excursion (heightEps θ k))
      (measurable_heightUniv_excursion_real_age θ)
  have himp : MeasurableSet {p : ℝ × Excursion | p.1.toNNReal < p.2.lifetime →
      Tendsto (fun k => heightApprox (heightEps θ k) p.2.path p.1.toNNReal) atTop
        (𝓝 (heightUniv θ p.2.path p.1.toNNReal))} := by
    convert measurableSet_heightExcursionAge_survival.compl.union hconv using 1
    ext p
    exact imp_iff_not_or
  have hraw : ∀ᵐ p ∂heightExcursionAgeMeasure θ S,
      Tendsto (fun k => heightApprox (heightEps θ k) p.2.path p.1.toNNReal) atTop
        (𝓝 (heightUniv θ p.2.path p.1.toNNReal)) := by
    rw [heightExcursionAgeMeasure]
    apply (ae_restrict_iff' measurableSet_heightExcursionAge_survival).mpr
    apply (MeasureTheory.Measure.ae_prod_iff_ae_ae himp).mpr
    filter_upwards [ae_age_tendsto_heightUniv_excursion hθ S] with s hs
    exact (ae_restrict_iff'
      (measurableSet_lt measurable_const measurable_excursion_lifetime)).mp hs
  filter_upwards [hraw, ae_heightUniv_eq_excursionHeight_ages hθ S] with p hp he
  rwa [he] at hp

/-- Full-filter identification with the continuous height on each finite surviving-age window. -/
theorem heightApprox_tendstoInMeasure_excursionHeight_ages {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (S : ℝ≥0) :
    TendstoInMeasure (heightExcursionAgeMeasure θ S)
      (fun (ε : ℝ) (p : ℝ × Excursion) => heightApprox ε p.2.path p.1.toNNReal)
      (𝓝[>] (0 : ℝ)) (fun p => excursionHeight θ p.2 p.1.toNNReal) := by
  let := isFiniteMeasure_heightExcursionAgeMeasure hθ S
  obtain ⟨L, _, hL⟩ := exists_heightApprox_tendstoInMeasure_excursion_ages hθ S
  have hseq := tendstoInMeasure_of_tendsto_ae (fun k =>
    (measurable_heightApprox_age_excursion (heightEps θ k)).aestronglyMeasurable)
      (ae_tendsto_excursionHeight_ages hθ S)
  exact TendstoInMeasure.congr_right
    (tendstoInMeasure_ae_unique (hL.comp (heightEps_tendsto_nhdsWithin_zero θ)) hseq) hL

end BGW.StableTrees
