/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightScalingMeasure

/-!
# Scaling of the continuous excursion height under the excursion measure

The two universal-subsequence limits are identified through the full-filter limit on finite
surviving-age windows. Continuity extends equality from almost every age to every age.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- Fixed-scale height equality on each finite surviving excursion age window. -/
theorem ae_excursionHeight_scale_ages {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (c : Ioi (0 : ℝ)) (S : ℝ≥0) :
    ∀ᵐ p ∂heightExcursionAgeMeasure θ S,
      excursionHeight θ (excursionScale θ c p.2) ((c : ℝ).toNNReal * p.1.toNNReal) =
        (c : ℝ) ^ (1 - 1 / θ) * excursionHeight θ p.2 p.1.toNNReal := by
  let := isFiniteMeasure_heightExcursionAgeMeasure hθ S
  let a : ℝ := (c : ℝ) ^ (1 / θ)
  let b : ℝ := (c : ℝ) ^ (1 - 1 / θ)
  have ha : 0 < a := Real.rpow_pos_of_pos c.2 _
  have hcut : Tendsto (fun n => heightEps θ n / a) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun n => div_pos (heightEps_pos θ n) ha⟩
    simpa only [zero_div] using
      ((heightEps_tendsto_nhdsWithin_zero θ).mono_right nhdsWithin_le_nhds).div_const a
  have hconv := (heightApprox_tendstoInMeasure_excursionHeight_ages hθ S).comp hcut
  have hmul := tendstoInMeasure_continuous_comp_filter
    (fun n => measurable_heightApprox_age_excursion (heightEps θ n / a)) hconv
      (show Continuous (fun y : ℝ => b * y) from continuous_const.mul continuous_id)
  have hs := (quasiMeasurePreserving_excursion_age_scale hθ c S).ae
    (ae_tendsto_excursionHeight_ages hθ ((c : ℝ).toNNReal * S))
  have hs' : ∀ᵐ p ∂heightExcursionAgeMeasure θ S,
      Tendsto (fun n => b * heightApprox (heightEps θ n / a) p.2.path p.1.toNNReal) atTop
        (𝓝 (excursionHeight θ (excursionScale θ c p.2)
          ((c : ℝ).toNNReal * p.1.toNNReal))) := by
    filter_upwards [hs] with p hp
    have he (n : ℕ) : heightApprox (heightEps θ n) (excursionScale θ c p.2).path
        ((c : ℝ).toNNReal * p.1.toNNReal) = b * heightApprox (heightEps θ n / a) p.2.path
          p.1.toNNReal := by
      exact heightApprox_scaleLoc θ c p.2.path p.1.toNNReal (heightEps θ n)
    simpa only [Prod.map_fst, Prod.map_snd, he, Real.toNNReal_mul c.2.le] using hp
  have hsM := tendstoInMeasure_of_tendsto_ae
    (fun n => (measurable_const.mul
      (measurable_heightApprox_age_excursion (heightEps θ n / a))).aestronglyMeasurable) hs'
  exact tendstoInMeasure_ae_unique hsM hmul

/-- Almost-everywhere interior scale equality determines the two continuous heights everywhere. -/
theorem excursionHeight_scale_of_ae (θ : ℝ) (c : Ioi (0 : ℝ)) (e : Excursion)
    (he : ∀ᵐ s : ℝ ∂(volume.restrict (Ioi (0 : ℝ))), s.toNNReal < e.lifetime →
      excursionHeight θ (excursionScale θ c e) ((c : ℝ).toNNReal * s.toNNReal) =
        (c : ℝ) ^ (1 - 1 / θ) * excursionHeight θ e s.toNNReal) :
    ∀ t : ℝ≥0, excursionHeight θ (excursionScale θ c e) ((c : ℝ).toNNReal * t) =
      (c : ℝ) ^ (1 - 1 / θ) * excursionHeight θ e t := by
  have hleft : Continuous (fun s : ℝ =>
      excursionHeight θ (excursionScale θ c e) ((c : ℝ).toNNReal * s.toNNReal)) :=
    (excursionHeight θ (excursionScale θ c e)).continuous.comp
      (continuous_const.mul continuous_real_toNNReal)
  have hright : Continuous (fun s : ℝ =>
      (c : ℝ) ^ (1 - 1 / θ) * excursionHeight θ e s.toNNReal) :=
    continuous_const.mul ((excursionHeight θ e).continuous.comp continuous_real_toNNReal)
  have hinside : ∀ᵐ s : ℝ ∂(volume.restrict (Ioo (0 : ℝ) (e.lifetime : ℝ))),
      excursionHeight θ (excursionScale θ c e) ((c : ℝ).toNNReal * s.toNNReal) =
        (c : ℝ) ^ (1 - 1 / θ) * excursionHeight θ e s.toNNReal := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioi_self : Ioo (0 : ℝ) (e.lifetime : ℝ) ⊆ Ioi 0) he,
      ae_restrict_mem measurableSet_Ioo] with s hs hmem
    apply hs
    change (s.toNNReal : ℝ) < (e.lifetime : ℝ)
    rw [Real.coe_toNNReal _ hmem.1.le]
    exact hmem.2
  have heq := eqOn_Icc_of_ae_eq_Ioo (show (0 : ℝ) < e.lifetime from e.lifetime_pos)
    hleft hright hinside
  intro t
  by_cases ht : e.lifetime ≤ t
  · rw [excursionHeight_eq_zero_of_lifetime_le θ e ht, mul_zero]
    apply excursionHeight_eq_zero_of_lifetime_le
    change (c : ℝ).toNNReal * e.lifetime ≤ (c : ℝ).toNNReal * t
    exact mul_le_mul_of_nonneg_left ht zero_le
  · have hmem : (t : ℝ) ∈ Icc (0 : ℝ) (e.lifetime : ℝ) := ⟨t.2, (not_le.mp ht).le⟩
    simpa only [Real.toNNReal_coe] using heq hmem

/-- **Scaling under `N`**, for each fixed `c > 0`:
`H(S_c e)(c t) = c^(1-1/θ) H(e)(t)` for all `t`, `N`-a.e. -/
theorem ae_excursionHeight_scale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (c : Set.Ioi (0 : ℝ)) :
    ∀ᵐ e ∂(excursionMeasure θ), ∀ t : ℝ≥0,
      excursionHeight θ (excursionScale θ c e) ((c : ℝ).toNNReal * t) =
        (c : ℝ) ^ (1 - 1 / θ) * excursionHeight θ e t := by
  let := sigmaFinite_excursionMeasure hθ
  have hmL : Measurable (fun p : ℝ × Excursion =>
      excursionHeight θ (excursionScale θ c p.2) ((c : ℝ).toNNReal * p.1.toNNReal)) :=
    Measurable.comp (g := fun p : ℝ≥0 × Excursion => excursionHeight θ p.2 p.1)
      (f := fun p : ℝ × Excursion =>
        ((c : ℝ).toNNReal * p.1.toNNReal, excursionScale θ c p.2))
      (measurable_excursionHeight_uncurry θ)
      ((measurable_const.mul (measurable_real_toNNReal.comp measurable_fst)).prodMk
        ((measurable_excursionScale θ c).comp measurable_snd))
  have hm : MeasurableSet {p : ℝ × Excursion | p.1.toNNReal < p.2.lifetime →
      excursionHeight θ (excursionScale θ c p.2) ((c : ℝ).toNNReal * p.1.toNNReal) =
        (c : ℝ) ^ (1 - 1 / θ) * excursionHeight θ p.2 p.1.toNNReal} := by
    convert measurableSet_heightExcursionAge_survival.compl.union
      (measurableSet_eq_fun hmL (measurable_const.mul
        (measurable_excursionHeight_real_age θ))) using 1
    ext p
    exact imp_iff_not_or
  have hn (n : ℕ) : ∀ᵐ e ∂excursionMeasure θ,
      ∀ᵐ s : ℝ ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))), s.toNNReal < e.lifetime →
        excursionHeight θ (excursionScale θ c e) ((c : ℝ).toNNReal * s.toNNReal) =
          (c : ℝ) ^ (1 - 1 / θ) * excursionHeight θ e s.toNNReal := by
    apply (MeasureTheory.Measure.ae_ae_comm hm).mp
    apply (MeasureTheory.Measure.ae_prod_iff_ae_ae hm).mp
    exact (ae_restrict_iff' measurableSet_heightExcursionAge_survival).mp
      (ae_excursionHeight_scale_ages hθ c n)
  have hu : (⋃ n : ℕ, Ioo (0 : ℝ) (n : ℝ)) = Ioi 0 := by
    ext s
    simp only [mem_iUnion, mem_Ioo, mem_Ioi]
    exact ⟨fun ⟨_, hs, _⟩ => hs, fun hs =>
      let ⟨n, hn⟩ := exists_nat_gt s
      ⟨n, hs, hn⟩⟩
  filter_upwards [ae_all_iff.mpr hn] with e he
  apply excursionHeight_scale_of_ae θ c e
  have hh := (ae_restrict_iUnion_iff _ _).mpr he
  simpa only [hu] using hh

end BGW.StableTrees
