/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactContourCompact

/-!
# Vanishing contour error on exact-size prefixes

Tightness of a larger height prefix and the local deterministic estimate give convergence
in probability under the exact-size conditioned laws themselves.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees.ExactContour

open BGW.StableTrees.DiscreteForest BGW.StableTrees.TailPair

/-- **Prefix contour error** (finite-tree K12a bracketing with K15 on a larger prefix `a' < 1`):
on `[0,a]`, `a < 1`, the normalized contour at `2nt` is uniformly close to the normalized height
at `nt`, in probability under the exact-size laws. -/
theorem tendsto_contourHeightError_prefix {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun k => (exactTreeLaw μ (q k) : Measure BGW.LocallyFinite.Tree).real
      {τ | ε < contourHeightError B (q k) a τ}) atTop (𝓝 0) := by
  let a' : ℝ≥0 := (a + 1) / 2
  have haa' : a < a' := by
    change (a : ℝ) < (a' : ℝ)
    dsimp [a']
    linarith [show (a : ℝ) < 1 from ha.2]
  have ha' : a' ∈ Ioo (0 : ℝ≥0) 1 := by
    refine ⟨ha.1.trans haa', ?_⟩
    change (a' : ℝ) < 1
    dsimp [a']
    linarith [show (a : ℝ) < 1 from ha.2]
  have htight := isTightMeasureSet_exactHeight_prefix h hqtop hq a' ha'
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨K, hK, hprob⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
    (ENNReal.ofReal (η / 2)) (ENNReal.ofReal_pos.mpr (half_pos hη))
  have hgood := hqtop.eventually (eventually_contourHeightError_le_of_compact h haa' ha'.2 K hK hε)
  filter_upwards [hgood] with k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have hsize : ∀ᵐ τ ∂(exactTreeLaw μ (q k) : Measure LocallyFinite.Tree),
      τ ∈ LocallyFinite.sizeEvent (q k) := by
    rw [exactTreeLaw_toMeasure μ (q k) (hq k)]
    exact ae_cond_mem (LocallyFinite.measurableSet_sizeEvent _)
  have hsub : {τ | ε < contourHeightError B (q k) a τ} ≤ᵐ[
      (exactTreeLaw μ (q k) : Measure LocallyFinite.Tree)]
      {τ | treeHeightPath B (q k) a' τ ∉ K} := by
    filter_upwards [hsize] with τ hτ hbad
    intro hmem
    obtain ⟨t, rfl⟩ := (LocallyFinite.exists_toLocallyFinite_iff τ).mpr hτ.1
    have ht := (LocallyFinite.toLocallyFinite_mem_sizeEvent_iff t (q k)).mp hτ
    exact (not_le_of_gt hbad) (hk t ht hmem)
  have hp := hprob _ (mem_range_self k)
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply (measurable_treeHeightPath B (q k) a')
    hK.measurableSet.compl] at hp
  have hle := (measure_mono_ae hsub).trans hp
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  simp only [ENNReal.toReal_ofReal (half_pos hη).le] at hr
  exact hr.trans_lt (half_lt_self hη)

end BGW.StableTrees.ExactContour
