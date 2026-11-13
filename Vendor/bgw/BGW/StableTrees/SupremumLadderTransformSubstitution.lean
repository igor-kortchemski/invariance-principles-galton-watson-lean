/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderTransformBasic

/-!
# Substitution by inverse local time

The inverse pushes positive-level Lebesgue measure to the clock measure. Endpoint
ambiguities at flat levels are squeezed between open and closed intervals of equal volume.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- A monotone right inverse of a continuous clock pushes level volume to its Stieltjes measure.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem map_inverse_eq_pathStieltjes {m : ℝ≥0 → ℝ} {A : ℝ≥0 → ℝ≥0}
    (hm : Monotone m ∧ Continuous m) (hm0 : m 0 = 0) (hA : Monotone A)
    (hinv : ∀ z : ℝ≥0, m (A z) = z) :
    (volume.restrict (Ioi (0 : ℝ))).map (fun z : ℝ => (A z.toNNReal : ℝ)) =
      (pathStieltjes m).measure.restrict (Ioi (0 : ℝ)) := by
  let B : ℝ → ℝ := fun z => (A z.toNNReal : ℝ)
  have hB : Measurable B := hA.measurable.coe_nnreal_real.comp measurable_real_toNNReal
  have hmass (t : ℝ) :
      ((volume.restrict (Ioi (0 : ℝ))).map B) (Iic t) = ENNReal.ofReal (m t.toNNReal) := by
    rw [Measure.map_apply hB measurableSet_Iic, Measure.restrict_apply
      (hB measurableSet_Iic)]
    by_cases ht : 0 ≤ t
    · have hlo : Ioo (0 : ℝ) (m t.toNNReal) ⊆ B ⁻¹' Iic t ∩ Ioi 0 := by
        intro z hz
        have hzcoe : (z.toNNReal : ℝ) = z := Real.coe_toNNReal _ hz.1.le
        have ha : A z.toNNReal ≤ t.toNNReal := by
          by_contra hn
          have h := hm.1 (le_of_lt (lt_of_not_ge hn))
          rw [hinv, hzcoe] at h
          exact not_le_of_gt hz.2 h
        refine ⟨?_, hz.1⟩
        change (A z.toNNReal : ℝ) ≤ t
        simpa only [Real.coe_toNNReal _ ht] using (NNReal.coe_le_coe.mpr ha)
      have hhi : B ⁻¹' Iic t ∩ Ioi 0 ⊆ Ioc (0 : ℝ) (m t.toNNReal) := by
        rintro z ⟨hzA, hz⟩
        change (A z.toNNReal : ℝ) ≤ t at hzA
        have ha : A z.toNNReal ≤ t.toNNReal := by
          apply NNReal.coe_le_coe.mp
          simpa only [Real.coe_toNNReal _ ht] using hzA
        have h := hm.1 ha
        rw [hinv, Real.coe_toNNReal _ hz.le] at h
        exact ⟨hz, h⟩
      apply le_antisymm
      · simpa only [Real.volume_Ioc, sub_zero] using measure_mono (μ := volume) hhi
      · simpa only [Real.volume_Ioo, sub_zero] using measure_mono (μ := volume) hlo
    · have he : B ⁻¹' Iic t ∩ Ioi 0 = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro z ⟨hz, _⟩
        exact ht ((A z.toNNReal).coe_nonneg.trans hz)
      rw [he, measure_empty, Real.toNNReal_of_nonpos (not_le.mp ht).le, hm0,
        ENNReal.ofReal_zero]
  have hclock (t : ℝ) :
      (pathStieltjes m).measure.restrict (Ioi (0 : ℝ)) (Iic t) =
        ENNReal.ofReal (m t.toNNReal) := by
    rw [Measure.restrict_apply measurableSet_Iic, Iic_inter_Ioi,
      pathStieltjes_measure_Ioc hm, Real.toNNReal_zero, hm0, sub_zero]
  symm
  apply Measure.ext_of_Ioc' _ _
  · intro a b _
    exact ne_of_lt ((measure_mono Ioc_subset_Iic_self).trans_lt (by
      rw [hclock b]
      exact ENNReal.ofReal_lt_top))
  · intro a b hab
    rw [← Iic_sdiff_Iic, measure_sdiff (Iic_subset_Iic.mpr hab.le)
      measurableSet_Iic.nullMeasurableSet (by rw [hclock a]; exact ENNReal.ofReal_ne_top),
      measure_sdiff (Iic_subset_Iic.mpr hab.le)
        measurableSet_Iic.nullMeasurableSet (by rw [hmass a]; exact ENNReal.ofReal_ne_top),
      hclock, hclock, hmass, hmass]

/-- **Stieltjes substitution** (pathwise, `q, λ ≥ 0`): almost surely
`∫_{(0,∞)} e^{-q A_z - λ B_z} dz = ∫_{(0,∞)} e^{-qt-λS_t} dM_t`
(`M` continuous nondecreasing, `M(A_z) = z`, `B_z = S_{A_z}`; `dM = A_* Leb`).

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem ae_lintegral_supLadder_eq_supBoundaryPotential {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam : ℝ} (hq : 0 ≤ q) (hlam : 0 ≤ lam) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∫⁻ z in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-q * (supLadderTime θ z.toNNReal f : ℝ) -
            lam * supLadderHeight θ z.toNNReal f)) = supBoundaryPotential θ q lam f := by
  -- `hq` and `hlam` are part of the stated interface; the substitution holds for all real
  -- parameters.
  have _hq := hq
  have _hlam := hlam
  filter_upwards [ae_supLocalTime_spec hθ, ae_supLadder_spec hθ] with f hm hA
  have he := map_inverse_eq_pathStieltjes ⟨hm.2.1, hm.2.2.1⟩ hm.1 hA.2.2.1 hA.2.2.2.2.2
  let w : ℝ → ℝ≥0∞ := fun t =>
    ENNReal.ofReal (Real.exp (-q * t - lam * supRunning f t.toNNReal))
  have hw : Measurable w := by
    apply Measurable.ennreal_ofReal
    apply Measurable.exp
    exact (measurable_const.mul measurable_id).sub
      (measurable_const.mul ((monotone_supRunning f).measurable.comp measurable_real_toNNReal))
  have hi := lintegral_map (μ := volume.restrict (Ioi (0 : ℝ))) hw
    (hA.2.2.1.measurable.coe_nnreal_real.comp measurable_real_toNNReal)
  simp only [Function.comp_def] at hi
  rw [he] at hi
  change _ = ∫⁻ t in Ioi (0 : ℝ), w t ∂(pathStieltjes (supLocalTime θ f)).measure
  simpa only [w, Real.toNNReal_coe, supLadderHeight] using hi.symm

end BGW.StableTrees
