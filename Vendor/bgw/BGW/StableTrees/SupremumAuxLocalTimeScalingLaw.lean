/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeScaling

/-!
# Scaling law of the constructed auxiliary clock

The positive-filter convergence in mean identifies dilated occupations with the clock.
No invariance of the particular fast cutoff sequence is asserted or needed.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Stable path dilation preserves the expectation of any integrable scalar observable. -/
theorem integral_scaleLoc {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (c : Ioi (0 : ℝ))
    {G : DLoc → ℝ} (hG : Integrable G (stableLocalLaw θ : Measure DLoc)) :
    (∫ f, G (scaleLoc θ c f) ∂(stableLocalLaw θ : Measure DLoc)) =
      ∫ f, G f ∂(stableLocalLaw θ : Measure DLoc) := by
  have hm : AEStronglyMeasurable G
      ((stableLocalLaw θ : Measure DLoc).map (scaleLoc θ c)) := by
    rw [map_scaleLoc_stableLocalLaw hθ c]
    exact hG.aestronglyMeasurable
  have he := integral_map (measurable_scaleLoc θ c).aemeasurable hm
  rw [map_scaleLoc_stableLocalLaw hθ c] at he
  exact he.symm

/-- Clock scaling at each deterministic time follows from occupation scaling in mean. -/
theorem ae_supAuxLocalTime_scaleLoc {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (c : Ioi (0 : ℝ)) (t : ℝ≥0) :
    (fun f => supAuxLocalTime θ (scaleLoc θ c f) t) =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      fun f => ((c : ℝ) / (c : ℝ) ^ (1 / θ)) *
        supAuxLocalTime θ f (t / (c : ℝ).toNNReal) := by
  let P : Measure DLoc := stableLocalLaw θ
  let a := (c : ℝ) ^ (1 / θ)
  let d := (c : ℝ) / a
  let T := t / (c : ℝ).toNNReal
  let F : DLoc → ℝ := fun f => supAuxLocalTime θ (scaleLoc θ c f) t
  let H : DLoc → ℝ := fun f => d * supAuxLocalTime θ f T
  have ha : 0 < a := Real.rpow_pos_of_pos c.2 _
  have hd : 0 < d := div_pos c.2 ha
  have hpres : MeasurePreserving (scaleLoc θ c) P P :=
    ⟨measurable_scaleLoc θ c, map_scaleLoc_stableLocalLaw hθ c⟩
  have hFi : Integrable F P :=
    hpres.integrable_comp_of_integrable (integrable_supAuxLocalTime hθ t)
  have hHi : Integrable H P := (integrable_supAuxLocalTime hθ T).const_mul d
  have hDi : Integrable (fun f => |F f - H f|) P := by
    simpa only [Pi.sub_apply] using (hFi.sub hHi).abs
  have hdiv : Tendsto (fun ε : ℝ => ε / a) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [id_eq, zero_div] using
        ((continuous_id.div_const a).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact div_pos hε ha
  have hl := (tendsto_integral_abs_supOccupation_sub hθ t).add
    (((tendsto_integral_abs_supOccupation_sub hθ T).comp hdiv).const_mul d)
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] 0, (∫ f, |F f - H f| ∂P) ≤
      (∫ f, |supOccupation ε f t - supAuxLocalTime θ f t| ∂P) +
        d * (∫ f, |supOccupation (ε / a) f T - supAuxLocalTime θ f T| ∂P) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    let K : DLoc → ℝ := fun f => supOccupation ε (scaleLoc θ c f) t
    have hKi : Integrable K P :=
      hpres.integrable_comp_of_integrable (integrable_supOccupation θ hε t)
    have hB : Integrable (fun f => |supOccupation (ε / a) f T - supAuxLocalTime θ f T|) P := by
      simpa only [Pi.sub_apply] using
        ((integrable_supOccupation θ (div_pos hε ha) T).sub
          (integrable_supAuxLocalTime hθ T)).abs
    have hAK : Integrable (fun f => |K f - F f|) P := by
      simpa only [Pi.sub_apply] using (hKi.sub hFi).abs
    have hineq : (∫ f, |F f - H f| ∂P) ≤
        (∫ f, |K f - F f| ∂P) +
          d * (∫ f, |supOccupation (ε / a) f T - supAuxLocalTime θ f T| ∂P) := by
      calc
        _ ≤ ∫ f, |K f - F f| +
            d * |supOccupation (ε / a) f T - supAuxLocalTime θ f T| ∂P := by
          apply integral_mono_ae hDi (hAK.add (hB.const_mul d))
          filter_upwards with f
          change |F f - H f| ≤ |K f - F f| +
            d * |supOccupation (ε / a) f T - supAuxLocalTime θ f T|
          have hK : K f = d * supOccupation (ε / a) f T :=
            supOccupation_scaleLoc θ ε c f t
          have hKH : |K f - H f| =
              d * |supOccupation (ε / a) f T - supAuxLocalTime θ f T| := by
            rw [hK]
            change |d * supOccupation (ε / a) f T - d * supAuxLocalTime θ f T| = _
            rw [← mul_sub, abs_mul, abs_of_pos hd]
          calc
            _ ≤ |F f - K f| + |K f - H f| := abs_sub_le _ _ _
            _ = _ := by rw [abs_sub_comm (F f) (K f), hKH]

        _ = _ := by
          rw [integral_add hAK (hB.const_mul d), integral_const_mul]
    have hG : Integrable (fun f => |supOccupation ε f t - supAuxLocalTime θ f t|) P := by
      simpa only [Pi.sub_apply] using
        ((integrable_supOccupation θ hε t).sub (integrable_supAuxLocalTime hθ t)).abs
    have hmap := integral_scaleLoc hθ c hG
    simpa only [K, F] using hineq.trans_eq (congrArg
      (fun x => x + d * (∫ f, |supOccupation (ε / a) f T - supAuxLocalTime θ f T| ∂P)) hmap)
  have hz : (∫ f, |F f - H f| ∂P) = 0 := by
    apply le_antisymm _ (integral_nonneg fun f => abs_nonneg _)
    simpa only [mul_zero, add_zero] using ge_of_tendsto hl hb
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun f => abs_nonneg _) hDi).mp hz
  filter_upwards [hae] with f hf
  exact sub_eq_zero.mp (abs_eq_zero.mp hf)

/-- The one-time clock laws have the stable local-time scaling factor. -/
theorem map_supAuxLocalTime_scaling {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (c : Ioi (0 : ℝ)) (t : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc).map (fun f => supAuxLocalTime θ f t) =
      (stableLocalLaw θ : Measure DLoc).map (fun f =>
        ((c : ℝ) / (c : ℝ) ^ (1 / θ)) * supAuxLocalTime θ f (t / (c : ℝ).toNNReal)) := by
  have ht : Measurable (fun f : DLoc => supAuxLocalTime θ f t) := by
    have hc : Measurable (fun _ : DLoc => t) := measurable_const
    have hh := (measurable_supAuxLocalTime_uncurry θ).comp (hc.prodMk measurable_id)
    exact hh
  calc
    _ = ((stableLocalLaw θ : Measure DLoc).map (scaleLoc θ c)).map
        (fun f => supAuxLocalTime θ f t) := by rw [map_scaleLoc_stableLocalLaw hθ c]
    _ = _ := by
      rw [Measure.map_map ht (measurable_scaleLoc θ c)]
      exact Measure.map_congr (ae_supAuxLocalTime_scaleLoc hθ c t)

end BGW.StableTrees
