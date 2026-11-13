/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumStoppedEnergyOccupation
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Full-filter stopped occupation convergence

Uniform second moments follow from the inverse-time energy and exact mean. The energy
bound vanishes along the full positive filter; Markov's inequality gives maximal convergence.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Auxiliary form of `supOccupation_stopped_L2_bound` (`A^*`, same shape). -/
theorem supOccupation_stopped_L2_bound_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Integrable (fun f => (supOccupation ε f (supAuxLadderTime θ z f)) ^ 2)
          (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (supOccupation ε f (supAuxLadderTime θ z f)) ^ 2 ∂(stableLocalLaw θ : Measure DLoc)
        ≤ C := by
  let K : ℝ := 1 / Real.Gamma θ + 1 / 2
  have hg := Real.Gamma_pos_of_pos (by linarith [hθ.1] : 0 < θ)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨(z : ℝ) ^ 2 + 4 * z * K + 12 * K ^ 2, by positivity, ?_⟩
  intro ε hε hε1
  have hV : 0 ≤ supCorrectionBound θ ε := by unfold supCorrectionBound; positivity
  have hVK : supCorrectionBound θ ε ≤ K := by
    change K * ε ^ (θ - 1) ≤ K
    exact mul_le_of_le_one_right hK (Real.rpow_le_one hε.le hε1 (by linarith [hθ.1]))
  have he := integral_sq_supOccupation_sub_supAuxLadderTime_le hθ hε z
  have ho := integral_supOccupation_supAuxLadderTime hθ hε z
  let O : DLoc → ℝ := fun f => supOccupation ε f (supAuxLadderTime θ z f)
  have hi : Integrable (fun f => O f ^ 2) (stableLocalLaw θ : Measure DLoc) := by
    apply ((he.1.add (ho.1.const_mul (2 * (z : ℝ)))).sub
      (integrable_const ((z : ℝ) ^ 2))).congr
    filter_upwards with f
    simp only [Pi.sub_apply, Pi.add_apply]
    dsimp only [O]
    ring
  refine ⟨hi, ?_⟩
  have hcalc : (∫ f, O f ^ 2 ∂(stableLocalLaw θ : Measure DLoc)) =
      (∫ f, (O f - (z : ℝ)) ^ 2 ∂(stableLocalLaw θ : Measure DLoc)) + (z : ℝ) ^ 2 := by
    calc
      _ = ∫ f, ((O f - (z : ℝ)) ^ 2 + 2 * z * O f) - (z : ℝ) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc) := by
        apply integral_congr_ae
        filter_upwards with f
        ring
      _ = _ := by
        have hei : Integrable (fun f => (O f - (z : ℝ)) ^ 2)
            (stableLocalLaw θ : Measure DLoc) := he.1
        have hoi : Integrable O (stableLocalLaw θ : Measure DLoc) := ho.1
        have hsum : Integrable (fun f => (O f - (z : ℝ)) ^ 2 + 2 * z * O f)
            (stableLocalLaw θ : Measure DLoc) := hei.add (hoi.const_mul (2 * (z : ℝ)))
        rw [integral_sub hsum (integrable_const ((z : ℝ) ^ 2)),
          integral_add hei (hoi.const_mul (2 * (z : ℝ))), integral_const_mul, integral_const]
        simp only [probReal_univ, one_smul]
        change _ + 2 * (z : ℝ) * (∫ f, O f ∂(stableLocalLaw θ : Measure DLoc)) - _ = _
        rw [ho.2]
        ring
  change (∫ f, O f ^ 2 ∂(stableLocalLaw θ : Measure DLoc)) ≤ _
  rw [hcalc]
  have hv2 := pow_le_pow_left₀ hV hVK 2
  have hzV := mul_le_mul_of_nonneg_left hVK z.coe_nonneg
  nlinarith [he.2]

/-- Auxiliary form of `supOccupation_stopped_L2_tendsto`. -/
theorem supOccupation_stopped_L2_tendsto_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (z : ℝ≥0) :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Integrable (fun f => (supOccupation ε f (supAuxLadderTime θ z f) - (z : ℝ)) ^ 2)
        (stableLocalLaw θ : Measure DLoc)) ∧
    Tendsto (fun ε : ℝ =>
        ∫ f, (supOccupation ε f (supAuxLadderTime θ z f) - (z : ℝ)) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine ⟨fun ε hε _hε1 => (integral_sq_supOccupation_sub_supAuxLadderTime_le hθ hε z).1, ?_⟩
  have ht := tendsto_supCorrectionBound hθ
  have he : Tendsto (fun ε : ℝ => 4 * (z : ℝ) * supCorrectionBound θ ε +
      12 * supCorrectionBound θ ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using
      (ht.const_mul (4 * (z : ℝ))).add ((ht.pow 2).const_mul 12)
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) _ he
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_sq_supOccupation_sub_supAuxLadderTime_le hθ hε z).2

/-- Auxiliary form of `supOccupation_stopped_uniform_tendstoInMeasure` (Markov on the stopped
maximal estimate; `z = 0` is the same bound). -/
theorem supOccupation_stopped_uniform_tendstoInMeasure_aux {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (z : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun ε : ℝ =>
        (stableLocalLaw θ : Measure DLoc)
          {f | δ ≤ ⨆ t : Set.Iic (supAuxLadderTime θ z f),
              |supOccupation ε f t - supAuxLocalTime θ f t|})
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let P : Measure DLoc := stableLocalLaw θ
  let H : ℝ → DLoc → ℝ := fun ε f => ⨆ t : Set.Iic (supAuxLadderTime θ z f),
    |supOccupation ε f t - supAuxLocalTime θ f t|
  let E : ℝ → ℝ := fun ε =>
    104 * ((z : ℝ) * supCorrectionBound θ ε + supCorrectionBound θ ε ^ 2)
  have hδ2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have ht : Tendsto (fun ε => ENNReal.ofReal (E ε / δ ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_div, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal ((tendsto_stopped_energy_bound hθ z).div_const (δ ^ 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hi := integral_sq_sup_supOccupation_sub_supAuxLocalTime_le hθ hε z
  have hm := meas_ge_le_lintegral_div hi.1.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (ENNReal.ofReal_ne_zero_iff.mpr hδ2) ENNReal.ofReal_ne_top
  calc
    P {f | δ ≤ H ε f} ≤ P {f | ENNReal.ofReal (δ ^ 2) ≤ ENNReal.ofReal (H ε f ^ 2)} := by
      apply measure_mono
      intro f hf
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hδ.le hf 2)
    _ ≤ (∫⁻ f, ENNReal.ofReal (H ε f ^ 2) ∂P) / ENNReal.ofReal (δ ^ 2) := hm
    _ = ENNReal.ofReal ((∫ f, H ε f ^ 2 ∂P) / δ ^ 2) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi.1 (ae_of_all _ (fun _ => sq_nonneg _)),
        ENNReal.ofReal_div_of_pos hδ2]
    _ ≤ ENNReal.ofReal (E ε / δ ^ 2) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hi.2 hδ2.le)

end BGW.StableTrees
