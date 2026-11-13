/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeOccupation
import Mathlib.MeasureTheory.Function.L2Space

/-!
# First moments of the auxiliary clock

Compact square-mean convergence implies fixed-time convergence in mean. The arbitrary-rate
resolvent bound then passes to the clock before recurrence is established.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The clock is nonnegative at all times on one event. -/
theorem ae_supAuxLocalTime_nonneg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t, 0 ≤ supAuxLocalTime θ f t := by
  filter_upwards [ae_supAuxLocalTime_continuous hθ] with f hf t
  simpa only [hf.1] using hf.2.1 (zero_le : (0 : ℝ≥0) ≤ t)

/-- The clock has integrable values at every deterministic time. -/
theorem integrable_supAuxLocalTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    Integrable (fun f => supAuxLocalTime θ f T) (stableLocalLaw θ : Measure DLoc) := by
  have hT : Measurable (fun _ : DLoc => T) := measurable_const
  have hM := (measurable_supAuxLocalTime_uncurry θ).comp (hT.prodMk measurable_id)
  dsimp only [Function.comp_def] at hM
  have hm : AEStronglyMeasurable (fun f : DLoc => supAuxLocalTime θ f T)
      (stableLocalLaw θ : Measure DLoc) := hM.aestronglyMeasurable
  exact MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    ((memLp_two_iff_integrable_sq hm).mpr (integrable_sq_supAuxLocalTime hθ T))

/-- The compact approximation error used in the square-mean estimate. -/
noncomputable def supAuxApproxError (θ ε : ℝ) (T : ℝ≥0) (f : DLoc) : ℝ :=
  ⨆ t : Set.Iic T, |supOccupation ε f t - supAuxLocalTime θ f t|

/-- The fixed-time error is bounded by the compact error on the continuous-path event. -/
theorem ae_abs_sub_le_supAuxApproxError {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      |supOccupation ε f T - supAuxLocalTime θ f T| ≤ supAuxApproxError θ ε T f := by
  filter_upwards [ae_supAuxLocalTime_continuous hθ] with f hf
  have hcompact : IsCompact (Iic T) := by
    simpa only [Icc, Iic, zero_le, true_and] using
      (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T))
  let : CompactSpace (Iic T) := isCompact_iff_compactSpace.mp hcompact
  have hc : Continuous (fun t : Iic T =>
      |supOccupation ε f t - supAuxLocalTime θ f t|) :=
    (((continuous_supOccupation hε f).sub hf.2.2).abs).comp continuous_subtype_val
  exact le_ciSup (isCompact_range hc).bddAbove ⟨T, le_rfl⟩

/-- An elementary square bound converts compact square error into fixed-time mean error. -/
theorem integral_abs_sub_le_supAuxApproxError {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (T : ℝ≥0) :
    (∫ f, |supOccupation ε f T - supAuxLocalTime θ f T|
      ∂(stableLocalLaw θ : Measure DLoc)) ≤
      δ + (∫ f, supAuxApproxError θ ε T f ^ 2 ∂(stableLocalLaw θ : Measure DLoc)) / δ := by
  have hi := ((integrable_supOccupation θ hε T).sub (integrable_supAuxLocalTime hθ T)).norm
  have hE : Integrable (fun f => supAuxApproxError θ ε T f ^ 2)
      (stableLocalLaw θ : Measure DLoc) :=
    (supOccupation_compact_L2_tendsto_supAuxLimit hθ T).1 ε hε
  have hb : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      |supOccupation ε f T - supAuxLocalTime θ f T| ≤
        δ + supAuxApproxError θ ε T f ^ 2 / δ := by
    filter_upwards [ae_abs_sub_le_supAuxApproxError hθ hε T] with f hf
    have hh : supAuxApproxError θ ε T f ≤ δ + supAuxApproxError θ ε T f ^ 2 / δ := by
      have hs : (supAuxApproxError θ ε T f - δ) * δ ≤
          supAuxApproxError θ ε T f ^ 2 := by
        nlinarith [sq_nonneg (supAuxApproxError θ ε T f - δ)]
      have hd := (le_div_iff₀ hδ).mpr hs
      linarith
    exact hf.trans hh
  have hh := integral_mono_ae hi ((integrable_const δ).add (hE.div_const δ)) hb
  simpa only [Pi.sub_apply, Pi.add_apply, Real.norm_eq_abs,
    integral_add (integrable_const δ) (hE.div_const δ),
    integral_const, probReal_univ, one_smul, integral_div] using hh

/-- Fixed-time occupations converge in mean along the full positive-cutoff filter. -/
theorem tendsto_integral_abs_supOccupation_sub {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    Tendsto (fun ε : ℝ => ∫ f, |supOccupation ε f T - supAuxLocalTime θ f T|
      ∂(stableLocalLaw θ : Measure DLoc)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  have hδ : 0 < η / 2 := half_pos hη
  have hl := (supOccupation_compact_L2_tendsto_supAuxLimit hθ T).2
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (∫ f, supAuxApproxError θ ε T f ^ 2 ∂(stableLocalLaw θ : Measure DLoc)) < (η / 2) ^ 2 :=
    hl.eventually (Iio_mem_nhds (sq_pos_of_pos hδ))
  filter_upwards [self_mem_nhdsWithin, he] with ε hε hεE
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun f => abs_nonneg _)]
  have hb := integral_abs_sub_le_supAuxApproxError hθ hε hδ T
  have hd : (∫ f, supAuxApproxError θ ε T f ^ 2
      ∂(stableLocalLaw θ : Measure DLoc)) / (η / 2) < η / 2 := by
    apply (div_lt_iff₀ hδ).mpr
    nlinarith only [hεE]
  linarith

/-- The occupation means converge to the clock mean. -/
theorem tendsto_integral_supOccupation {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    Tendsto (fun ε : ℝ => ∫ f, supOccupation ε f T ∂(stableLocalLaw θ : Measure DLoc))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ f, supAuxLocalTime θ f T ∂(stableLocalLaw θ : Measure DLoc))) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun ε => dist_nonneg) _
    (tendsto_integral_abs_supOccupation_sub hθ T)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [Real.dist_eq, ← integral_sub (integrable_supOccupation θ hε T)
    (integrable_supAuxLocalTime hθ T)]
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
    (fun f => supOccupation ε f T - supAuxLocalTime θ f T)

/-- The arbitrary-rate first-moment growth bound passes to the clock. -/
theorem integral_supAuxLocalTime_le_exp {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q : ℝ} (hq : 0 < q) (T : ℝ≥0) :
    (∫ f, supAuxLocalTime θ f T ∂(stableLocalLaw θ : Measure DLoc)) ≤
      Real.exp (q * T) * (q ^ (1 / θ) / q) := by
  apply le_of_tendsto (tendsto_integral_supOccupation hθ T)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact integral_supOccupation_le_exp hθ hq hε T

end BGW.StableTrees
