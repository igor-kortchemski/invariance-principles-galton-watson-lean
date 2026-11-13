/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderTransformMeanError
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The normalized boundary potential

The compact error tends to zero first, and the half-rate bound then removes the tail.
Exponential-clock independence identifies the resulting finite mean.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Weighted occupations converge in mean to the real boundary potential.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem tendsto_integral_abs_supWeightedOccupation_sub {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam : ℝ} (hq : 0 < q) (hlam : 0 ≤ lam) :
    Tendsto (fun ε : ℝ => ∫ f,
      |supWeightedOccupation q lam ε f - (supBoundaryPotential θ q lam f).toReal|
        ∂(stableLocalLaw θ : Measure DLoc)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let δ := η / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let C := 2 * ((q / 2) ^ (1 / θ) / (q / 2))
  have htail : Tendsto (fun N : ℕ => Real.exp (-(q / 2) * (N : ℝ)) * C)
      atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos hq))).mul_const C
    simpa only [Function.comp_def, neg_mul, zero_mul] using h
  obtain ⟨N, hN⟩ := (htail.eventually (Iio_mem_nhds hδ)).exists
  have hcompact := (supOccupation_compact_L2_tendsto_supAuxLimit hθ (N : ℝ≥0)).2
  have hsmall := hcompact.eventually (Iio_mem_nhds (mul_pos hδ hδ))
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε he
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun f => abs_nonneg _)]
  have hb := integral_abs_supWeightedOccupation_sub_le hθ hq hlam hε hδ (N : ℝ≥0)
  have hquot : (∫ f, supAuxApproxError θ ε (N : ℝ≥0) f ^ 2
      ∂(stableLocalLaw θ : Measure DLoc)) / δ < δ := (div_lt_iff₀ hδ).mpr he
  change Real.exp (-(q / 2) * (N : ℝ)) * C < δ at hN
  dsimp [δ, C] at hb hquot hN
  simp only [NNReal.coe_natCast] at hb
  exact lt_of_le_of_lt hb (by linarith)

private theorem integral_weightedOccupation_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam ε : ℝ} (hq : 0 < q) (hlam : 0 ≤ lam) (hε : 0 < ε) :
    (∫ f, supWeightedOccupation q lam ε f ∂(stableLocalLaw θ : Measure DLoc)) =
      q⁻¹ * (ε⁻¹ * (1 - Real.exp (-(ε * q ^ (1 / θ))))) *
        ∫ p, Real.exp (-lam * supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q := by
  rw [← integral_resolvent_exp_neg_supRunning hθ hq hlam hε]
  apply integral_congr_ae
  filter_upwards with f
  apply integral_congr_ae
  filter_upwards with t
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Boundary potential, mean form.** For `q > 0`, `λ ≥ 0`:
`E ∫_0^∞ e^{-qt-λS_t} dM_t = (Φ/q) E e^{-λ S_{e_q}}`
(cumulative Tonelli representation, compact square-mean occupation error, and half-rate
control of the tail, along the full positive-cutoff filter). -/
theorem lintegral_supBoundaryPotential_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ}
    (hq : 0 < q) (hlam : 0 ≤ lam) :
    ∫⁻ f, supBoundaryPotential θ q lam f ∂(stableLocalLaw θ : Measure DLoc) =
      ENNReal.ofReal (q ^ (1 / θ) / q *
        ∫ p, Real.exp (-lam * supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q) := by
  have hV := integrable_supBoundaryPotential_toReal hθ hq hlam
  have hmean : Tendsto (fun ε : ℝ => ∫ f, supWeightedOccupation q lam ε f
    ∂(stableLocalLaw θ : Measure DLoc))
      (𝓝[>] 0) (𝓝 (∫ f, (supBoundaryPotential θ q lam f).toReal
        ∂(stableLocalLaw θ : Measure DLoc))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun ε => dist_nonneg) _
      (tendsto_integral_abs_supWeightedOccupation_sub hθ hq hlam)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [Real.dist_eq, ← integral_sub (integrable_supWeightedOccupation hθ hq hlam hε) hV]
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (μ := (stableLocalLaw θ : Measure DLoc))
      (fun f => supWeightedOccupation q lam ε f - (supBoundaryPotential θ q lam f).toReal)
  have hd : HasDerivAt (fun ε : ℝ => 1 - Real.exp (-(q ^ (1 / θ)) * ε)) (q ^ (1 / θ)) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul (-(q ^ (1 / θ)))).exp.const_sub 1)
      using 1 <;> simp
  have hcoef : Tendsto (fun ε : ℝ => ε⁻¹ * (1 - Real.exp (-(ε * q ^ (1 / θ)))))
      (𝓝[>] 0) (𝓝 (q ^ (1 / θ))) := by
    simpa only [zero_add, mul_zero, zero_mul, neg_zero, Real.exp_zero, sub_self, sub_zero,
      smul_eq_mul,
      mul_comm, neg_mul, mul_neg] using hd.tendsto_slope_zero_right
  have hformula := (hcoef.const_mul q⁻¹).mul_const
    (∫ p, Real.exp (-lam * supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q)
  have he : (∫ f, (supBoundaryPotential θ q lam f).toReal ∂(stableLocalLaw θ : Measure DLoc)) =
      q ^ (1 / θ) / q *
        ∫ p, Real.exp (-lam * supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q := by
    have hlim := hformula.congr' (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (integral_weightedOccupation_eq hθ hq hlam hε).symm)
    simpa only [div_eq_mul_inv, mul_comm q⁻¹] using tendsto_nhds_unique hmean hlim
  calc
    _ = ∫⁻ f, ENNReal.ofReal (supBoundaryPotential θ q lam f).toReal
      ∂(stableLocalLaw θ : Measure DLoc) := by
      apply lintegral_congr_ae
      filter_upwards [ae_supBoundaryPotential_cumulative hθ hq hlam] with f hf
      exact (ENNReal.ofReal_toReal (by rw [hf.1]; exact ENNReal.ofReal_ne_top)).symm
    _ = ENNReal.ofReal (∫ f, (supBoundaryPotential θ q lam f).toReal
      ∂(stableLocalLaw θ : Measure DLoc)) :=
      (ofReal_integral_eq_lintegral_ofReal hV (ae_of_all _ fun f => ENNReal.toReal_nonneg)).symm
    _ = _ := congrArg ENNReal.ofReal he

/-- **Boundary potential, exact form**: `E ∫_0^∞ e^{-qt-λS_t} dM_t = 1/κ(q,λ)`. -/
theorem lintegral_supBoundaryPotential {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ}
    (hq : 0 < q) (hlam : 0 ≤ lam) :
    ∫⁻ f, supBoundaryPotential θ q lam f ∂(stableLocalLaw θ : Measure DLoc) =
      ENNReal.ofReal (supLadderExponent θ q lam)⁻¹ := by
  rw [lintegral_supBoundaryPotential_eq hθ hq hlam,
    inv_supLadderExponent_eq_integral hθ hq hlam]

end BGW.StableTrees
