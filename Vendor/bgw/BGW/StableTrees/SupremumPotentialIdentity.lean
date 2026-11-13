/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialTail

/-!
# Integral identities for the supremum potential

The identified probability density is integrable without an exponential tilt.
Its tail integral gives the potential and its boundary difference.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem measurable_supremum_density {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) :
    Measurable (fun x => stableSeriesDeriv θ q x - q ^ (1 / θ) * stableSeries θ q x) :=
  (measurable_stableSeriesDeriv hθ q).sub
    (measurable_const.mul (continuous_stableSeries hθ q).measurable)

/-- The unscaled supremum density is integrable without an exponential weight. -/
theorem integrableOn_supremum_density {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    IntegrableOn (fun x => stableSeriesDeriv θ q x - q ^ (1 / θ) * stableSeries θ q x) (Ioi 0) := by
  let := isProbabilityMeasure_expClockLaw θ hq
  let d := fun x => q / q ^ (1 / θ) *
    (stableSeriesDeriv θ q x - q ^ (1 / θ) * stableSeries θ q x)
  have hd : Measurable d := measurable_const.mul (measurable_supremum_density hθ q)
  have hfinite : IsFiniteMeasure ((volume.restrict (Ioi 0)).withDensity
      (fun x => ENNReal.ofReal (d x))) := by
    rw [← map_supRunning_expClockLaw hθ hq]
    infer_instance
  have hi : Integrable d (volume.restrict (Ioi 0)) := by
    refine ⟨hd.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have he : (fun x => ‖d x‖ₑ) =ᵐ[volume.restrict (Ioi 0)] (fun x => ENNReal.ofReal (d x)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact Real.enorm_eq_ofReal (mul_nonneg (by positivity)
        (stableSeriesDeriv_sub_nonneg hθ hq hx))
    rw [lintegral_congr_ae he]
    exact (isFiniteMeasure_withDensity_iff.1 hfinite).lt_top
  have hc := hi.const_mul (q ^ (1 / θ) / q)
  have he : (fun x => q ^ (1 / θ) / q * d x) =
      (fun x => stableSeriesDeriv θ q x - q ^ (1 / θ) * stableSeries θ q x) := by
    funext x
    dsimp [d]
    field_simp
  exact he ▸ hc

/-- `H_q(x) = (q/Φ) ∫_x^∞ (W_q'-ΦW_q)` for `x ≥ 0`. -/
theorem supExpTail_eq_integral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) {x : ℝ}
    (hx : 0 ≤ x) :
    supExpTail θ q x = q / q ^ (1 / θ) * ∫ y in Ioi x,
      (stableSeriesDeriv θ q y - q ^ (1 / θ) * stableSeries θ q y) := by
  let := isProbabilityMeasure_expClockLaw θ hq
  let μ := (expClockLaw θ q).map (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal)
  have hz : μ {x} = 0 := by
    rw [Measure.map_apply measurable_supRunning_expTime (measurableSet_singleton x)]
    exact expClockLaw_supRunning_eq hθ hq x
  have he : μ (Ici x) = μ (Ioi x) := (measure_congr (Ioi_ae_eq_Ici' hz)).symm
  rw [supExpTail_eq_measureReal hθ hq, Measure.real]
  change (μ (Ici x)).toReal = _
  rw [he]
  change (((expClockLaw θ q).map
    (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal)) (Ioi x)).toReal = _
  rw [map_supRunning_expClockLaw hθ hq, withDensity_apply _ measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.2 (Ioi_subset_Ioi hx)]
  have hi := (integrableOn_supremum_density hθ hq).mono_set (Ioi_subset_Ioi hx)
  have hc := hi.const_mul (q / q ^ (1 / θ))
  have hn : ∀ᵐ y ∂volume.restrict (Ioi x),
      0 ≤ q / q ^ (1 / θ) * (stableSeriesDeriv θ q y - q ^ (1 / θ) * stableSeries θ q y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_nonneg (by positivity) (stableSeriesDeriv_sub_nonneg hθ hq (lt_of_le_of_lt hx hy))
  rw [← integral_eq_lintegral_of_nonneg_ae hn hc.aestronglyMeasurable, integral_const_mul]

/-- The potential is the tail integral of the unscaled supremum density. -/
theorem supPotential_eq_integral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) {x : ℝ}
    (hx : 0 ≤ x) : supPotential θ q x = ∫ y in Ioi x,
      (stableSeriesDeriv θ q y - q ^ (1 / θ) * stableSeries θ q y) := by
  rw [supPotential, supExpTail_eq_integral hθ hq hx]
  field_simp

/-- `h_q(0) - h_q(x) = W_q(x) - Φ ∫_0^x W_q(y)dy` for `x ≥ 0`. -/
theorem supPotential_zero_sub {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) {x : ℝ}
    (hx : 0 ≤ x) :
    supPotential θ q 0 - supPotential θ q x =
      stableSeries θ q x - q ^ (1 / θ) * ∫ y in Ioc 0 x, stableSeries θ q y := by
  have hi := integrableOn_supremum_density hθ hq
  have hs : IntegrableOn (stableSeries θ q) (Ioc 0 x) :=
    (continuous_stableSeries hθ q).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [supPotential_eq_integral hθ hq le_rfl, supPotential_eq_integral hθ hq hx,
    intervalIntegral.integral_Ioi_sub_Ioi hi hx, intervalIntegral.integral_of_le hx,
    integral_sub (integrableOn_stableSeriesDeriv hθ q x) (hs.const_mul _), integral_const_mul,
    integral_stableSeriesDeriv hθ q hx]

end BGW.StableTrees
