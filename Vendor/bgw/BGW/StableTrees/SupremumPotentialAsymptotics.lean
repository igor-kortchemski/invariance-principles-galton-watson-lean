/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialIdentity
public import BGW.StableTrees.SupremumPotentialZeroRate

/-!
# Uniform boundary-potential asymptotics

Compact joint continuity bounds the integral remainder in the boundary identity.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace BGW.StableTrees

/-- Zero-rate boundary asymptotics, locally uniformly in the nonnegative argument. -/
theorem tendstoUniformlyOn_supPotential_zero_sub {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (K : ℝ) :
    TendstoUniformlyOn (fun q x => supPotential θ q 0 - supPotential θ q x) (stableScale θ)
      (𝓝[>] 0) (Icc 0 K) := by
  let L := max K 0
  have hL : 0 ≤ L := le_max_right _ _
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    (continuousOn_stableSeries_rate_argument hθ L).norm
  have hbound (q y : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc 0 L) :
      ‖stableSeries θ q y‖ ≤ M := hM (mem_image_of_mem
        (fun p : ℝ × ℝ => ‖stableSeries θ p.1 p.2‖)
        (show (q, y) ∈ Icc (0 : ℝ) 1 ×ˢ Icc 0 L from ⟨hq, hy⟩))
  have hM0 : 0 ≤ M := (norm_nonneg (stableSeries θ 0 0)).trans
    (hbound 0 0 ⟨le_rfl, zero_le_one⟩ ⟨le_rfl, hL⟩)
  have hroot : Tendsto (fun q : ℝ => q ^ (1 / θ)) (𝓝[>] 0) (𝓝 0) := by
    have hp : 0 < 1 / θ := div_pos zero_lt_one (by linarith [hθ.1])
    simpa only [Real.zero_rpow hp.ne'] using
      ((Real.continuousAt_rpow_const 0 (1 / θ) (Or.inr hp.le)).tendsto.mono_left
        nhdsWithin_le_nhds)
  have hrem : Tendsto (fun q : ℝ => q ^ (1 / θ) * (M * L)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hroot.mul_const (M * L)
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hW := (Metric.tendstoUniformlyOn_iff.1 (tendstoUniformlyOn_stableSeries_zero hθ K))
    (δ / 2) (half_pos hδ)
  have hsmall := hrem.eventually (Iio_mem_nhds (half_pos hδ))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds, hW, hsmall]
    with q hq hq1 hWq hsmallq
  intro x hx
  have hI : ‖∫ y in Ioc 0 x, stableSeries θ q y‖ ≤ M * L := by
    have hh := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc 0 x)
      (f := stableSeries θ q) (by simp) (fun y hy => hbound q y ⟨hq.le, hq1.le⟩
        ⟨hy.1.le, hy.2.trans (hx.2.trans (le_max_left _ _))⟩)
    have hh' : ‖∫ y in Ioc 0 x, stableSeries θ q y‖ ≤ M * x := by
      simpa only [Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hx.1] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_left (hx.2.trans (le_max_left _ _)) hM0)
  have hr : |q ^ (1 / θ) * ∫ y in Ioc 0 x, stableSeries θ q y| ≤ q ^ (1 / θ) * (M * L) := by
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hq _)]
    rw [Real.norm_eq_abs] at hI
    exact mul_le_mul_of_nonneg_left hI (Real.rpow_pos_of_pos hq _).le
  rw [supPotential_zero_sub hθ hq hx.1, Real.dist_eq]
  calc
    _ = |(stableScale θ x - stableSeries θ q x) +
        q ^ (1 / θ) * ∫ y in Ioc 0 x, stableSeries θ q y| := by
      congr 1
      ring
    _ ≤ |stableScale θ x - stableSeries θ q x| +
        |q ^ (1 / θ) * ∫ y in Ioc 0 x, stableSeries θ q y| := abs_add_le _ _
    _ ≤ |stableScale θ x - stableSeries θ q x| + q ^ (1 / θ) * (M * L) := add_le_add (le_refl _) hr
    _ < δ := by
      have hh := hWq x hx
      rw [Real.dist_eq] at hh
      linarith

end BGW.StableTrees
