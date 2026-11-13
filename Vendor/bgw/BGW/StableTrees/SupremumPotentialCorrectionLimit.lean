/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialAsymptotics
public import BGW.StableTrees.SupremumPotentialUniform
public import BGW.StableTrees.SupremumPotentialCorrection
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The zero-rate limit of the occupation correction

The scalar boundary term is a derivative of an averaged exponential at zero.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace BGW.StableTrees

private noncomputable def averageExp (ε z : ℝ) : ℝ :=
  ε⁻¹ * ∫ r in Ioc 0 ε, Real.exp (-(z * (ε - r)))

private theorem averageExp_zero {ε : ℝ} (hε : 0 < ε) : averageExp ε 0 = 1 := by
  simp only [averageExp, zero_mul, neg_zero, Real.exp_zero, setIntegral_const,
    smul_eq_mul, mul_one, Measure.real, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal hε.le, inv_mul_cancel₀ hε.ne']

private theorem hasDerivAt_averageExp_zero {ε : ℝ} (hε : 0 < ε) :
    HasDerivAt (averageExp ε) (-ε / 2) 0 := by
  let F := fun z r : ℝ => Real.exp (-(z * (ε - r)))
  let F' := fun z r : ℝ => -(ε - r) * Real.exp (-(z * (ε - r)))
  have hd (z r : ℝ) : HasDerivAt (fun z => F z r) (F' z r) z := by
    change HasDerivAt (fun z => Real.exp (-(z * (ε - r))))
      (-(ε - r) * Real.exp (-(z * (ε - r)))) z
    convert (((hasDerivAt_id z).mul_const (ε - r)).neg.exp) using 1
    · simp only [Pi.neg_apply, id_eq]
    · simp only [Pi.neg_apply, id_eq]
      ring
  have hInt := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc 0 ε)) (F := F) (F' := F') (x₀ := 0)
    (bound := fun _ => ε * Real.exp ε) (s := Ioo (-1 : ℝ) 1)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall (fun z =>
      (show Continuous (F z) by dsimp [F]; fun_prop).aestronglyMeasurable))
    (by simpa only [F, zero_mul, neg_zero, Real.exp_zero, IntegrableOn] using
      (integrableOn_const (μ := volume) (C := (1 : ℝ)) (s := Ioc 0 ε) (by simp)))
    (show AEStronglyMeasurable (F' 0) (volume.restrict (Ioc 0 ε)) from
      (show Continuous (F' 0) by dsimp [F']; fun_prop).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      intro z hz
      have hs0 : 0 ≤ ε - r := sub_nonneg.mpr hr.2
      have hsε : ε - r ≤ ε := by linarith [hr.1]
      have harg : -(z * (ε - r)) ≤ ε := by nlinarith [hz.1]
      dsimp [F']
      rw [abs_mul, abs_neg, abs_of_nonneg hs0, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul hsε (Real.exp_le_exp.2 harg) (Real.exp_pos _).le hε.le)
    (integrableOn_const (by simp))
    (ae_of_all _ (fun r z _ => hd z r))
  have hh := hInt.2.const_mul ε⁻¹
  change HasDerivAt (fun z => ε⁻¹ * ∫ r in Ioc 0 ε, Real.exp (-(z * (ε - r)))) (-ε / 2) 0
  convert hh using 1
  dsimp only [F']
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, neg_sub]
  rw [← intervalIntegral.integral_of_le hε.le,
    intervalIntegral.integral_sub (f := fun r : ℝ => r) (g := fun _ : ℝ => ε)
      (continuous_id.intervalIntegrable (μ := volume) 0 ε) intervalIntegrable_const,
    integral_id, intervalIntegral.integral_const]
  simp only [zero_pow two_ne_zero, sub_zero, smul_eq_mul]
  field_simp
  ring

private theorem tendsto_scalar_correction {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun q : ℝ => supPotential θ q 0 * (averageExp ε (q ^ (1 / θ)) - 1))
      (𝓝[>] 0) (𝓝 (-(if θ = 2 then ε / 2 else 0))) := by
  have hp : 0 < 1 / θ := div_pos zero_lt_one (by linarith [hθ.1])
  have hr : Tendsto (fun q : ℝ => q ^ (1 / θ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hp.ne'] using
      ((Real.continuousAt_rpow_const 0 (1 / θ) (Or.inr hp.le)).tendsto.mono_left nhdsWithin_le_nhds)
  have hr' : Tendsto (fun q : ℝ => q ^ (1 / θ)) (𝓝[>] 0) (𝓝[>] 0) :=
    by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact hr
      · filter_upwards [self_mem_nhdsWithin] with q hq
        exact Real.rpow_pos_of_pos hq _
  have hs := (hasDerivAt_averageExp_zero hε).tendsto_slope_zero_right.comp hr'
  simp only [zero_add, averageExp_zero hε, smul_eq_mul] at hs
  have ht := (tendsto_rpow_two_div_sub_one hθ).mul hs
  have he : (fun q : ℝ => q ^ (2 / θ - 1) *
      ((q ^ (1 / θ))⁻¹ * (averageExp ε (q ^ (1 / θ)) - 1))) =ᶠ[𝓝[>] 0]
      (fun q => supPotential θ q 0 * (averageExp ε (q ^ (1 / θ)) - 1)) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    rw [← supPotential_zero_mul hθ hq]
    calc
      _ = (q ^ (1 / θ) * (q ^ (1 / θ))⁻¹) *
          (supPotential θ q 0 * (averageExp ε (q ^ (1 / θ)) - 1)) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (Real.rpow_pos_of_pos hq _).ne', one_mul]
  have hh := ht.congr' he
  by_cases h : θ = 2 <;>
    simpa only [h, ite_true, ite_false, one_mul, zero_mul, neg_zero, neg_div] using hh

private theorem potential_difference_nonpos {θ q z : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (hq : 0 < q) (hz : z ≤ 0) : supPotential θ q 0 - supPotential θ q z = 0 := by
  rcases eq_or_lt_of_le hz with rfl | hz
  · exact sub_self _
  · rw [supPotential_zero hθ hq]
    simp only [supPotential, supExpTail, ite_eq_left hz, mul_one, sub_self]

private theorem correction_decomposition {θ q ε y : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (hq : 0 < q) (hε : 0 < ε) (hy : 0 ≤ y) :
    supOccupationResolvent θ q ε y - supPotential θ q y =
      supPotential θ q 0 * (averageExp ε (q ^ (1 / θ)) - 1) +
        (supPotential θ q 0 - supPotential θ q y) - ε⁻¹ *
          ∫ r in Ioc 0 ε, Real.exp (-(q ^ (1 / θ) * (ε - r))) *
            (supPotential θ q 0 - supPotential θ q (y - r)) := by
  have hw : Continuous (fun r : ℝ => Real.exp (-(q ^ (1 / θ) * (ε - r)))) := by fun_prop
  have hh : Continuous (fun r : ℝ => supPotential θ q (y - r)) :=
    (continuous_supPotential hθ hq).comp (continuous_const.sub continuous_id)
  have hwI := hw.continuousOn.integrableOn_Icc (μ := volume) (a := 0) (b := ε)
    |>.mono_set Ioc_subset_Icc_self
  have hwhI := (hw.mul hh).continuousOn.integrableOn_Icc (μ := volume) (a := 0) (b := ε)
    |>.mono_set Ioc_subset_Icc_self
  change IntegrableOn (fun r => Real.exp (-(q ^ (1 / θ) * (ε - r))) *
    supPotential θ q (y - r)) (Ioc 0 ε) at hwhI
  have he : (fun r => Real.exp (-(q ^ (1 / θ) * (ε - r))) *
      (supPotential θ q 0 - supPotential θ q (y - r))) =
      (fun r => supPotential θ q 0 * Real.exp (-(q ^ (1 / θ) * (ε - r))) -
        Real.exp (-(q ^ (1 / θ) * (ε - r))) * supPotential θ q (y - r)) := by funext r; ring
  rw [supOccupationResolvent_eq hθ hq hε hy, he,
    integral_sub (hwI.const_mul _) hwhI, integral_const_mul, averageExp]
  ring

private theorem tendstoUniformlyOn_correction {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) (K : ℝ) :
    TendstoUniformlyOn (fun q y => supOccupationResolvent θ q ε y - supPotential θ q y)
      (supCorrection θ ε) (𝓝[>] 0) (Icc 0 K) := by
  let L := max K 0
  let β := -(if θ = 2 then ε / 2 else 0)
  have hL : 0 ≤ L := le_max_right _ _
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image
    (continuous_stableScale hθ.1).norm.continuousOn (K := Icc (-ε) L)
  have hbound (z : ℝ) (hz : z ∈ Icc (-ε) L) : |stableScale θ z| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM (mem_image_of_mem
      (fun z : ℝ => ‖stableScale θ z‖) hz)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hbound 0 ⟨by linarith, hL⟩)
  have hp : 0 < 1 / θ := div_pos zero_lt_one (by linarith [hθ.1])
  have hr : Tendsto (fun q : ℝ => q ^ (1 / θ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hp.ne'] using
      ((Real.continuousAt_rpow_const 0 (1 / θ) (Or.inr hp.le)).tendsto.mono_left nhdsWithin_le_nhds)
  have hscalar : Tendsto (fun q : ℝ => M * (1 - Real.exp (-(q ^ (1 / θ) * ε))))
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun z : ℝ => M * (1 - Real.exp (-(z * ε)))) := by fun_prop
    simpa only [Function.comp_def, zero_mul, neg_zero, Real.exp_zero, sub_self, mul_zero] using
      (hc.tendsto 0).comp hr
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hbq := (Metric.tendstoUniformlyOn_iff.1 (tendstoUniformlyOn_supPotential_zero_sub hθ L))
    (δ / 8) (by positivity)
  have hsc := (Metric.tendsto_nhds.1 (tendsto_scalar_correction hθ hε)) (δ / 4) (by positivity)
  have hsm := hscalar.eventually (Iio_mem_nhds (by positivity : 0 < δ / 8))
  filter_upwards [self_mem_nhdsWithin, hbq, hsc, hsm] with q hq hBq hSc hSm
  intro y hy
  have hΦ : 0 < q ^ (1 / θ) := Real.rpow_pos_of_pos hq _
  have hB (z : ℝ) (hz : z ≤ L) :
      |(supPotential θ q 0 - supPotential θ q z) - stableScale θ z| ≤ δ / 8 := by
    by_cases hz0 : z ≤ 0
    · rw [potential_difference_nonpos hθ hq hz0, stableScale_eq_zero hθ.1 hz0]
      simp only [sub_self, abs_zero]
      positivity
    · have hh := hBq z ⟨(not_le.mp hz0).le, hz⟩
      rw [Real.dist_eq, abs_sub_comm] at hh
      exact hh.le
  have hIntegrand (r : ℝ) (hr : r ∈ Ioc 0 ε) :
      ‖Real.exp (-(q ^ (1 / θ) * (ε - r))) *
          (supPotential θ q 0 - supPotential θ q (y - r)) - stableScale θ (y - r)‖ ≤ δ / 4 := by
    let w := Real.exp (-(q ^ (1 / θ) * (ε - r)))
    have hw0 : 0 < w := Real.exp_pos _
    have hw1 : w ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hr.2])
    have hwlo : Real.exp (-(q ^ (1 / θ) * ε)) ≤ w := Real.exp_le_exp.2 (by nlinarith [hr.1])
    have hshift : y - r ≤ L := by linarith [hy.2, le_max_left K 0, hr.1]
    have hd := hB (y - r) hshift
    have hW := hbound (y - r) ⟨by linarith [hy.1, hr.2], hshift⟩
    have hfirst : |w * ((supPotential θ q 0 - supPotential θ q (y - r)) -
        stableScale θ (y - r))| ≤ δ / 8 := by
      rw [abs_mul, abs_of_pos hw0]
      exact (mul_le_mul_of_nonneg_left hd hw0.le).trans (by nlinarith)
    have hsecond : |(w - 1) * stableScale θ (y - r)| ≤
        M * (1 - Real.exp (-(q ^ (1 / θ) * ε))) := by
      rw [abs_mul, abs_of_nonpos (by linarith : w - 1 ≤ 0)]
      nlinarith
    rw [Real.norm_eq_abs]
    calc
      _ = |w * ((supPotential θ q 0 - supPotential θ q (y - r)) - stableScale θ (y - r)) +
          (w - 1) * stableScale θ (y - r)| := by dsimp [w]; congr 1; ring
      _ ≤ |w * ((supPotential θ q 0 - supPotential θ q (y - r)) - stableScale θ (y - r))| +
          |(w - 1) * stableScale θ (y - r)| := abs_add_le _ _
      _ ≤ δ / 8 + M * (1 - Real.exp (-(q ^ (1 / θ) * ε))) := add_le_add hfirst hsecond
      _ ≤ δ / 4 := by linarith
  have hI := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc 0 ε)
    (f := fun r => Real.exp (-(q ^ (1 / θ) * (ε - r))) *
      (supPotential θ q 0 - supPotential θ q (y - r)) - stableScale θ (y - r)) (by simp) hIntegrand
  have hI' : |ε⁻¹ * ∫ r in Ioc 0 ε, (Real.exp (-(q ^ (1 / θ) * (ε - r))) *
      (supPotential θ q 0 - supPotential θ q (y - r)) - stableScale θ (y - r))| ≤ δ / 4 := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hε)]
    have hh := mul_le_mul_of_nonneg_left hI (inv_pos.mpr hε).le
    simpa only [Real.norm_eq_abs, Measure.real, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal hε.le, mul_comm (δ / 4) ε, ← mul_assoc,
      inv_mul_cancel₀ hε.ne', one_mul] using hh
  have hw : Continuous (fun r : ℝ => Real.exp (-(q ^ (1 / θ) * (ε - r)))) := by fun_prop
  have hbc : Continuous (fun r : ℝ => supPotential θ q 0 - supPotential θ q (y - r)) :=
    continuous_const.sub ((continuous_supPotential hθ hq).comp (continuous_const.sub continuous_id))
  have hBW := (hw.mul hbc).continuousOn.integrableOn_Icc (μ := volume) (a := 0) (b := ε)
    |>.mono_set Ioc_subset_Icc_self
  change IntegrableOn (fun r => Real.exp (-(q ^ (1 / θ) * (ε - r))) *
    (supPotential θ q 0 - supPotential θ q (y - r))) (Ioc 0 ε) at hBW
  have hWc : Continuous (fun r : ℝ => stableScale θ (y - r)) :=
    (continuous_stableScale hθ.1).comp (continuous_const.sub continuous_id)
  have hW : IntegrableOn (fun r : ℝ => stableScale θ (y - r)) (Ioc 0 ε) :=
    hWc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self

  have he : (supOccupationResolvent θ q ε y - supPotential θ q y) - supCorrection θ ε y =
      (supPotential θ q 0 * (averageExp ε (q ^ (1 / θ)) - 1) - β) +
        ((supPotential θ q 0 - supPotential θ q y) - stableScale θ y) -
          ε⁻¹ * ∫ r in Ioc 0 ε, (Real.exp (-(q ^ (1 / θ) * (ε - r))) *
            (supPotential θ q 0 - supPotential θ q (y - r)) - stableScale θ (y - r)) := by
    rw [correction_decomposition hθ hq hε hy.1, supCorrection, integral_sub hBW hW]
    dsimp [β]
    ring
  have hSc' : |supPotential θ q 0 * (averageExp ε (q ^ (1 / θ)) - 1) - β| < δ / 4 := by
    simpa only [Real.dist_eq] using hSc
  have hBy := hB y (hy.2.trans (le_max_left _ _))
  rw [Real.dist_eq, abs_sub_comm, he]
  have htri := abs_sub_le
    ((supPotential θ q 0 * (averageExp ε (q ^ (1 / θ)) - 1) - β) +
      ((supPotential θ q 0 - supPotential θ q y) - stableScale θ y))
    0 (ε⁻¹ * ∫ r in Ioc 0 ε, (Real.exp (-(q ^ (1 / θ) * (ε - r))) *
      (supPotential θ q 0 - supPotential θ q (y - r)) - stableScale θ (y - r)))
  simp only [sub_zero, zero_sub, abs_neg] at htri
  have hadd := abs_add_le (supPotential θ q 0 * (averageExp ε (q ^ (1 / θ)) - 1) - β)
    ((supPotential θ q 0 - supPotential θ q y) - stableScale θ y)
  linarith

/-- The zero-rate occupation correction converges locally uniformly in the nonnegative start. -/
theorem tendstoLocallyUniformlyOn_supOccupationResolvent_sub {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ε : ℝ} (hε : 0 < ε) :
    TendstoLocallyUniformlyOn
      (fun q y => supOccupationResolvent θ q ε y - supPotential θ q y) (supCorrection θ ε)
      (𝓝[>] 0) (Ici 0) := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro x hx
  refine ⟨Icc 0 (x + 1), ?_, tendstoUniformlyOn_correction hθ hε (x + 1)⟩
  exact inter_mem self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by linarith : x < x + 1)))

end BGW.StableTrees
