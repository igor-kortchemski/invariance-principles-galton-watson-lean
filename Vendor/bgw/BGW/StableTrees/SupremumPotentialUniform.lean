/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialOccupation

/-!
# Uniform convergence of occupation potentials

Uniform continuity of the extended supremum potential controls all initial states
at once in the convolution formula.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace BGW.StableTrees

/-- Occupation potentials converge uniformly over all nonnegative starts. -/
theorem tendstoUniformlyOn_supOccupationResolvent {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) :
    TendstoUniformlyOn (fun ε y => supOccupationResolvent θ q ε y) (supPotential θ q)
      (𝓝[>] 0) (Ici 0) := by
  let Φ := q ^ (1 / θ)
  let C := Φ / q
  have hΦ : 0 < Φ := Real.rpow_pos_of_pos hq _
  have hC : 0 < C := div_pos hΦ hq
  have hscalar : Tendsto (fun ε : ℝ => C * (1 - Real.exp (-Φ * ε))) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => C * (1 - Real.exp (-Φ * ε))) := by fun_prop
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  obtain ⟨a, ha, hmod⟩ := Metric.uniformContinuous_iff.1 (uniformContinuous_supPotential hθ hq)
    (δ / 4) (by positivity)
  have hs := hscalar.eventually (Iio_mem_nhds (by positivity : 0 < δ / 4))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds, hs] with ε hε hεa hsε
  intro y hy
  have hi : IntegrableOn (fun r => Real.exp (-(Φ * (ε - r))) * supPotential θ q (y - r))
      (Ioc 0 ε) := by
    have hc : Continuous (fun r => Real.exp (-(Φ * (ε - r))) * supPotential θ q (y - r)) :=
      ((continuous_const.mul (continuous_const.sub continuous_id)).neg.rexp).mul
        ((continuous_supPotential hθ hq).comp (continuous_const.sub continuous_id))
    exact hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have he : supOccupationResolvent θ q ε y - supPotential θ q y =
      ε⁻¹ * ∫ r in Ioc 0 ε, (Real.exp (-(Φ * (ε - r))) * supPotential θ q (y - r) -
        supPotential θ q y) := by
    rw [supOccupationResolvent_eq hθ hq hε hy,
      integral_sub hi (integrableOn_const (by simp)), setIntegral_const]
    simp only [Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hε.le, smul_eq_mul]
    dsimp [Φ]
    field_simp [hε.ne']
  have hbound (r : ℝ) (hr : r ∈ Ioc 0 ε) :
      ‖Real.exp (-(Φ * (ε - r))) * supPotential θ q (y - r) - supPotential θ q y‖ ≤ δ / 2 := by
    have hdiff : |supPotential θ q (y - r) - supPotential θ q y| < δ / 4 := by
      have hh : dist (y - r) y < a := by
        rw [Real.dist_eq, show y - r - y = -r by ring, abs_neg, abs_of_nonneg hr.1.le]
        exact hr.2.trans_lt hεa
      simpa only [Real.dist_eq] using hmod hh
    have hw0 : 0 < Real.exp (-(Φ * (ε - r))) := Real.exp_pos _
    have hw1 : Real.exp (-(Φ * (ε - r))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hr.2])
    have hwlo : Real.exp (-Φ * ε) ≤ Real.exp (-(Φ * (ε - r))) :=
      Real.exp_le_exp.2 (by nlinarith [hr.1])
    obtain ⟨hH0, hH1⟩ := supPotential_mem_Icc hθ hq y
    have hfirst : |Real.exp (-(Φ * (ε - r))) *
        (supPotential θ q (y - r) - supPotential θ q y)| ≤ δ / 4 := by
      rw [abs_mul, abs_of_pos hw0]
      exact (mul_le_mul_of_nonneg_left hdiff.le hw0.le).trans
        (by nlinarith)
    have hsecond : |(Real.exp (-(Φ * (ε - r))) - 1) * supPotential θ q y| ≤
        C * (1 - Real.exp (-Φ * ε)) := by
      rw [abs_mul, abs_of_nonpos (by linarith : Real.exp (-(Φ * (ε - r))) - 1 ≤ 0),
        abs_of_nonneg hH0]
      dsimp [C, Φ] at hH1 ⊢
      nlinarith
    rw [Real.norm_eq_abs]
    calc
      _ = |Real.exp (-(Φ * (ε - r))) * (supPotential θ q (y - r) - supPotential θ q y) +
          (Real.exp (-(Φ * (ε - r))) - 1) * supPotential θ q y| := by congr 1; ring
      _ ≤ |Real.exp (-(Φ * (ε - r))) * (supPotential θ q (y - r) - supPotential θ q y)| +
          |(Real.exp (-(Φ * (ε - r))) - 1) * supPotential θ q y| := abs_add_le _ _
      _ ≤ δ / 4 + C * (1 - Real.exp (-Φ * ε)) := add_le_add hfirst hsecond
      _ ≤ δ / 2 := by linarith
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc 0 ε)
    (f := fun r => Real.exp (-(Φ * (ε - r))) * supPotential θ q (y - r) - supPotential θ q y)
    (by simp) hbound
  have hb' : |supOccupationResolvent θ q ε y - supPotential θ q y| ≤ δ / 2 := by
    rw [he, abs_mul, abs_of_pos (inv_pos.mpr hε)]
    have hh := mul_le_mul_of_nonneg_left hb (inv_pos.mpr hε).le
    simpa only [Real.norm_eq_abs, Measure.real, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal hε.le, mul_comm (δ / 2) ε, ← mul_assoc,
      inv_mul_cancel₀ hε.ne', one_mul] using hh
  rw [Real.dist_eq, abs_sub_comm]
  exact hb'.trans_lt (by linarith)

/-- Cauchy control at rate one is uniform over every real initial argument. -/
theorem exists_forall_abs_supOccupationResolvent_sub_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ a : ℝ, 0 < a ∧ ∀ ε η : ℝ, 0 < ε → ε < a → 0 < η → η < a → ∀ y : ℝ,
      |supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y| ≤ δ := by
  have he := (Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_supOccupationResolvent hθ zero_lt_one)) (δ / 2) (half_pos hδ)
  obtain ⟨a, ha, hsub⟩ := Metric.mem_nhdsWithin_iff.1 he
  refine ⟨a, ha, fun ε η hε hεa hη hηa y => ?_⟩
  have hεb : ε ∈ Metric.ball (0 : ℝ) a ∩ Ioi 0 := by
    refine ⟨?_, hε⟩
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε] using hεa
  have hηb : η ∈ Metric.ball (0 : ℝ) a ∩ Ioi 0 := by
    refine ⟨?_, hη⟩
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hη] using hηa
  have hbε := hsub hεb (max y 0) (le_max_right _ _)
  have hbη := hsub hηb (max y 0) (le_max_right _ _)
  rw [Real.dist_eq] at hbε hbη
  rw [supOccupationResolvent_eq_max θ 1 ε y, supOccupationResolvent_eq_max θ 1 η y]
  have ht := abs_sub_le (supOccupationResolvent θ 1 ε (max y 0)) (supPotential θ 1 (max y 0))
    (supOccupationResolvent θ 1 η (max y 0))
  rw [abs_sub_comm (supOccupationResolvent θ 1 ε (max y 0)) (supPotential θ 1 (max y 0))] at ht
  linarith

end BGW.StableTrees
