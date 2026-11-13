/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialConvolution

/-!
# Bounds and regularity of occupation potentials

The occupation convolution is a weighted average of a uniformly continuous tail potential.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace BGW.StableTrees

/-- The supremum potential is uniformly continuous on all real arguments. -/
theorem uniformContinuous_supPotential {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    UniformContinuous (supPotential θ q) :=
  (@Real.uniformContinuous_const_mul (q ^ (1 / θ) / q)).comp (uniformContinuous_supExpTail hθ hq)

/-- The supremum potential is continuous on all real arguments. -/
theorem continuous_supPotential {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    Continuous (supPotential θ q) := (uniformContinuous_supPotential hθ hq).continuous

/-- Negative initial arguments are aliases of the zero start. -/
theorem supOccupationResolvent_eq_max (θ q ε y : ℝ) :
    supOccupationResolvent θ q ε y = supOccupationResolvent θ q ε (max y 0) := by
  by_cases hy : 0 ≤ y
  · rw [max_eq_left hy]
  · simp only [supOccupationResolvent, reflectedResolvent, max_eq_right (not_le.mp hy).le,
      Real.toNNReal_of_nonpos (not_le.mp hy).le, Real.toNNReal_zero]

private theorem integrable_convolution {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    (ε y : ℝ) : IntegrableOn (fun r => Real.exp (-(q ^ (1 / θ) * (ε - r))) *
      supPotential θ q (y - r)) (Ioc 0 ε) := by
  have hc : Continuous (fun r => Real.exp (-(q ^ (1 / θ) * (ε - r))) *
      supPotential θ q (y - r)) :=
    ((continuous_const.mul (continuous_const.sub continuous_id)).neg.rexp).mul
      ((continuous_supPotential hθ hq).comp (continuous_const.sub continuous_id))
  exact hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self

private theorem continuous_convolution {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    (ε : ℝ) : Continuous (fun y => ε⁻¹ * ∫ r in Ioc 0 ε,
      Real.exp (-(q ^ (1 / θ) * (ε - r))) * supPotential θ q (y - r)) := by
  have hc : Continuous (fun y => ∫ r in Icc 0 ε,
      Real.exp (-(q ^ (1 / θ) * (ε - r))) * supPotential θ q (y - r)) :=
    continuous_parametric_integral_of_continuous
      (f := fun y r : ℝ => Real.exp (-(q ^ (1 / θ) * (ε - r))) * supPotential θ q (y - r))
      (((continuous_const.mul (continuous_const.sub continuous_snd)).neg.rexp).mul
        ((continuous_supPotential hθ hq).comp (continuous_fst.sub continuous_snd))) isCompact_Icc
  have he : (fun y => ∫ r in Icc 0 ε,
      Real.exp (-(q ^ (1 / θ) * (ε - r))) * supPotential θ q (y - r)) =
      (fun y => ∫ r in Ioc 0 ε,
        Real.exp (-(q ^ (1 / θ) * (ε - r))) * supPotential θ q (y - r)) := by
    funext y
    exact integral_Icc_eq_integral_Ioc
  rw [he] at hc
  exact hc.const_mul _

private theorem convolution_weight_mem {q ε r θ : ℝ} (hq : 0 < q) (hr : r ≤ ε) :
    Real.exp (-(q ^ (1 / θ) * (ε - r))) ∈ Icc (0 : ℝ) 1 := by
  refine ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 ?_⟩
  exact neg_nonpos.mpr (mul_nonneg (Real.rpow_pos_of_pos hq _).le (sub_nonneg.mpr hr))

/-- `0 ≤ u^q_ε ≤ Φ/q`, on all of `ℝ`. -/
theorem supOccupationResolvent_mem_Icc {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    supOccupationResolvent θ q ε y ∈ Icc (0 : ℝ) (q ^ (1 / θ) / q) := by
  rw [supOccupationResolvent_eq_max θ q ε y, supOccupationResolvent_eq hθ hq hε (le_max_right _ _)]
  have hb (r : ℝ) (hr : r ∈ Ioc 0 ε) :
      Real.exp (-(q ^ (1 / θ) * (ε - r))) * supPotential θ q (max y 0 - r) ∈
        Icc (0 : ℝ) (q ^ (1 / θ) / q) := by
    obtain ⟨hw0, hw1⟩ := convolution_weight_mem hq hr.2
    obtain ⟨h0, h1⟩ := supPotential_mem_Icc hθ hq (max y 0 - r)
    exact ⟨mul_nonneg hw0 h0, (mul_le_mul_of_nonneg_right hw1 h0).trans (by simpa using h1)⟩
  refine ⟨mul_nonneg (inv_pos.mpr hε).le (integral_nonneg_of_ae ?_), ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact (hb r hr).1
  · have hi := setIntegral_mono_on (integrable_convolution hθ hq ε (max y 0))
      (integrableOn_const (by simp)) measurableSet_Ioc (fun r hr => (hb r hr).2)
    have hm := mul_le_mul_of_nonneg_left hi (inv_pos.mpr hε).le
    simpa only [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal hε.le, ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul] using hm

/-- The occupation resolvent is nonincreasing in the nonnegative start. -/
theorem antitoneOn_supOccupationResolvent {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    {ε : ℝ} (hε : 0 < ε) : AntitoneOn (supOccupationResolvent θ q ε) (Ici 0) := by
  intro a ha b hb hab
  rw [supOccupationResolvent_eq hθ hq hε hb, supOccupationResolvent_eq hθ hq hε ha]
  apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hε).le
  apply setIntegral_mono_on (integrable_convolution hθ hq ε b) (integrable_convolution hθ hq ε a)
    measurableSet_Ioc
  intro r _
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left
    (antitone_supExpTail hθ hq (sub_le_sub_right hab r)) (by positivity)

/-- Continuity in the nonnegative initial state. -/
theorem continuousOn_supOccupationResolvent {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    {ε : ℝ} (hε : 0 < ε) : ContinuousOn (supOccupationResolvent θ q ε) (Ici 0) := by
  apply (continuous_convolution hθ hq ε).continuousOn.congr
  intro y hy
  exact supOccupationResolvent_eq hθ hq hε hy

end BGW.StableTrees
