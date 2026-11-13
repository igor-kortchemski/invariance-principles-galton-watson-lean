/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcess
public import BGW.StableTrees.StablePassageSubordinator
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Exponential tail for a fresh infimum depth

The first-passage Laplace transform gives the strict tail. Approaching the barrier from
below gives the weak tail, without assumptions about atoms of the infimum law.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The strict infimum-depth tail is controlled by the first-passage Laplace transform. -/
theorem measure_depth_gt_le_exp {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (r : ℝ≥0)
    {b : ℝ≥0} (hb : 0 < b) {q : ℝ} (hq : 0 ≤ q) :
    (stableLocalLaw θ : Measure DLoc) {f | (b : ℝ) < -runningInfLoc f r} ≤
      ENNReal.ofReal (Real.exp (q * r - (b : ℝ) * q ^ (1 / θ))) := by
  let T (f : DLoc) : ℝ := ((firstPassageBelow b f).untopD 0 : ℝ≥0)
  have hT : Measurable T := measurable_coe_nnreal_real.comp
    ((isStoppingTime_firstPassageBelow b).measurable'.untopD 0)
  have hF : Measurable (fun f => ENNReal.ofReal (Real.exp (q * r - q * T f))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.sub (measurable_const.mul hT)))
  have hbnd := meas_le_lintegral₀ (μ := (stableLocalLaw θ : Measure DLoc))
    hF.aemeasurable (s := {f | (b : ℝ) < -runningInfLoc f r}) (by
      intro f hf
      change (b : ℝ) < -runningInfLoc f r at hf
      have hpass : firstPassageBelow b f ≤ (r : WithTop ℝ≥0) :=
        (runningInf_lt_sandwich b r f).2 (by linarith only [hf])
      have htr : T f ≤ (r : ℝ) := by exact_mod_cast (WithTop.untopD_le hpass)
      rw [ENNReal.one_le_ofReal]
      exact Real.one_le_exp (by nlinarith only [hq, htr]))
  calc
    _ ≤ ∫⁻ f, ENNReal.ofReal (Real.exp (q * r - q * T f))
        ∂(stableLocalLaw θ : Measure DLoc) := hbnd
    _ = ENNReal.ofReal (Real.exp (q * r)) *
        ∫⁻ f, ENNReal.ofReal (Real.exp (-q * T f))
          ∂(stableLocalLaw θ : Measure DLoc) := by
      simp_rw [sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _),
        neg_mul]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.exp (q * r - (b : ℝ) * q ^ (1 / θ))) := by
      rw [lintegral_exp_neg_firstPassageBelow hθ hb hq, ← ENNReal.ofReal_mul
        (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring

/-- The weak infimum-depth tail, including the zero barrier, has the same exponential bound. -/
theorem measure_depth_ge_le_exp {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (r b : ℝ≥0)
    {q : ℝ} (hq : 0 ≤ q) :
    (stableLocalLaw θ : Measure DLoc) {f | (b : ℝ) ≤ -runningInfLoc f r} ≤
      ENNReal.ofReal (Real.exp (q * r - (b : ℝ) * q ^ (1 / θ))) := by
  by_cases hb : b = 0
  · subst b
    apply prob_le_one.trans
    simp only [NNReal.coe_zero, zero_mul, sub_zero, ENNReal.one_le_ofReal]
    exact Real.one_le_exp (mul_nonneg hq r.2)
  have hbpos : 0 < b := pos_iff_ne_zero.mpr hb
  have : (𝓝[<] b).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hbpos⟩
  have hc : Continuous (fun a : ℝ≥0 =>
      ENNReal.ofReal (Real.exp (q * r - (a : ℝ) * q ^ (1 / θ)))) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have hlim : Tendsto (fun a : ℝ≥0 =>
      ENNReal.ofReal (Real.exp (q * r - (a : ℝ) * q ^ (1 / θ)))) (𝓝[<] b)
        (𝓝 (ENNReal.ofReal (Real.exp (q * r - (b : ℝ) * q ^ (1 / θ))))) :=
    hc.continuousAt.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hbpos] with a ha
  exact (measure_mono (fun f hf => (show (a : ℝ) < b from ha.2).trans_le hf)).trans
    (measure_depth_gt_le_exp hθ r ha.1 hq)

end BGW.StableTrees
