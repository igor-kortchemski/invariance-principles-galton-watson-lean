/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StablePassageSubordinator
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Passage-time tails from the Laplace transform

Markov's inequality applied to `1 - exp(-T / y)` yields the stable power tail needed for
dyadic left-slope estimates. The passage law is read on its finite nonnegative carrier.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- A polynomial upper bound for strict passage tails, uniform in the level and threshold. -/
theorem measure_passageTime_gt_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0)
    {y : ℝ} (hy : 0 < y) :
    (stableLocalLaw θ : Measure DLoc) {f | y < (passageTime x f : ℝ)} ≤
      ENNReal.ofReal (((x : ℝ) * y ^ (-1 / θ)) / (1 - Real.exp (-1))) := by
  let P : Measure DLoc := stableLocalLaw θ
  let Z (f : DLoc) : ℝ := passageTime x f
  let F (f : DLoc) : ℝ := 1 - Real.exp (-(y⁻¹ * Z f))
  let a : ℝ := 1 - Real.exp (-1)
  have ha : 0 < a := sub_pos.mpr (by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (-1 : ℝ) < 0))
  have hZ : Measurable Z := (measurable_passageTime x).coe_nnreal_real
  have hexp : Integrable (fun f => Real.exp (-(y⁻¹ * Z f))) P := by
    apply (integrable_const (1 : ℝ)).mono'
      ((hZ.const_mul y⁻¹).neg.exp).aestronglyMeasurable
    filter_upwards with f
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (inv_nonneg.mpr hy.le)
      (passageTime x f).2))
  have hF : Integrable F P := (integrable_const 1).sub hexp
  have hF0 : 0 ≤ᵐ[P] F := ae_of_all _ fun f => sub_nonneg.mpr
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr
      (mul_nonneg (inv_nonneg.mpr hy.le) (passageTime x f).2)))
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hF0 hF a
  have hincl : {f : DLoc | y < Z f} ⊆ {f | a ≤ F f} := by
    intro f hf
    change 1 - Real.exp (-1) ≤ 1 - Real.exp (-(y⁻¹ * Z f))
    apply sub_le_sub_left
    apply Real.exp_le_exp.mpr
    have hprod : 1 < y⁻¹ * Z f := by
      rw [← div_eq_inv_mul]
      exact (one_lt_div hy).mpr hf
    linarith only [hprod]
  have hlap : (∫ f, Real.exp (-(y⁻¹ * Z f)) ∂P) =
      Real.exp (-(x : ℝ) * (y⁻¹) ^ (1 / θ)) := by
    have hh := integral_exp_neg_passageLaw hθ x (inv_nonneg.mpr hy.le)
    rw [passageLaw, integral_map (measurable_passageTime x).coe_nnreal_real.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun t : ℝ => Real.exp (-y⁻¹ * t))
        ((stableLocalLaw θ : Measure DLoc).map (fun f => (passageTime x f : ℝ))))] at hh
    simpa only [neg_mul, P, Z] using hh
  have hreal : a * (P {f | y < Z f}).toReal ≤ (x : ℝ) * y ^ (-1 / θ) := by
    calc
      _ ≤ a * (P {f | a ≤ F f}).toReal := mul_le_mul_of_nonneg_left
        (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hincl)) ha.le
      _ ≤ ∫ f, F f ∂P := hmarkov
      _ = 1 - Real.exp (-(x : ℝ) * (y⁻¹) ^ (1 / θ)) := by
        rw [show F = fun f => 1 - Real.exp (-(y⁻¹ * Z f)) from rfl,
          integral_sub (integrable_const 1) hexp, integral_const, hlap]
        simp
      _ ≤ (x : ℝ) * y ^ (-1 / θ) := by
        have he := Real.add_one_le_exp (-(x : ℝ) * (y⁻¹) ^ (1 / θ))
        rw [Real.inv_rpow hy.le, ← Real.rpow_neg hy.le] at he
        have hp : -(1 / θ) = -1 / θ := by ring
        rw [hp] at he
        rw [Real.inv_rpow hy.le, ← Real.rpow_neg hy.le, hp]
        linarith only [he]
  rw [← ENNReal.ofReal_toReal (measure_ne_top P {f | y < Z f})]
  apply ENNReal.ofReal_le_ofReal
  exact (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hreal)

/-- Stationary passage increments satisfy the same polynomial tail bound. -/
theorem measure_passageIncrement_gt_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a b : ℝ≥0)
    {y : ℝ} (hy : 0 < y) :
    (stableLocalLaw θ : Measure DLoc)
      {f | y < (passageTime (a + b) f : ℝ) - (passageTime a f : ℝ)} ≤
        ENNReal.ofReal (((b : ℝ) * y ^ (-1 / θ)) / (1 - Real.exp (-1))) := by
  have hm : Measurable (fun f : DLoc =>
      (passageTime (a + b) f : ℝ) - (passageTime a f : ℝ)) :=
    (measurable_passageTime (a + b)).coe_nnreal_real.sub
      (measurable_passageTime a).coe_nnreal_real
  calc
    _ = ((stableLocalLaw θ : Measure DLoc).map (fun f =>
        (passageTime (a + b) f : ℝ) - (passageTime a f : ℝ))) (Ioi y) :=
      (Measure.map_apply hm measurableSet_Ioi).symm
    _ = passageLaw θ b (Ioi y) := by rw [map_passageIncrement hθ a b]
    _ = (stableLocalLaw θ : Measure DLoc) {f | y < (passageTime b f : ℝ)} :=
      Measure.map_apply (measurable_passageTime b).coe_nnreal_real measurableSet_Ioi
    _ ≤ _ := measure_passageTime_gt_le hθ b hy

end BGW.StableTrees
