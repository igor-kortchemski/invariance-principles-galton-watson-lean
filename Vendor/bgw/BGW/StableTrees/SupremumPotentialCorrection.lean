/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialBasic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Continuity and the Brownian case of the supremum correction

The positive-part power representation makes the zero-rate scale continuous.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace BGW.StableTrees

/-- The zero-rate scale is continuous through its zero extension. -/
theorem continuous_stableScale {θ : ℝ} (hθ : 1 < θ) : Continuous (stableScale θ) := by
  have he : stableScale θ = fun x => (max x 0) ^ (θ - 1) / Real.Gamma θ := by
    funext x
    by_cases hx : 0 ≤ x
    · simp [stableScale, hx]
    · simp [stableScale, hx, max_eq_right (not_le.mp hx).le,
        Real.zero_rpow (by linarith : θ - 1 ≠ 0)]
  rw [he]
  exact ((Real.continuous_rpow_const (by linarith : 0 ≤ θ - 1)).comp
    (continuous_id.max continuous_const)).div_const _

/-- Continuity of the correction on nonnegative starting states. -/
theorem continuousOn_supCorrection {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (supCorrection θ ε) (Ici 0) := by
  -- `hε` is part of the stated interface; this holds for every ε.
  have _hε := hε
  have hc : Continuous (fun x => ∫ r in Icc 0 ε, stableScale θ (x - r)) :=
    continuous_parametric_integral_of_continuous
      (f := fun x r : ℝ => stableScale θ (x - r))
      ((continuous_stableScale hθ.1).comp (continuous_fst.sub continuous_snd)) isCompact_Icc
  have he : (fun x => ∫ r in Ioc 0 ε, stableScale θ (x - r)) =
      (fun x => ∫ r in Icc 0 ε, stableScale θ (x - r)) := by
    funext x
    exact integral_Icc_eq_integral_Ioc.symm
  have hc' : Continuous (fun x => ∫ r in Ioc 0 ε, stableScale θ (x - r)) := he.symm ▸ hc
  exact ((continuous_stableScale hθ.1).sub (hc'.const_mul _)).sub continuous_const
    |>.continuousOn

private theorem scale_two (x : ℝ) : stableScale 2 x = max x 0 := by
  by_cases hx : 0 ≤ x
  · norm_num [stableScale, hx]
  · simp [stableScale, hx, max_eq_right (not_le.mp hx).le]

private theorem integral_scale_two_of_le {x b : ℝ} (hb : 0 ≤ b) (hbx : b ≤ x) :
    (∫ r in Ioc 0 b, stableScale 2 (x - r)) = x * b - b ^ 2 / 2 := by
  have he : (∫ r in Ioc 0 b, stableScale 2 (x - r)) = ∫ r in Ioc 0 b, x - r := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    change stableScale 2 (x - r) = x - r
    rw [scale_two, max_eq_left (by linarith [hr.2] : 0 ≤ x - r)]
  rw [he, ← intervalIntegral.integral_of_le hb,
    intervalIntegral.integral_sub (f := fun _ : ℝ => x) (g := fun r : ℝ => r)
      (intervalIntegrable_const) (continuous_id.intervalIntegrable (μ := volume) 0 b),
    intervalIntegral.integral_const, integral_id]
  simp only [sub_zero, zero_pow two_ne_zero, smul_eq_mul]
  ring

/-- Brownian case: `v_ε(y) = -(ε-y)_+² / (2ε)`. -/
theorem supCorrection_two {ε : ℝ} (hε : 0 < ε) {y : ℝ} (hy : 0 ≤ y) :
    supCorrection 2 ε y = -((max (ε - y) 0) ^ 2 / (2 * ε)) := by
  have hscale : stableScale 2 y = y := by rw [scale_two, max_eq_left hy]
  by_cases he : ε ≤ y
  · rw [supCorrection, integral_scale_two_of_le hε.le he, hscale,
      ite_eq_left rfl, max_eq_right (by linarith : ε - y ≤ 0)]
    field_simp
    ring
  · have he' : y ≤ ε := (not_le.mp he).le
    have hi : (∫ r in Ioc 0 ε, stableScale 2 (y - r)) = y ^ 2 / 2 := by
      have hcont : Continuous (fun r => stableScale 2 (y - r)) :=
        (continuous_stableScale (by norm_num : (1 : ℝ) < 2)).comp
          (continuous_const.sub continuous_id)
      have hzero : (∫ r in Ioc y ε, stableScale 2 (y - r)) = 0 := by
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro r hr
        exact stableScale_eq_zero (by norm_num) (by linarith [hr.1])
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable (μ := volume) 0 y)
        (hcont.intervalIntegrable (μ := volume) y ε)
      rw [intervalIntegral.integral_of_le hy, intervalIntegral.integral_of_le he',
        intervalIntegral.integral_of_le hε.le, hzero, add_zero,
        integral_scale_two_of_le hy le_rfl] at hadd
      linarith
    rw [supCorrection, hi, hscale, ite_eq_left rfl,
      max_eq_left (by linarith : 0 ≤ ε - y)]
    field_simp
    ring

private theorem scale_increment {θ y r : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (hy : 0 ≤ y) (hr : 0 ≤ r) :
    stableScale θ y - stableScale θ (y - r) ∈
      Icc (0 : ℝ) (r ^ (θ - 1) / Real.Gamma θ) := by
  have ha : 0 ≤ θ - 1 := by linarith [hθ.1]
  have ha1 : θ - 1 ≤ 1 := by linarith [hθ.2]
  have hg : 0 < Real.Gamma θ := Real.Gamma_pos_of_pos (by linarith [hθ.1])
  by_cases hry : r ≤ y
  · have hd : 0 ≤ y - r := sub_nonneg.mpr hry
    simp only [stableScale, ite_eq_left hy, ite_eq_left hd]
    rw [← sub_div]
    refine ⟨div_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hd (by linarith) ha)) hg.le, ?_⟩
    apply div_le_div_of_nonneg_right _ hg.le
    have hb := Real.rpow_add_le_add_rpow hd hr ha ha1
    rw [sub_add_cancel] at hb
    linarith
  · have hd : y - r ≤ 0 := by linarith
    rw [stableScale_eq_zero hθ.1 hd, sub_zero]
    simp only [stableScale, ite_eq_left hy]
    exact ⟨div_nonneg (Real.rpow_nonneg hy _) hg.le,
      div_le_div_of_nonneg_right (Real.rpow_le_rpow hy (not_le.mp hry).le ha) hg.le⟩

/-- `|v_ε| ≤ (1/Γ(θ) + 1/2) ε^{θ-1}` for every `ε > 0`, `y ≥ 0`. -/
theorem abs_supCorrection_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε) {y : ℝ}
    (hy : 0 ≤ y) : |supCorrection θ ε y| ≤ (1 / Real.Gamma θ + 1 / 2) * ε ^ (θ - 1) := by
  by_cases ht : θ = 2
  · subst θ
    rw [supCorrection_two hε hy, abs_neg, abs_of_nonneg (by positivity)]
    norm_num
    have hm : 0 ≤ max (ε - y) 0 := le_max_right _ _
    have hme : max (ε - y) 0 ≤ ε := max_le (by linarith) hε.le
    have hs : (max (ε - y) 0) ^ 2 ≤ ε ^ 2 := by nlinarith
    apply (div_le_iff₀ (by positivity : 0 < 2 * ε)).2
    nlinarith
  · have hg : 0 < Real.Gamma θ := Real.Gamma_pos_of_pos (by linarith [hθ.1])
    have hc : Continuous (fun r => stableScale θ (y - r)) :=
      (continuous_stableScale hθ.1).comp (continuous_const.sub continuous_id)
    have hi : IntegrableOn (fun r => stableScale θ (y - r)) (Ioc 0 ε) :=
      hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have he : supCorrection θ ε y =
        ε⁻¹ * ∫ r in Ioc 0 ε, (stableScale θ y - stableScale θ (y - r)) := by
      rw [supCorrection, ite_eq_right ht, sub_zero, integral_sub (integrableOn_const (by simp)) hi,
        setIntegral_const]
      simp only [Measure.real, Real.volume_Ioc, sub_zero, smul_eq_mul]
      rw [ENNReal.toReal_ofReal hε.le]
      field_simp
    have hb : ‖∫ r in Ioc 0 ε, (stableScale θ y - stableScale θ (y - r))‖ ≤
        (ε ^ (θ - 1) / Real.Gamma θ) * ε := by
      have hb' := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc 0 ε)
        (f := fun r : ℝ => stableScale θ y - stableScale θ (y - r))
        (C := ε ^ (θ - 1) / Real.Gamma θ) (by simp) (fun r hr => ?_)
      · simpa only [Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hε.le] using hb'
      · obtain ⟨h0, h1⟩ := scale_increment hθ hy hr.1.le
        rw [Real.norm_eq_abs, abs_of_nonneg h0]
        exact h1.trans (div_le_div_of_nonneg_right
          (Real.rpow_le_rpow hr.1.le hr.2 (by linarith [hθ.1])) hg.le)
    rw [he, abs_mul, abs_of_pos (inv_pos.mpr hε)]
    have hmul := mul_le_mul_of_nonneg_left hb (inv_pos.mpr hε).le
    rw [Real.norm_eq_abs] at hmul
    calc
      _ ≤ ε⁻¹ * ((ε ^ (θ - 1) / Real.Gamma θ) * ε) := hmul
      _ = (1 / Real.Gamma θ) * ε ^ (θ - 1) := by field_simp
      _ ≤ _ := by nlinarith [Real.rpow_nonneg hε.le (θ - 1)]

end BGW.StableTrees
