/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderTransformBasic
import BGW.StableTrees.SupremumPotentialClock
import Mathlib.Probability.Independence.Integration

/-!
# Weighted occupation resolvent at the supremum

Exponential-clock independence factors the weighted occupation resolvent exactly.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **`ε`-level exact identity.**  For `q, ε > 0`, `λ ≥ 0`: with `g_ε` the occupation kernel,
`E ∫_0^∞ e^{-qt} e^{-λ S_t} g_ε(R_t) dt = q⁻¹ ε⁻¹ (1 - e^{-εΦ}) E e^{-λ S_{e_q}}`
(`E ∫ e^{-qt} G_t dt = q⁻¹ E G(e_q)`, independence of `S_{e_q}` and `R_{e_q}`,
`R_{e_q} ~ Exp(Φ)`). -/
theorem integral_resolvent_exp_neg_supRunning {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam ε : ℝ}
    (hq : 0 < q) (hlam : 0 ≤ lam) (hε : 0 < ε) :
    ∫ f, (∫ t in Ioi (0 : ℝ), Real.exp (-q * t) *
        (Real.exp (-lam * supRunning f t.toNNReal) *
          supOccKernel ε (supReflected f t.toNNReal))) ∂(stableLocalLaw θ : Measure DLoc) =
      q⁻¹ * (ε⁻¹ * (1 - Real.exp (-(ε * q ^ (1 / θ))))) *
        ∫ p, Real.exp (-lam * supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q := by
  let P : Measure DLoc := stableLocalLaw θ
  let F : ℝ → ℝ := fun x => Real.exp (-lam * max x 0)
  let G : ℝ → ℝ := supOccKernel ε
  have hF : Measurable F := by fun_prop
  have hG : Measurable G := measurable_supOccKernel ε
  have hFbound (x : ℝ) : |F x| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam) (le_max_right _ _)
  let H : DLoc × ℝ → ℝ := fun p =>
    F (supRunning p.1 p.2.toNNReal) * G (supReflected p.1 p.2.toNNReal)
  have hH : Measurable H := (hF.comp measurable_supRunning_expTime).mul
    (hG.comp measurable_supReflected_expTime)
  have hclock := integral_expClockLaw_eq (θ := θ) hq hH (by
    refine ⟨ε⁻¹, fun p => ?_⟩
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hFbound _) (abs_nonneg _)).trans
      (by simpa only [G, one_mul, abs_of_nonneg (supOccKernel_mem_Icc hε _).1] using
        (supOccKernel_mem_Icc hε (supReflected p.1 p.2.toNNReal)).2))
  have hind := (indepFun_supRunning_supReflected_expTime hθ hq).integral_fun_comp_mul_comp
    measurable_supRunning_expTime.aemeasurable measurable_supReflected_expTime.aemeasurable
    hF.aestronglyMeasurable hG.aestronglyMeasurable
  have hfeq : (∫ p, F (supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q) =
      ∫ p, Real.exp (-lam * supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q := by
    apply integral_congr_ae
    filter_upwards [ae_nonneg_supRunning_supReflected_expTime hθ hq] with p hp
    simp only [F, max_eq_left hp.1]
  have hPhi : 0 < q ^ (1 / θ) := Real.rpow_pos_of_pos hq _
  let : NullSingletonClass (expMeasure (q ^ (1 / θ))) := by
    change NullSingletonClass (volume.withDensity (exponentialPDF (q ^ (1 / θ))))
    infer_instance
  let := isProbabilityMeasure_expMeasure hPhi
  have hgeq : (∫ p, G (supReflected p.1 p.2.toNNReal) ∂expClockLaw θ q) =
      ε⁻¹ * (1 - Real.exp (-(ε * q ^ (1 / θ)))) := by
    rw [← integral_map measurable_supReflected_expTime.aemeasurable hG.aestronglyMeasurable,
      law_supReflected_expTime hθ hq]
    change (∫ x, (Iio ε).indicator (fun _ => ε⁻¹) x ∂expMeasure (q ^ (1 / θ))) = _
    rw [integral_indicator_const _ measurableSet_Iio, smul_eq_mul, Measure.real,
      measure_congr Iio_ae_eq_Iic, ← ofReal_cdf, ENNReal.toReal_ofReal
        (cdf_nonneg _ _), cdf_expMeasure_eq hPhi, ite_eq_left hε.le]
    simp only [mul_comm]
  have hepath : (∫ f, (∫ t in Ioi (0 : ℝ), Real.exp (-q * t) * H (f, t)) ∂P) =
      ∫ f, (∫ t in Ioi (0 : ℝ), Real.exp (-q * t) *
        (Real.exp (-lam * supRunning f t.toNNReal) *
          supOccKernel ε (supReflected f t.toNNReal))) ∂P := by
    apply integral_congr_ae
    filter_upwards [ae_eval_zero_stableLocalLaw hθ] with f hf
    apply integral_congr_ae
    filter_upwards with t
    have hs : 0 ≤ supRunning f t.toNNReal := by
      simpa only [hf] using eval_le_supRunning f (u := 0) (zero_le : 0 ≤ t.toNNReal)
    simp only [H, F, G, max_eq_left hs]
  change (∫ p, H p ∂expClockLaw θ q) = _ at hind
  rw [hfeq, hgeq] at hind
  rw [hepath] at hclock
  change (∫ f, (∫ t in Ioi (0 : ℝ), Real.exp (-q * t) *
    (Real.exp (-lam * supRunning f t.toNNReal) *
      supOccKernel ε (supReflected f t.toNNReal))) ∂P) = _
  calc
    _ = q⁻¹ * ∫ p, H p ∂expClockLaw θ q := by rw [hclock]; field_simp
    _ = _ := by rw [hind]; ring

end BGW.StableTrees
