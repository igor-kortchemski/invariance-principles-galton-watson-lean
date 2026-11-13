/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Auxiliary layer-cake identities for Doob's `L²` maximal inequality.

Reference: O. Kallenberg, *Foundations of Modern Probability*, 2nd ed., Springer, 2002.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace BGW.Probability

/-- The tail-integral formula for the square of a nonnegative measurable function. -/
theorem lintegral_sq_eq_tail {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {f : Ω → ℝ} (hf : Measurable f) (hnn : ∀ ω, 0 ≤ f ω) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ^ 2 ∂μ =
      ∫⁻ t in Ioi (0 : ℝ), μ {ω | t ≤ f ω} * ENNReal.ofReal (2 * t) := by
  have h := lintegral_comp_eq_lintegral_meas_le_mul μ
    (f := f) (g := fun t => 2 * t) (Eventually.of_forall hnn) hf.aemeasurable
    (fun t _ => (by fun_prop : Continuous fun x : ℝ => 2 * x).intervalIntegrable 0 t)
    ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall (fun t ht => mul_nonneg (by norm_num) (le_of_lt ht))))
  rw [← h]
  apply lintegral_congr
  intro ω
  rw [intervalIntegral.integral_const_mul, integral_id]
  have heq : 2 * ((f ω ^ 2 - 0 ^ 2) / 2) = f ω ^ 2 := by ring
  rw [heq, ENNReal.ofReal_pow (hnn ω)]

/-- Tonelli's theorem applied to the integral of `g` over the tail sets of `f`. -/
theorem lintegral_tail_eq {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [SFinite μ]
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ ω in {ω | t ≤ f ω}, ENNReal.ofReal (g ω) ∂μ) =
      ∫⁻ ω, ENNReal.ofReal (f ω) * ENNReal.ofReal (g ω) ∂μ := by
  have hset : MeasurableSet {p : ℝ × Ω | p.1 ≤ f p.2} :=
    measurableSet_le measurable_fst (hf.comp measurable_snd)
  have hmeas : AEMeasurable (fun p : ℝ × Ω =>
      {ω | p.1 ≤ f ω}.indicator (fun _ => ENNReal.ofReal (g p.2)) p.2)
      ((volume.restrict (Ioi 0)).prod μ) := by
    apply AEMeasurable.indicator
    · exact (hg.comp measurable_snd).ennreal_ofReal.aemeasurable
    · exact hset
  simp_rw [← lintegral_indicator (measurableSet_le measurable_const hf)]
  rw [lintegral_lintegral_swap hmeas]
  apply lintegral_congr
  intro ω
  have heq (t : ℝ) : {ω' | t ≤ f ω'}.indicator
      (fun _ => ENNReal.ofReal (g ω)) ω =
      {t | t ≤ f ω}.indicator (fun _ => ENNReal.ofReal (g ω)) t := by
    by_cases h : t ≤ f ω <;> simp [Set.indicator, h]
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), {t | t ≤ f ω}.indicator
        (fun _ => ENNReal.ofReal (g ω)) t := by
      apply lintegral_congr
      intro t
      exact heq t
    _ = ENNReal.ofReal (g ω) * (volume.restrict (Ioi (0 : ℝ))) {t | t ≤ f ω} :=
      lintegral_indicator_const (μ := volume.restrict (Ioi (0 : ℝ)))
        (s := {t | t ≤ f ω}) (measurableSet_le measurable_id measurable_const) _
    _ = _ := by
      rw [Measure.restrict_apply (μ := volume) (s := Ioi (0 : ℝ))
        (t := {t | t ≤ f ω}) (measurableSet_le measurable_id measurable_const)]
      rw [show {t | t ≤ f ω} ∩ Ioi (0 : ℝ) = Ioc 0 (f ω) by ext t; simp [and_comm]]
      simp only [Real.volume_Ioc, sub_zero]
      ring

/-- A tail estimate `t μ(f ≥ t) ≤ ∫_{f ≥ t} g` for `t > 0` implies `∫ f² ≤ 2 ∫ f g`. -/
theorem lintegral_sq_le_two_mul_of_tail {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [SFinite μ] {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfnn : ∀ ω, 0 ≤ f ω)
    (htail : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {ω | t ≤ f ω} ≤
      ∫⁻ ω in {ω | t ≤ f ω}, ENNReal.ofReal (g ω) ∂μ) :
    ∫⁻ ω, ENNReal.ofReal (f ω) ^ 2 ∂μ ≤
      2 * ∫⁻ ω, ENNReal.ofReal (f ω) * ENNReal.ofReal (g ω) ∂μ := by
  have hpoint (t : ℝ) (ht : 0 < t) :
      μ {ω | t ≤ f ω} * ENNReal.ofReal (2 * t) ≤
        2 * ∫⁻ ω in {ω | t ≤ f ω}, ENNReal.ofReal (g ω) ∂μ := by
    calc
      _ = 2 * (ENNReal.ofReal t * μ {ω | t ≤ f ω}) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
        ring
      _ ≤ _ := by
        gcongr
        exact htail t ht
  calc
    _ = ∫⁻ t in Ioi (0 : ℝ), μ {ω | t ≤ f ω} * ENNReal.ofReal (2 * t) :=
      lintegral_sq_eq_tail hf hfnn
    _ ≤ ∫⁻ t in Ioi (0 : ℝ),
        2 * ∫⁻ ω in {ω | t ≤ f ω}, ENNReal.ofReal (g ω) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact hpoint t ht
    _ = 2 * ∫⁻ t in Ioi (0 : ℝ),
        ∫⁻ ω in {ω | t ≤ f ω}, ENNReal.ofReal (g ω) ∂μ := by
      rw [lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    _ = _ := by
      congr 1
      exact lintegral_tail_eq hf hg

end BGW.Probability
