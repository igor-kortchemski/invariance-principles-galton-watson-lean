/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumFactorization
public import BGW.StableTrees.SupremumDrawdownExponential
public import BGW.StableTrees.SupremumDrawdownPassage

/-! # The infimum and drawdown at an independent exponential clock

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The infimum coordinate as a separate function of nonnegative time and path. -/
noncomputable def infimumLevel (p : ℝ≥0 × DLoc) : ℝ := localTime p.2 p.1

/-- The infimum local time evaluated at the independent clock. -/
noncomputable def clockLocalTime (p : DLoc × ℝ) : ℝ :=
  infimumLevel (p.2.toNNReal, p.1)

/-- Measurability of the infimum local time at the clock. -/
theorem measurable_clockLocalTime : Measurable clockLocalTime := by
  have h1 : Measurable infimumLevel :=
    measurable_localTime_uncurry
  have hp : Measurable (fun p : DLoc × ℝ => (p.2.toNNReal, p.1)) :=
    measurable_snd.real_toNNReal.prodMk measurable_fst
  exact h1.comp hp

/-- Fixed-time reversal integrated over the independent clock identifies the drawdown
marginal with the negative infimum marginal. -/
theorem lintegral_supReflected_eq_localTime_expTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q : ℝ} (hq : 0 < q) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ p, G (supReflected p.1 p.2.toNNReal) ∂expClockLaw θ q) =
      ∫⁻ p, G (clockLocalTime p) ∂expClockLaw θ q := by
  have hR : Measurable (fun p : DLoc × ℝ => G (supReflected p.1 p.2.toNNReal)) :=
    hG.comp measurable_supReflected_expTime
  have hL : Measurable (fun p : DLoc × ℝ => G (clockLocalTime p)) :=
    hG.comp measurable_clockLocalTime
  rw [lintegral_expClockLaw θ hq hR, lintegral_expClockLaw θ hq hL]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ)),
    ae_restrict_mem measurableSet_Ici] with t hne ht
  have he := lintegral_sup_drawdown_reverse_local hθ
    (Real.toNNReal_pos.mpr (lt_of_le_of_ne ht hne.symm))
    (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ≥0∞))) hG
  simp only [one_mul, mul_one] at he
  exact congrArg (fun z => ENNReal.ofReal (q * Real.exp (-q * t)) * z) he

/-- The local-time tail at an independent exponential clock is the passage Laplace transform. -/
theorem expClockLaw_clockLocalTime_gt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q : ℝ} (hq : 0 < q) (x : ℝ≥0) :
    expClockLaw θ q {p | (x : ℝ) < clockLocalTime p} =
      ENNReal.ofReal (Real.exp (-(x : ℝ) * q ^ (1 / θ))) := by
  let := isProbabilityMeasure_expMeasure hq
  have he : {p | (x : ℝ) < clockLocalTime p} =ᵐ[expClockLaw θ q]
      {p | (passageTime x p.1 : ℝ) < p.2} := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (ae_localTime_gt_iff_passageTime_lt hθ), ae_clock_nonneg_expClockLaw θ hq]
      with p hp ht
    apply propext
    change ((x : ℝ) < localTime p.1 p.2.toNNReal) ↔ _
    rw [hp x p.2.toNNReal]
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ ht]
  have hset : MeasurableSet {p : DLoc × ℝ | (passageTime x p.1 : ℝ) < p.2} :=
    measurableSet_lt ((measurable_passageTime x).coe_nnreal_real.comp measurable_fst)
      measurable_snd
  rw [measure_congr he, expClockLaw, Measure.prod_apply hset]
  have hinner (f : DLoc) :
      expMeasure q (Prod.mk f ⁻¹' {p | (passageTime x p.1 : ℝ) < p.2}) =
        ENNReal.ofReal (Real.exp (-q * (passageTime x f : ℝ))) := by
    have hs : (Prod.mk f ⁻¹' {p : DLoc × ℝ | (passageTime x p.1 : ℝ) < p.2}) =
        Ioi (passageTime x f : ℝ) := by
      ext t
      rfl
    rw [hs]
    simpa only [neg_mul] using expMeasure_Ioi_nonneg hq (passageTime x f).coe_nonneg
  simp_rw [hinner]
  by_cases hx : x = 0
  · subst x
    have hz : (fun f => ENNReal.ofReal (Real.exp (-q * (passageTime 0 f : ℝ)))) =ᵐ[
        (stableLocalLaw θ : Measure DLoc)] (fun _ => (1 : ℝ≥0∞)) := by
      filter_upwards [ae_passageTime_eq_firstPassageBelow hθ] with f hf
      simp [hf.2]
    rw [lintegral_congr_ae hz]
    simp
  · simpa only [passageTime] using
      lintegral_exp_neg_firstPassageBelow hθ (pos_iff_ne_zero.mpr hx) hq.le

/-- Tail form: `P ⊗ Exp(q) (R_{e_q} > y) = e^{-y q^{1/θ}}` for `y ≥ 0`. -/
theorem expClockLaw_supReflected_gt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    {y : ℝ} (hy : 0 ≤ y) :
    expClockLaw θ q {p | y < supReflected p.1 p.2.toNNReal} =
      ENNReal.ofReal (Real.exp (-(y * q ^ (1 / θ)))) := by
  classical
  have he := lintegral_supReflected_eq_localTime_expTime hθ hq
    (measurable_const.indicator measurableSet_Ioi :
      Measurable ((Ioi y).indicator (fun _ => (1 : ℝ≥0∞))))
  have hiR : (fun p : DLoc × ℝ => (Ioi y).indicator (fun _ => (1 : ℝ≥0∞))
      (supReflected p.1 p.2.toNNReal)) =
      {p : DLoc × ℝ | y < supReflected p.1 p.2.toNNReal}.indicator (fun _ => 1) := rfl
  have hiL : (fun p : DLoc × ℝ => (Ioi y).indicator (fun _ => (1 : ℝ≥0∞))
      (clockLocalTime p)) = {p : DLoc × ℝ | y < clockLocalTime p}.indicator (fun _ => 1) := rfl
  rw [hiR, hiL, lintegral_indicator_const
    (measurableSet_lt measurable_const measurable_supReflected_expTime),
    lintegral_indicator_const (measurableSet_lt measurable_const measurable_clockLocalTime)] at he
  simp only [one_mul] at he
  rw [he]
  simpa only [Real.coe_toNNReal _ hy, neg_mul] using
    expClockLaw_clockLocalTime_gt hθ hq y.toNNReal

/-- **Exponential drawdown.** `S_{e_q} - X_{e_q} ~ Exp(q^{1/θ})`. -/
theorem law_supReflected_expTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    (expClockLaw θ q).map (fun p : DLoc × ℝ => supReflected p.1 p.2.toNNReal) =
      expMeasure (q ^ (1 / θ)) := by
  let := isProbabilityMeasure_expClockLaw θ hq
  have hPhi : 0 < q ^ (1 / θ) := Real.rpow_pos_of_pos hq _
  let := isProbabilityMeasure_expMeasure hPhi
  apply Measure.ext_of_Iic
  intro y
  by_cases hy : 0 ≤ y
  · rw [← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top _ _), measure_univ,
      measure_compl measurableSet_Ioi (measure_ne_top _ _), measure_univ,
      Measure.map_apply measurable_supReflected_expTime measurableSet_Ioi]
    change 1 - expClockLaw θ q {p | y < supReflected p.1 p.2.toNNReal} = _
    rw [expClockLaw_supReflected_gt hθ hq hy, expMeasure_Ioi_nonneg hPhi hy]
    congr 3
    ring
  · rw [Measure.map_apply measurable_supReflected_expTime measurableSet_Iic]
    have hempty : {p : DLoc × ℝ | supReflected p.1 p.2.toNNReal ≤ y} = ∅ := by
      ext p
      exact iff_false_intro (fun h => hy ((supReflected_nonneg _ _).trans h))
    rw [show (fun p : DLoc × ℝ => supReflected p.1 p.2.toNNReal) ⁻¹' Iic y =
      {p : DLoc × ℝ | supReflected p.1 p.2.toNNReal ≤ y} from rfl, hempty, measure_empty,
      ← ofReal_cdf, cdf_expMeasure_eq hPhi, ite_eq_right hy]
    simp

end BGW.StableTrees
