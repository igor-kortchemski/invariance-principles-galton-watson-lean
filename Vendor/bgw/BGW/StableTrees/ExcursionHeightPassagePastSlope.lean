/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightSlopeInterpolation
public import BGW.StableTrees.SupremumFactorizationPredictable
import BGW.StableTrees.SupremumFactorizationCompensation
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Predictable left passage slopes at fixed levels

The extended left passage time and its deterministic delays are predictable. Hence failure
of convergence of their dyadic left difference quotients is a predictable event. Infinite
passage times are retained throughout this construction.

The extended left passage process is monotone and lies between each strictly earlier
passage and the current passage. A doubled-cutoff comparison transfers the full-filter
zero-slope estimate to its finite reading, without assuming equality at fixed levels.
-/

@[expose] public section

open MeasureTheory MeasurableSpace Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The extended left passage time is predictable. -/
theorem measurable_predictable_passagePast :
    Measurable[predictableSigma] (fun p : ℝ≥0 × DLoc => passagePast p.1 p.2) :=
  measurable_predictable_of_leftContinuous measurable_passagePast_stopped
    (fun f _ hx => continuousWithinAt_passagePast f hx)

/-- A deterministic delay of the extended left passage time is predictable. -/
theorem measurable_predictable_passagePast_delay (δ : ℝ≥0) :
    Measurable[predictableSigma] (fun p : ℝ≥0 × DLoc => passagePast (p.1 - δ) p.2) := by
  apply measurable_predictable_of_leftContinuous (H := fun x f => passagePast (x - δ) f)
  · intro x
    exact (measurable_passagePast_stopped (x - δ)).mono
      (IsStoppingTime.measurableSpace_mono (isStoppingTime_firstPassageBelow (x - δ))
        (isStoppingTime_firstPassageBelow x)
        (fun f => firstPassageBelow_mono f tsub_le_self)) le_rfl
  · intro f x _
    by_cases hx : x ≤ δ
    · have he : (fun y : ℝ≥0 => passagePast (y - δ) f) =ᶠ[𝓝[Iio x] x]
          (fun _ => passagePast 0 f) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        rw [show y - δ = 0 from tsub_eq_zero_of_le (hy.le.trans hx)]
      rw [ContinuousWithinAt, tsub_eq_zero_of_le hx]
      exact tendsto_const_nhds.congr' he.symm
    · have hpos : 0 < x - δ := tsub_pos_iff_lt.mpr (not_le.mp hx)
      apply (continuousWithinAt_passagePast f hpos).comp (f := fun y : ℝ≥0 => y - δ)
        (show ContinuousWithinAt (fun y : ℝ≥0 => y - δ) (Iio x) x from
          (by fun_prop : Continuous (fun y : ℝ≥0 => y - δ)).continuousWithinAt)
      intro y hy
      by_cases hyδ : δ ≤ y
      · exact tsub_lt_tsub_right_of_le hyδ hy
      · change y - δ < x - δ
        rw [tsub_eq_zero_of_le (not_le.mp hyδ).le]
        exact hpos

/-- Failure of vanishing dyadic left slopes of the extended passage process. -/
noncomputable def excursionHeightLeftSlopeBad : Set (ℝ≥0 × DLoc) :=
  {p | ¬ Tendsto
    (fun n : ℕ => (passagePast p.1 p.2 - passagePast (p.1 - 1 / (2 : ℝ≥0) ^ n) p.2) /
      ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0)}

/-- The bad left-slope event is predictable, so general predictable compensation applies. -/
theorem measurableSet_excursionHeightLeftSlopeBad :
    MeasurableSet[predictableSigma] excursionHeightLeftSlopeBad := by
  let : MeasurableSpace (ℝ≥0 × DLoc) := predictableSigma
  exact (measurableSet_tendsto (𝓝 (0 : ℝ≥0∞)) (fun n =>
    (measurable_predictable_passagePast.sub
      (measurable_predictable_passagePast_delay (1 / (2 : ℝ≥0) ^ n))).div_const _)).compl

/-- The extended left passage process is monotone on every path. -/
theorem monotone_passagePast (f : DLoc) : Monotone (fun x => passagePast x f) := by
  intro x y hxy
  apply iSup_le
  intro z
  exact le_iSup_of_le ⟨z, z.2.trans_le hxy⟩ le_rfl

/-- Finite left passage values have monotonicity and the usual earlier/current bounds. -/
theorem ae_passageTimeMinus_order_bounds {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      Monotone (fun x => passageTimeMinus x f) ∧
        (∀ x, passageTimeMinus x f ≤ passageTime x f) ∧
          ∀ a b : ℝ≥0, a < b → passageTime a f ≤ passageTimeMinus b f := by
  filter_upwards [ae_passagePast_eq_passageTimeMinus hθ,
    ae_passageTime_eq_firstPassageBelow hθ] with f hp hf
  have hbound (x : ℝ≥0) : passagePast x f ≤ (passageTime x f : ℝ≥0∞) := by
    apply iSup_le
    intro z
    have hh := firstPassageBelow_mono f z.2.le
    have hh' : passageTime z f ≤ passageTime x f := by
      simpa only [hf.1 z, hf.1 x, WithTop.coe_le_coe] using hh
    rw [hf.1 z]
    exact ENNReal.coe_le_coe.mpr hh'
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    have hh := monotone_passagePast f hab
    change passagePast a f ≤ passagePast b f at hh
    rw [hp a, hp b] at hh
    exact ENNReal.coe_le_coe.mp hh
  · intro x
    have hh := hbound x
    rw [hp x] at hh
    exact ENNReal.coe_le_coe.mp hh
  · intro a b hab
    have hh : (firstPassageBelow a f : ℝ≥0∞) ≤ passagePast b f :=
      le_iSup (fun z : Iio b => (firstPassageBelow z f : ℝ≥0∞)) ⟨a, hab⟩
    rw [hf.1 a, hp b] at hh
    exact ENNReal.coe_le_coe.mp hh

/-- At a fixed positive level the finite left passage process has a zero full left slope. -/
theorem ae_tendsto_passageTimeMinus_leftSlope {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (x : ℝ≥0) (hx : 0 < x) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      Tendsto (fun ε : ℝ =>
        ((passageTimeMinus x f : ℝ) - (passageTimeMinus (x - ε.toNNReal) f : ℝ)) / ε)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [ae_tendsto_passageTime_leftSlope hθ x hx,
    ae_passageTimeMinus_order_bounds hθ] with f hright hf
  have hdouble : Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    have hi : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    refine ⟨by simpa only [mul_zero] using hi.const_mul 2, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact mul_pos (by norm_num) hε
  have hupper : Tendsto (fun ε : ℝ =>
      2 * (((passageTime x f : ℝ) - (passageTime (x - (2 * ε).toNNReal) f : ℝ)) /
        (2 * ε))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using (hright.comp hdouble).const_mul 2
  apply squeeze_zero' ?_ ?_ hupper
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact div_nonneg (sub_nonneg.mpr (show (passageTimeMinus (x - ε.toNNReal) f : ℝ) ≤
      passageTimeMinus x f from hf.1 tsub_le_self)) hε.le
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < (x : ℝ) / 2 from half_pos hx)]
      with ε hε
    have hεpos : 0 < ε := hε.1
    have h2ε : (2 * ε).toNNReal ≤ x := Real.toNNReal_le_iff_le_coe.mpr (by linarith [hε.1, hε.2])
    have hεx : ε.toNNReal ≤ x := Real.toNNReal_le_iff_le_coe.mpr (by linarith [hε.1, hε.2])
    have hab : x - (2 * ε).toNNReal < x - ε.toNNReal := by
      rw [← NNReal.coe_lt_coe, NNReal.coe_sub h2ε, NNReal.coe_sub hεx,
        Real.coe_toNNReal _ (by positivity : 0 ≤ 2 * ε), Real.coe_toNNReal _ hε.1.le]
      linarith only [hε.1]
    have hlo := hf.2.2 _ _ hab
    have hhi := hf.2.1 x
    have hnum : (passageTimeMinus x f : ℝ) - passageTimeMinus (x - ε.toNNReal) f ≤
        (passageTime x f : ℝ) - passageTime (x - (2 * ε).toNNReal) f :=
      sub_le_sub hhi hlo
    have hb := div_le_div_of_nonneg_right hnum hε.1.le
    convert hb using 1
    field_simp

end BGW.StableTrees
