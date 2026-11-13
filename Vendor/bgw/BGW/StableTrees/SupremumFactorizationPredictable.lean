/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureCompensation
public import BGW.StableTrees.ExcursionMeasureLaplaceBasic

/-!
# Predictable discount at the left passage time

Passage times are kept in the extended nonnegative reals until after discounting.
This preserves left continuity even on paths with an infinite passage time.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
-/

@[expose] public section

open MeasureTheory MeasurableSpace Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The extended left passage time, without totalizing infinite times to zero. -/
noncomputable def passagePast (x : ℝ≥0) (f : DLoc) : ℝ≥0∞ :=
  ⨆ y : Set.Iio x, firstPassageBelow y f

private theorem passagePast_eq_rat (x : ℝ≥0) (f : DLoc) :
    passagePast x f = ⨆ r : ℚ,
      if 0 ≤ r ∧ (r : ℝ) < (x : ℝ) then
        (firstPassageBelow (Real.toNNReal r) f : ℝ≥0∞) else 0 := by
  apply le_antisymm
  · apply iSup_le
    intro y
    obtain ⟨r, hyr, hrx⟩ := exists_rat_btwn
      (show (y : ℝ) < (x : ℝ) by exact_mod_cast y.2)
    have hr0 : 0 ≤ (r : ℝ) := y.1.2.trans hyr.le
    have hle : (y : ℝ≥0) ≤ Real.toNNReal r := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]
      exact hyr.le
    apply (firstPassageBelow_mono f hle).trans
    apply le_iSup_of_le r
    simp only [show 0 ≤ r from by exact_mod_cast hr0, hrx, and_self, ite_eq_left]
    exact le_rfl
  · apply iSup_le
    intro r
    split_ifs with hr
    · have hr0 : 0 ≤ (r : ℝ) := by exact_mod_cast hr.1
      have hrx : Real.toNNReal r < x := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]
        exact hr.2
      exact le_iSup (fun y : Set.Iio x => (firstPassageBelow y f : ℝ≥0∞))
        ⟨Real.toNNReal r, hrx⟩
    · exact bot_le

/-- The extended left passage time is measurable in the stopped past at its label. -/
theorem measurable_passagePast_stopped (x : ℝ≥0) :
    Measurable[(isStoppingTime_firstPassageBelow x).measurableSpace] (passagePast x) := by
  have he : passagePast x = fun f => ⨆ r : ℚ,
      if 0 ≤ r ∧ (r : ℝ) < (x : ℝ) then
        (firstPassageBelow (Real.toNNReal r) f : ℝ≥0∞) else 0 :=
    funext (passagePast_eq_rat x)
  rw [he]
  apply Measurable.iSup
  intro r
  by_cases hr : 0 ≤ r ∧ (r : ℝ) < (x : ℝ)
  · simp only [ite_eq_left hr]
    have hr0 : 0 ≤ (r : ℝ) := by exact_mod_cast hr.1
    have hrx : Real.toNNReal r ≤ x := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]
      exact hr.2.le
    exact (isStoppingTime_firstPassageBelow (Real.toNNReal r)).measurable.mono
      (IsStoppingTime.measurableSpace_mono (isStoppingTime_firstPassageBelow _)
        (isStoppingTime_firstPassageBelow x) (fun f => firstPassageBelow_mono f hrx)) le_rfl
  · simp only [ite_eq_right hr]
    exact measurable_const

private theorem passagePast_eq_leftLim (f : DLoc) {x : ℝ≥0} (hx : 0 < x) :
    passagePast x f = Function.leftLim (fun y => (firstPassageBelow y f : ℝ≥0∞)) x := by
  have : (𝓝[<] x).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hx⟩
  rw [(show Monotone (fun y => (firstPassageBelow y f : ℝ≥0∞)) from
    firstPassageBelow_mono f).leftLim_eq_sSup]
  exact (sSup_image' (s := Iio x)
    (f := fun y => (firstPassageBelow y f : ℝ≥0∞))).symm

/-- The extended left passage time is left continuous, including exceptional paths. -/
theorem continuousWithinAt_passagePast (f : DLoc) {x : ℝ≥0} (hx : 0 < x) :
    ContinuousWithinAt (fun y => passagePast y f) (Iio x) x := by
  have hm : Monotone (fun y => (firstPassageBelow y f : ℝ≥0∞)) := firstPassageBelow_mono f
  have ht := (continuousWithinAt_leftLim_Iic (hm.tendsto_leftLim x)).mono
    Iio_subset_Iic_self
  rw [ContinuousWithinAt, passagePast_eq_leftLim f hx]
  apply ht.tendsto.congr'
  filter_upwards [Ioo_mem_nhdsLT hx] with y hy
  exact (passagePast_eq_leftLim f hy.1).symm

/-- Predictable exponential discount of the extended left passage time. -/
theorem measurable_predictable_passagePast_discount (q : ℝ) :
    Measurable[predictableSigma]
      (fun p : ℝ≥0 × DLoc => expNeg (ENNReal.ofReal q * passagePast p.1 p.2)) := by
  apply measurable_predictable_of_leftContinuous
    (H := fun x f => expNeg (ENNReal.ofReal q * passagePast x f))
  · intro x
    exact continuous_expNeg.measurable.comp
      (measurable_const.mul (measurable_passagePast_stopped x))
  · intro f x hx
    exact continuous_expNeg.continuousAt.comp_continuousWithinAt
      ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).continuousAt.comp_continuousWithinAt
        (continuousWithinAt_passagePast f hx))

end BGW.StableTrees
