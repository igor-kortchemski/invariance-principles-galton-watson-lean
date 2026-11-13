/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumReflectedFamily
import BGW.StableTrees.SupremumAuxLocalTimePrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Occupation restart at a supremum contact

The deterministic reflected restart identifies the occupation increment with the occupation
of the centered shifted path, at every contact time.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VI.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- At a contact time, the centered shifted path has the same future reflection. -/
theorem supReflected_shift_of_contact {f : DLoc} (hf : f.1 0 = 0) {s : ℝ≥0}
    (hs : supReflected f s = 0) (t : ℝ≥0) :
    supReflected f (s + t) = supReflected (DLoc.shift s f) t := by
  have h := supReflectedFrom_restart 0 f s t
  simpa only [supReflectedFrom_zero_apply hf, hs, Real.toNNReal_zero,
    supReflectedFrom_zero_apply (show (DLoc.shift s f).1 0 = 0 by
      change f.1 (s + 0) - f.1 s = 0
      simp)] using h

/-- The running supremum adds its contact value to that of the centered future path. -/
theorem supRunning_shift_of_contact {f : DLoc} (hf : f.1 0 = 0) {s : ℝ≥0}
    (hs : supReflected f s = 0) (t : ℝ≥0) :
    supRunning f (s + t) = supRunning f s + supRunning (DLoc.shift s f) t := by
  have h := supReflected_shift_of_contact hf hs t
  change supRunning f (s + t) - f.1 (s + t) =
    supRunning (DLoc.shift s f) t - (f.1 (s + t) - f.1 s) at h
  change supRunning f s - f.1 s = 0 at hs
  linarith

/-- Occupation approximations split exactly at every supremum contact time. -/
theorem supOccupation_shift_of_contact {ε : ℝ} (hε : 0 < ε) {f : DLoc}
    (hf : f.1 0 = 0) {s : ℝ≥0} (hs : supReflected f s = 0) (t : ℝ≥0) :
    supOccupation ε f (s + t) - supOccupation ε f s =
      supOccupation ε (DLoc.shift s f) t := by
  have hshift : (DLoc.shift s f).1 0 = 0 := by
    change f.1 (s + 0) - f.1 s = 0
    simp
  rw [supOccupation_sub_eq_integral hε f hf (le_add_of_nonneg_right (show 0 ≤ t from zero_le)),
    supOccupation_eq_integral_supOccKernel _ hshift]
  rw [← intervalIntegral.integral_of_le (show (s : ℝ) ≤ (s + t : ℝ≥0) by
    simp only [NNReal.coe_add]; exact le_add_of_nonneg_right t.coe_nonneg),
    ← intervalIntegral.integral_of_le t.coe_nonneg]
  have htrans := intervalIntegral.integral_comp_add_left (a := 0) (b := (t : ℝ))
    (fun x => supOccKernel ε (supReflectedFrom 0 f x.toNNReal)) (s : ℝ)
  simp only [add_zero] at htrans
  rw [NNReal.coe_add, ← htrans]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with u
  intro hu
  rw [uIoc_of_le t.coe_nonneg] at hu
  have hu0 : 0 ≤ u := hu.1.le
  have hsum : (s + u).toNNReal = s + u.toNNReal := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by positivity), NNReal.coe_add,
      Real.coe_toNNReal _ hu0]
  rw [hsum, supReflectedFrom_zero_apply hf, supReflectedFrom_zero_apply hshift,
    supReflected_shift_of_contact hf hs]

end BGW.StableTrees
