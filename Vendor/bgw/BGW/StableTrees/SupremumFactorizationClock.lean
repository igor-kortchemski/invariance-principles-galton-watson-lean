/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLocalTime
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Independence.Basic

/-!
# Exponential clocks for the stable supremum

The path law and an independent exponential clock, with joint measurability and
nonnegativity of the running supremum and its reflection.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Path law times an independent `Exp(q)` clock** on `DLoc × ℝ`. -/
noncomputable def expClockLaw (θ q : ℝ) : Measure (DLoc × ℝ) :=
  (stableLocalLaw θ : Measure DLoc).prod (expMeasure q)

/-- The clock model is a probability space for `q > 0`. -/
theorem isProbabilityMeasure_expClockLaw (θ : ℝ) {q : ℝ} (hq : 0 < q) :
    IsProbabilityMeasure (expClockLaw θ q) := by
  let := isProbabilityMeasure_expMeasure hq
  unfold expClockLaw
  infer_instance

/-- The clock is a.s. nonnegative, so `toNNReal` reads it without junk. -/
theorem ae_clock_nonneg_expClockLaw (θ : ℝ) {q : ℝ} (hq : 0 < q) :
    ∀ᵐ p ∂expClockLaw θ q, 0 ≤ p.2 := by
  let := isProbabilityMeasure_expMeasure hq
  have hz : expMeasure q (Iio 0) = 0 := by
    rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
    exact lintegral_exponentialPDF_of_nonpos le_rfl
  exact Measure.quasiMeasurePreserving_snd.ae
    ((measure_eq_zero_iff_ae_notMem.mp hz).mono (fun _ h => not_lt.mp h))

/-- `p ↦ S_{e_q}` is measurable. -/
theorem measurable_supRunning_expTime :
    Measurable (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal) := by
  exact measurable_supRunning_uncurry.comp
    ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk measurable_fst)

/-- `p ↦ R_{e_q} = S_{e_q} - X_{e_q}` is measurable. -/
theorem measurable_supReflected_expTime :
    Measurable (fun p : DLoc × ℝ => supReflected p.1 p.2.toNNReal) := by
  exact measurable_supReflected_uncurry.comp
    ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk measurable_fst)

/-- Both `S_{e_q}` and `R_{e_q}` are a.s. nonnegative (`f 0 = 0` a.s.; `R ≥ 0` always). -/
theorem ae_nonneg_supRunning_supReflected_expTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) :
    ∀ᵐ p ∂expClockLaw θ q, 0 ≤ supRunning p.1 p.2.toNNReal ∧ 0 ≤ supReflected p.1 p.2.toNNReal := by
  let := isProbabilityMeasure_expMeasure hq
  have he : ∀ᵐ p ∂expClockLaw θ q, p.1.1 0 = 0 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_eval_zero_stableLocalLaw hθ)
  filter_upwards [he] with p hp
  refine ⟨?_, supReflected_nonneg _ _⟩
  simpa only [hp] using eval_le_supRunning p.1 (u := 0) (bot_le : 0 ≤ p.2.toNNReal)

end BGW.StableTrees
