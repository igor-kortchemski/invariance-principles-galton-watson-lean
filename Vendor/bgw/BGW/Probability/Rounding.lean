/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp

/-! # Measurability and normalized convergence of rounding -/

@[expose] public section

open Filter
open scoped Topology

namespace BGW.Probability

/-- Rounding a real number to the nearest integer is measurable. -/
theorem measurable_round : Measurable (round : ℝ → ℤ) := by
  change Measurable (fun x : ℝ => round x)
  simp_rw [round_eq]
  exact Int.measurable_floor.comp (measurable_id.add_const _)

/-- Rounding `v k * b k` and dividing by `b k` preserves the limit of `v` when `b` diverges. -/
theorem round_normalized_tendsto {v b : ℕ → ℝ} {x : ℝ}
    (hv : Tendsto v atTop (𝓝 x)) (hb : Tendsto b atTop atTop) :
    Tendsto (fun k => (round (v k * b k) : ℝ) / b k) atTop (𝓝 x) := by
  have herr : Tendsto (fun k => (round (v k * b k) : ℝ) / b k - v k) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (g := fun k => (1 / 2 : ℝ) / b k)
      (Eventually.of_forall fun k => abs_nonneg _)
    · filter_upwards [hb.eventually_gt_atTop 0] with k hk
      have heq : (round (v k * b k) : ℝ) / b k - v k =
          ((round (v k * b k) : ℝ) - v k * b k) / b k := by field_simp
      rw [heq, abs_div, abs_of_pos hk]
      apply div_le_div_of_nonneg_right _ hk.le
      simpa only [abs_sub_comm] using (abs_sub_round (v k * b k))
    · exact hb.const_div_atTop (1 / 2 : ℝ)
  simpa only [sub_add_cancel, zero_add] using herr.add hv

end BGW.Probability
