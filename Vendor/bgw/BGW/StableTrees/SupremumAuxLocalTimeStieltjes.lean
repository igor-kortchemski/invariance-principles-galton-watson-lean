/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# Stieltjes extension of a continuous clock

A monotone continuous clock on nonnegative times is extended constantly to negative times.
The zero totalization is continuous as well, so its measure is always atomless.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.StableTrees

open scoped Classical in
/-- The Stieltjes function `s ↦ m(s⁺)` of a path `m`; junk zero unless `m` is monotone and
continuous (same pattern as `supLocalTimeStieltjes`). -/
noncomputable def pathStieltjes (m : ℝ≥0 → ℝ) : StieltjesFunction ℝ :=
  if h : Monotone m ∧ Continuous m then
    { toFun := fun s => m s.toNNReal
      mono' := h.1.comp (fun _ _ hab => Real.toNNReal_mono hab)
      right_continuous' := fun _ =>
        ((h.2.comp continuous_real_toNNReal).continuousAt).continuousWithinAt }
  else
    { toFun := fun _ => 0
      mono' := monotone_const
      right_continuous' := fun _ => continuousWithinAt_const }

/-- On a continuous monotone path the Stieltjes extension evaluates the original clock. -/
theorem pathStieltjes_apply {m : ℝ≥0 → ℝ} (hm : Monotone m ∧ Continuous m) (s : ℝ) :
    pathStieltjes m s = m s.toNNReal := by
  simp only [pathStieltjes, dite_eq_left hm]

/-- The totalized Stieltjes function is continuous, including on the zero branch. -/
theorem continuous_pathStieltjes (m : ℝ≥0 → ℝ) : Continuous (pathStieltjes m) := by
  classical
  by_cases hm : Monotone m ∧ Continuous m
  · have he : (pathStieltjes m : ℝ → ℝ) = fun s => m s.toNNReal :=
      funext (pathStieltjes_apply hm)
    rw [he]
    exact hm.2.comp continuous_real_toNNReal
  · simp only [pathStieltjes, dite_eq_right hm]
    exact continuous_const

/-- The totalized clock measure has no atoms, even on exceptional paths. -/
theorem pathStieltjes_measure_singleton (m : ℝ≥0 → ℝ) (s : ℝ) :
    (pathStieltjes m).measure {s} = 0 := by
  rw [StieltjesFunction.measure_singleton,
    (continuous_pathStieltjes m).continuousAt.continuousWithinAt.leftLim_eq,
    sub_self, ENNReal.ofReal_zero]

/-- The mass of a half-open interval is the increment of a good clock path. -/
theorem pathStieltjes_measure_Ioc {m : ℝ≥0 → ℝ} (hm : Monotone m ∧ Continuous m)
    (s t : ℝ) :
    (pathStieltjes m).measure (Ioc s t) = ENNReal.ofReal (m t.toNNReal - m s.toNNReal) := by
  rw [StieltjesFunction.measure_Ioc, pathStieltjes_apply hm, pathStieltjes_apply hm]

end BGW.StableTrees
