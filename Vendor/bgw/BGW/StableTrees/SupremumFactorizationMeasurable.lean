/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StablePassageSubordinator
public import BGW.StableTrees.ReflectedRestart

/-! # Measurability of joint infimum occupation tests

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Joint nonnegative tests of the infimum local time and the reflected position are measurable. -/
theorem measurable_infimum_test {F G : ℝ → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) :
    Measurable (fun p : ℝ≥0 × DLoc =>
      F (localTime p.2 p.1) * G ((reflectedFrom 0 p.2).1 p.1)) := by
  have h1 : Measurable (fun p : ℝ≥0 × DLoc => localTime p.2 p.1) :=
    measurable_localTime_uncurry
  have hp : Measurable (fun p : ℝ≥0 × DLoc => ((0 : ℝ≥0), p.2, p.1)) :=
    measurable_const.prodMk (measurable_snd.prodMk measurable_fst)
  have h2 : Measurable (fun p : ℝ≥0 × DLoc => (reflectedFrom 0 p.2).1 p.1) :=
    measurable_reflectedFrom_eval.comp hp
  have hF1 : Measurable (fun p : ℝ≥0 × DLoc => F (localTime p.2 p.1)) := hF.comp h1
  have hG2 : Measurable (fun p : ℝ≥0 × DLoc => G ((reflectedFrom 0 p.2).1 p.1)) := hG.comp h2
  exact hF1.mul hG2

/-- A joint infimum occupation test, bundled before changing the time carrier. -/
noncomputable def infimumTest (F G : ℝ → ℝ≥0∞) (p : ℝ≥0 × DLoc) : ℝ≥0∞ :=
  F (localTime p.2 p.1) * G ((reflectedFrom 0 p.2).1 p.1)

/-- Measurability of the bundled joint infimum test. -/
theorem measurable_infimumTest {F G : ℝ → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) :
    Measurable (infimumTest F G) := measurable_infimum_test hF hG

/-- A joint infimum test read at a real-valued clock time. -/
noncomputable def infimumTestReal (F G : ℝ → ℝ≥0∞) (p : ℝ × DLoc) : ℝ≥0∞ :=
  infimumTest F G (p.1.toNNReal, p.2)

/-- Changing the clock carrier preserves measurability of the bundled test. -/
theorem measurable_infimumTestReal {F G : ℝ → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) : Measurable (infimumTestReal F G) := by
  have hp : Measurable (fun p : ℝ × DLoc => (p.1.toNNReal, p.2)) :=
    (continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd
  exact (measurable_infimumTest hF hG).comp hp

end BGW.StableTrees
