/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.DLocBasic
public import BGW.Skorokhod.JumpDetection

import Mathlib.Data.NNRat.Encodable
import Mathlib.Data.Rat.Encodable

/-! # Jump times as stopping times

The first jump after a rational time with size above a positive rational threshold is a stopping
time for the right-continuous filtration on `DLoc`. Enumerating the rational parameters therefore
gives a countable family of stopping times containing every jump time of every path (the
bounded-horizon version of the jump-time argument of P. W. Millar, Zero-one laws and the minimum
of a Markov process, Trans. Amer. Math. Soc. 226 (1977), 365–391).
-/

@[expose] public section

open MeasureTheory Set Filter Function
open scoped NNReal ENNReal

namespace BGW.Skorokhod

private theorem measurable_eval_filtration {s t : ℝ≥0} (hst : s ≤ t) :
    Measurable[DLoc.filtration t] (DLoc.eval s) :=
  (DLoc.adapted_eval s).mono (DLoc.filtration.mono hst) le_rfl

/-- **The time `σ_{q,ε}` is a stopping time** of the right-continuous filtration, for rational
`q ≥ 0` and rational `ε > 0` (formulated on `DLoc` paths, as a `WithTop ℝ≥0`-valued time). -/
theorem isStoppingTime_firstJumpAbove (q : ℚ≥0) {ε : ℚ} (hε : 0 < ε) :
    IsStoppingTime DLoc.filtration
      (fun f : DLoc => (firstJumpAbove (q : ℝ≥0) (ε : ℝ) f.1 : WithTop ℝ≥0)) := by
  classical
  apply MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro t
  change MeasurableSet[DLoc.filtration t]
    {f : DLoc | firstJumpAbove (q : ℝ≥0) (ε : ℝ) f.1 < (t : ℝ≥0∞)}
  have hset : {f : DLoc |
        (firstJumpAbove (q : ℝ≥0) (ε : ℝ) f.1 : WithTop ℝ≥0) < t} =
      ⋃ ε' : {ε' : ℚ // ε < ε'}, ⋂ n : ℕ, ⋃ a : ℚ≥0, ⋃ b : ℚ≥0,
        {f : DLoc | q < a ∧ a < b ∧ (b : ℝ≥0) < t ∧ ((b : ℝ) - a < 1 / (n + 1)) ∧
          ((ε' : ℚ) : ℝ) ≤ |f.1 (b : ℝ≥0) - f.1 (a : ℝ≥0)|} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
    rw [firstJumpAbove_lt_iff f.2 q hε t]
    constructor
    · rintro ⟨ε', hεε', h⟩
      refine ⟨⟨ε', hεε'⟩, fun n ↦ ?_⟩
      obtain ⟨a, b, hqa, hab, hbt, hn, hjump⟩ := h n
      exact ⟨a, b, hqa, hab, hbt, hn, hjump⟩
    · rintro ⟨⟨ε', hεε'⟩, h⟩
      refine ⟨ε', hεε', fun n ↦ ?_⟩
      obtain ⟨a, b, hqa, hab, hbt, hn, hjump⟩ := h n
      exact ⟨a, b, hqa, hab, hbt, hn, hjump⟩
  rw [hset]
  apply MeasurableSet.iUnion
  intro ε'
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro b
  by_cases hcond : q < a ∧ a < b ∧ (b : ℝ≥0) < t ∧
      ((b : ℝ) - a < 1 / (n + 1))
  · have hbt : (b : ℝ≥0) ≤ t := hcond.2.2.1.le
    have hab : (a : ℝ≥0) < (b : ℝ≥0) := by exact_mod_cast hcond.2.1
    have hat : (a : ℝ≥0) ≤ t := hab.le.trans hbt
    have hmeas : MeasurableSet[DLoc.filtration t]
        {f : DLoc | ((ε' : ℚ) : ℝ) ≤ |f.1 (b : ℝ≥0) - f.1 (a : ℝ≥0)|} := by
      apply measurableSet_le measurable_const
      exact continuous_abs.measurable.comp
        ((measurable_eval_filtration hbt).sub (measurable_eval_filtration hat))
    convert hmeas using 1
    ext f
    simp only [Set.mem_ofPred_eq]
    constructor
    · exact fun hf ↦ hf.2.2.2.2
    · exact fun hf ↦ ⟨hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2, hf⟩
  · have hempty : {f : DLoc | q < a ∧ a < b ∧ (b : ℝ≥0) < t ∧
          ((b : ℝ) - a < 1 / (n + 1)) ∧
          ((ε' : ℚ) : ℝ) ≤ |f.1 (b : ℝ≥0) - f.1 (a : ℝ≥0)|} = ∅ := by
      ext f
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hf
      exact hcond ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩
    have hem : MeasurableSet[DLoc.filtration t] (∅ : Set DLoc) :=
      @MeasurableSet.empty DLoc (DLoc.filtration t)
    exact hem.congr hempty.symm

/-- **Jump enumeration.** There are countably many stopping times of `DLoc.filtration` such
that every path's every jump time `t > 0` is one of them. -/
theorem exists_jumpStoppingTimes :
    ∃ J : ℕ → DLoc → WithTop ℝ≥0,
      (∀ n, IsStoppingTime DLoc.filtration (J n)) ∧
      ∀ (f : DLoc) (t : ℝ≥0), 0 < t → f.1 t ≠ Function.leftLim f.1 t →
        ∃ n, J n f = (t : WithTop ℝ≥0) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat (ℚ≥0 × {ε : ℚ // 0 < ε})
  let J : ℕ → DLoc → WithTop ℝ≥0 := fun n f =>
    (firstJumpAbove ((e n).1 : ℝ≥0) (((e n).2 : ℚ) : ℝ) f.1 : WithTop ℝ≥0)
  refine ⟨J, fun n ↦ isStoppingTime_firstJumpAbove (e n).1 (e n).2.2, ?_⟩
  intro f t ht hjump
  obtain ⟨q, ε, hε, hfirst⟩ := exists_rat_firstJumpAbove_eq f.2 ht hjump
  obtain ⟨n, hn⟩ := he (q, ⟨ε, hε⟩)
  refine ⟨n, ?_⟩
  dsimp [J]
  rw [hn]
  exact hfirst

end BGW.Skorokhod
