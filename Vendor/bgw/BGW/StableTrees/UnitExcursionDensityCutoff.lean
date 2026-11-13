/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionDensityGoodTimes
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Increasing compactly supported endpoint cutoffs

The cutoffs are continuous, take values in `[0,1]`, and equal one eventually at
any fixed endpoint. Their supports include both sides of zero.

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

/-- Continuous endpoint cutoffs increasing to one. -/
noncomputable def prefixCutoff (n : ℕ) (x : ℝ) : ℝ :=
  max 0 (min 1 ((n : ℝ) + 1 - |x|))

/-- Continuity of the endpoint cutoff. -/
theorem continuous_prefixCutoff (n : ℕ) : Continuous (prefixCutoff n) := by
  unfold prefixCutoff
  fun_prop

/-- The cutoff lies between zero and one. -/
theorem prefixCutoff_mem_Icc (n : ℕ) (x : ℝ) : prefixCutoff n x ∈ Icc 0 1 := by
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- The cutoff vanishes outside a bounded interval. -/
theorem hasCompactSupport_prefixCutoff (n : ℕ) : HasCompactSupport (prefixCutoff n) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -(n + 1 : ℝ))
    (b := n + 1))
  intro x hx
  have hpos : 0 < prefixCutoff n x := lt_of_le_of_ne (prefixCutoff_mem_Icc n x).1
    (Ne.symm hx)
  have hlt : |x| < (n : ℝ) + 1 := by
    unfold prefixCutoff at hpos
    have hm : 0 < min 1 ((n : ℝ) + 1 - |x|) :=
      (lt_max_iff.mp hpos).resolve_left (lt_irrefl 0)
    linarith [(lt_min_iff.mp hm).2]
  exact ⟨by linarith [neg_le_abs x], (le_abs_self x).trans hlt.le⟩

/-- Monotonicity in the cutoff radius. -/
theorem monotone_prefixCutoff (x : ℝ) : Monotone (fun n => prefixCutoff n x) := by
  intro n m hnm
  apply max_le_max le_rfl
  apply min_le_min le_rfl
  have hnm' : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
  linarith

/-- Each endpoint eventually lies in the region where the cutoff is one. -/
theorem eventually_prefixCutoff_eq_one (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, prefixCutoff n x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge |x|
  filter_upwards [eventually_ge_atTop N] with n hn
  have hx : |x| ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
  simp only [prefixCutoff, min_eq_left (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1 - |x|),
    max_eq_right zero_le_one]

end BGW.StableTrees
