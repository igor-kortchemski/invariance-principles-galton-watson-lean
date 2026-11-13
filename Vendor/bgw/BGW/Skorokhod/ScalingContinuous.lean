/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Topology.CompactOpen

/-!
# Time and space scaling of continuous paths

Time-space scaling is a continuous operation on continuous paths, with the compact-open topology.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- Time–space scaling of continuous paths (C6.4, continuous coordinates). -/
def timeSpaceScaleC [NormedRing E] (a : ℝ) (hT : 0 ≤ T)
    (p : C(Set.Icc (0 : ℝ) T, E) × E × Set.Ioi (0 : ℝ)) : C(Set.Icc (0 : ℝ) a, E) where
  toFun t := p.2.1 * p.1 ⟨min (p.2.2 * t) T,
    le_min (mul_nonneg (le_of_lt p.2.2.2) t.2.1) hT, min_le_right _ _⟩
  continuous_toFun := by
    apply Continuous.mul continuous_const
    apply p.1.continuous.comp
    apply Continuous.subtype_mk
    fun_prop

/-- On continuous paths, time–space scaling is continuous everywhere (C6.4). -/
theorem continuous_timeSpaceScaleC [NormedRing E] (a : ℝ) (hT : 0 ≤ T) :
    Continuous (timeSpaceScaleC (E := E) a hT) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun q : (C(Set.Icc (0 : ℝ) T, E) × E × Set.Ioi (0 : ℝ)) ×
    Set.Icc (0 : ℝ) a => q.1.2.1 * q.1.1 ⟨min (q.1.2.2 * q.2) T,
      le_min (mul_nonneg (le_of_lt q.1.2.2.2) q.2.2.1) hT, min_le_right _ _⟩)
  fun_prop

end BGW.Skorokhod
