/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StablePassageSubordinator
public import BGW.StableTrees.ReflectedRestart

/-! # Strict infimum crossings and passage times

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Simultaneously at all levels and times, a strict infimum crossing occurs precisely
when the corresponding strict passage time is before the observation time. -/
theorem ae_localTime_gt_iff_passageTime_lt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x t : ℝ≥0,
      (x : ℝ) < localTime f t ↔ passageTime x f < t := by
  filter_upwards [ae_passageTime_eq_firstPassageBelow hθ, ae_localTime_passageTime hθ]
    with f hT hL
  intro x t
  constructor
  · intro h
    have hI : runningInfLoc f t < -(x : ℝ) := by
      dsimp [localTime] at h
      linarith
    have hle : firstPassageBelow x f ≤ (t : WithTop ℝ≥0) := by
      rw [firstPassageBelow_eq_inf_runningInf]
      exact iInf_le_of_le t (iInf_le _ hI)
    rw [hT.1 x] at hle
    have hle' : passageTime x f ≤ t := WithTop.coe_le_coe.mp hle
    apply lt_of_le_of_ne hle'
    intro he
    have hx := (hL x).1
    rw [he] at hx
    exact h.ne' hx
  · intro h
    have hh : firstPassageBelow x f < (t : WithTop ℝ≥0) := by
      rw [hT.1 x]
      exact_mod_cast h
    change (⨅ u : ℝ≥0, ⨅ (_ : f.1 u < -(x : ℝ)), (u : WithTop ℝ≥0)) < _ at hh
    obtain ⟨u, hu⟩ := iInf_lt_iff.mp hh
    obtain ⟨hval, hut⟩ := iInf_lt_iff.mp hu
    have hut' : u ≤ t := (WithTop.coe_lt_coe.mp hut).le
    have hb := runningInfLoc_le_eval f t ⟨u, hut'⟩
    dsimp [localTime]
    linarith

end BGW.StableTrees
