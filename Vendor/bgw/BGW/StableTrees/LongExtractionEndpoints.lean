/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionBrackets
public import BGW.StableTrees.LongExtractionExclusion

/-!
# Endpoints of the first long block

A matching long block is the first long block: any preceding long block would end too early.
-/

@[expose] public section

open Filter Topology
open scoped NNReal
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees

/-- **Endpoint matching** (finding 1): the first long block's endpoints converge to the
selected excursion interval `(T_{L-}, T_L)`.  No convergence of extraction is assumed. -/
theorem tendsto_firstLongBlock_endpoints {B : ℕ → ℝ} (hB : Tendsto B atTop atTop)
    {M : ℝ≥0} (ω : ℕ → ℕ → ℝ) (hω : ∀ n i, IsSkipFreeIncrement (ω n i))
    {f : DLoc} (hf : GoodLongExtractionPath M f)
    (hu : Tendsto (fun n => realStepPath (M : ℝ) n (B n) (ω n)) atTop
      (𝓝 (DLoc.restrict M f))) :
    Tendsto (fun n => extractionEndpoints n (ω n)) atTop (𝓝 (firstLongEnds f)) := by
  let g := passageTimeMinus (firstLongLabel f) f
  have hgd : g < passageTime (firstLongLabel f) f := hf.isLeast_firstLongLabel.1.1.2
  obtain ⟨H, hgH, hH⟩ := exists_between
    (lt_min (lt_add_of_pos_right g zero_lt_one) (hgd.trans hf.end_lt))
  have hno := eventually_no_early_longBlock hB ω hω hf hu (le_of_lt (lt_min_iff.mp hH).2)
    (lt_min_iff.mp hH).1
  have hbox (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n in atTop,
      (firstLongEnds f).1 - ε < (extractionEndpoints n (ω n)).1 ∧
      (extractionEndpoints n (ω n)).1 < (firstLongEnds f).1 + ε ∧
      (firstLongEnds f).2 - ε < (extractionEndpoints n (ω n)).2 ∧
      (extractionEndpoints n (ω n)).2 < (firstLongEnds f).2 + ε := by
    let δ : ℝ := min (ε / 2) (((H : ℝ) - g) / 2)
    have hgH' : (g : ℝ) < H := by exact_mod_cast hgH
    have hδ : 0 < δ := lt_min (by positivity) (by linarith only [hgH'])
    have hδε : δ ≤ ε / 2 := min_le_left _ _
    have hδH : δ ≤ ((H : ℝ) - g) / 2 := min_le_right _ _
    filter_upwards [hno, eventually_exists_longBlock_near_firstLong hB ω hω hf hu hδ]
      with n hnno hnmatch
    obtain ⟨r, hr, hrlow, hrup, hdlow, hdup⟩ := hnmatch
    have hrH : (ladderTime (ω n) r : ℝ) / n < H := by
      change (ladderTime (ω n) r : ℝ) / n < (g : ℝ) + δ at hrup
      linarith only [hrup, hδH, hgH']
    have hfirstmem : firstLongIndex n (ω n) ∈ longBlockSet n (ω n) :=
      csInf_mem ⟨r, hr⟩
    have hfirstr : firstLongIndex n (ω n) ≤ r := csInf_le (OrderBot.bddBelow _) hr
    have heq : firstLongIndex n (ω n) = r := by
      apply le_antisymm hfirstr
      apply le_of_not_gt
      intro hlt
      have hle := (ladderTime_mono_of_finite (Nat.succ_le_of_lt hlt)
        (ladderTime_mono_of_finite (Nat.le_succ r) hr.1).1).2
      have htime : (ladderTime (ω n) (firstLongIndex n (ω n) + 1) : ℝ) / n ≤
          (ladderTime (ω n) r : ℝ) / n := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
        exact_mod_cast hle
      exact (hnno _ hfirstmem).not_ge (htime.trans hrH.le)
    simp only [extractionEndpoints, heq]
    constructor
    · linarith only [hrlow, hδε, hε]
    constructor
    · linarith only [hrup, hδε, hε]
    constructor
    · linarith only [hdlow, hδε, hε]
    · linarith only [hdup, hδε, hε]
  rw [nhds_prod_eq, Filter.tendsto_prod_iff']
  constructor
  · apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [hbox ((firstLongEnds f).1 - a) (sub_pos.mpr ha)] with n hn
      linarith only [hn.1]
    · intro b hb
      filter_upwards [hbox (b - (firstLongEnds f).1) (sub_pos.mpr hb)] with n hn
      linarith only [hn.2.1]
  · apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [hbox ((firstLongEnds f).2 - a) (sub_pos.mpr ha)] with n hn
      linarith only [hn.2.2.1]
    · intro b hb
      filter_upwards [hbox (b - (firstLongEnds f).2) (sub_pos.mpr hb)] with n hn
      linarith only [hn.2.2.2]

end BGW.StableTrees
