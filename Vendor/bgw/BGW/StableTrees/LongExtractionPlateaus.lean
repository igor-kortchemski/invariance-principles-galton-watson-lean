/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionLadder

/-!
# Exclusion of long plateaus before the selected excursion

A constant running infimum on a nontrivial interval belongs to a passage jump.
The lifetime threshold and the least-long-label property exclude such intervals of length
at least one before the first long excursion.
-/

@[expose] public section

open Filter Topology
open scoped NNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The selected label is the least long label under the good-path predicate.
Reference: Billingsley (1999), Chapter 3. -/
theorem GoodLongExtractionPath.isLeast_firstLongLabel {M : ℝ≥0} {f : DLoc}
    (hf : GoodLongExtractionPath M f) : IsLeast (longLabelSet f) (firstLongLabel f) := by
  obtain ⟨L, hL⟩ := hf.hasLongLabel
  have heq : firstLongLabel f = L := hL.csInf_eq
  exact heq.symm ▸ hL

/-- A running-infimum plateau lies in the closed interval of its passage jump.
Reference: Billingsley (1999), Chapter 3. -/
private theorem passage_interval_of_runningInf_plateau {M : ℝ≥0} {f : DLoc}
    (hf : GoodLongExtractionPath M f) {a b x : ℝ≥0}
    (hab : a < b) (hx : 0 < x)
    (ha : runningInfLoc f a = -(x : ℝ)) (hb : runningInfLoc f b = -(x : ℝ)) :
    x ∈ passageJumpSet f ∧ passageTimeMinus x f ≤ a ∧ b ≤ passageTime x f := by
  have hleft : (⨆ y : Set.Iio x, firstPassageBelow y f) ≤ (a : WithTop ℝ≥0) := by
    apply iSup_le
    intro y
    apply (runningInf_lt_sandwich y a f).2
    rw [ha]
    exact neg_lt_neg (by exact_mod_cast y.2)
  have hfin : (⨆ y : Set.Iio x, firstPassageBelow y f) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hleft
  have hminus : passageTimeMinus x f ≤ a := by
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hfin
    simp only [← hs, WithTop.coe_le_coe] at hleft
    simpa only [passageTimeMinus, ← hs, WithTop.untopD_coe] using hleft
  have hright : b ≤ passageTime x f := by
    by_contra h
    have hpass : firstPassageBelow x f < (b : WithTop ℝ≥0) := by
      rw [hf.finitePassage x]
      exact_mod_cast lt_of_not_ge h
    have hi := (runningInf_lt_sandwich x b f).1 hpass
    rw [hb] at hi
    exact (lt_irrefl _ hi)
  exact ⟨⟨hx, hminus.trans_lt (hab.trans_le hright)⟩, hminus, hright⟩

/-- A running-infimum plateau of length at least one starts after the first long start.
Reference: Billingsley (1999), Chapter 3. -/
private theorem firstLong_start_le_of_runningInf_plateau {M : ℝ≥0} {f : DLoc}
    (hf : GoodLongExtractionPath M f) {a b : ℝ≥0}
    (hlen : 1 ≤ b - a) (heq : runningInfLoc f a = runningInfLoc f b) :
    passageTimeMinus (firstLongLabel f) f ≤ a := by
  have hab : a < b := by
    by_contra h
    have : b - a = 0 := tsub_eq_zero_of_le (le_of_not_gt h)
    rw [this] at hlen
    norm_num at hlen
  have hbpos : 0 < b := a.2.trans_lt hab
  have hi : runningInfLoc f b < 0 := by
    have hpass : firstPassageBelow 0 f < (b : WithTop ℝ≥0) := by
      rw [hf.finitePassage 0, hf.passageZero]
      exact_mod_cast hbpos
    simpa only [NNReal.coe_zero, neg_zero] using
      (runningInf_lt_sandwich 0 b f).1 hpass
  let x : ℝ≥0 := ⟨-runningInfLoc f b, neg_nonneg.mpr hi.le⟩
  have hx : 0 < x := neg_pos.mpr hi
  have hib : runningInfLoc f b = -(x : ℝ) := by
    change runningInfLoc f b = -(-runningInfLoc f b)
    ring
  have hia : runningInfLoc f a = -(x : ℝ) := heq.trans hib
  obtain ⟨hxjump, hxg, hxd⟩ := passage_interval_of_runningInf_plateau hf hab hx hia hib
  have hlong : 1 < passageTime x f - passageTimeMinus x f := by
    have hle : 1 ≤ passageTime x f - passageTimeMinus x f :=
      hlen.trans (tsub_le_tsub hxd hxg)
    exact lt_of_le_of_ne hle (Ne.symm (hf.noLifetimeOne x hxjump))
  have hL := hf.isLeast_firstLongLabel
  have hLx : firstLongLabel f ≤ x := hL.2 ⟨hxjump, hlong⟩
  have hstart : passageTimeMinus (firstLongLabel f) f ≤ passageTimeMinus x f := by
    rcases hLx.eq_or_lt with h | h
    · rw [h]
    · exact hL.1.1.2.le.trans
        (passageTime_lt_passageTimeMinus hf.finitePassage hf.strictMono h).le
  exact hstart.trans hxg

/-- No unit-long plateau can end before one unit after the selected start.
Reference: Billingsley (1999), Chapter 3. -/
theorem no_long_runningInf_plateau_ending_early {M : ℝ≥0} {f : DLoc}
    (hf : GoodLongExtractionPath M f) {a b : ℝ≥0}
    (hlen : 1 ≤ b - a) (hb : b < passageTimeMinus (firstLongLabel f) f + 1) :
    runningInfLoc f a ≠ runningInfLoc f b := by
  intro heq
  have hstart := firstLong_start_le_of_runningInf_plateau hf hlen heq
  have hab : a ≤ b := by
    by_contra h
    have : b - a = 0 := tsub_eq_zero_of_le (le_of_not_ge h)
    rw [this] at hlen
    norm_num at hlen
  have hlen' : a + 1 ≤ b := by
    have h := (le_tsub_iff_right hab).mp hlen
    simpa only [add_comm] using h
  apply hb.not_ge
  calc
    passageTimeMinus (firstLongLabel f) f + 1 ≤ a + 1 := add_le_add hstart le_rfl
    _ ≤ b := hlen'

/-- No interval of length at least one before the selected start has constant running infimum.
Reference: Billingsley (1999), Chapter 3. -/
theorem no_long_runningInf_plateau_before_firstLong {M : ℝ≥0} {f : DLoc}
    (hf : GoodLongExtractionPath M f) {a b : ℝ≥0}
    (hlen : 1 ≤ b - a) (hb : b ≤ passageTimeMinus (firstLongLabel f) f) :
    runningInfLoc f a ≠ runningInfLoc f b := by
  apply no_long_runningInf_plateau_ending_early hf hlen
  exact hb.trans_lt (lt_add_of_pos_right _ zero_lt_one)

end BGW.StableTrees
