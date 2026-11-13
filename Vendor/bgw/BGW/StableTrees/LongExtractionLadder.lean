/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionDefs

/-!
# Deterministic ladder-time estimates for long-block extraction

Strict barriers transfer to weak walk hits under J1 time changes.
-/

@[expose] public section

open Filter Topology
open scoped NNReal
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees

/-- A walk value below the barrier bounds the finite ladder time.
Reference: Billingsley (1999), Chapter 3. -/
theorem ladderTime_le_of_stepPath_le {M b : ℝ} {n r : ℕ} {ω : ℕ → ℝ}
    (hn : 0 < n) (hb : 0 < b) (t : Set.Icc (0 : ℝ) M)
    (ht : realStepPath M n b ω t ≤ -(r : ℝ) / b) :
    walkHitTime r ω ≠ ⊤ ∧ (ladderTime ω r : ℝ) / n ≤ t := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hval : partialSum ω ⌊(n : ℝ) * (t : ℝ)⌋₊ ≤ -(r : ℝ) := by
    exact (div_le_div_iff_of_pos_right hb).mp ht
  have hhit : walkHitTime r ω ≤ (⌊(n : ℝ) * (t : ℝ)⌋₊ : ℕ∞) :=
    iInf_le_of_le _ (iInf_le _ hval)
  have hfin : walkHitTime r ω ≠ ⊤ := ne_top_of_le_ne_top (by simp) hhit
  refine ⟨hfin, ?_⟩
  have hnat : ladderTime ω r ≤ ⌊(n : ℝ) * (t : ℝ)⌋₊ := by
    rw [← ENat.natCast_toNat hfin] at hhit
    exact_mod_cast hhit
  apply (div_le_iff₀ hn').mpr
  have hcast : (ladderTime ω r : ℝ) ≤ (⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast hnat
  exact hcast.trans (by
    simpa [mul_comm] using Nat.floor_le (mul_nonneg hn'.le t.2.1))

/-- A finite ladder time attains its weak barrier.
Reference: Billingsley (1999), Chapter 3. -/
theorem partialSum_ladderTime_le {r : ℕ} {ω : ℕ → ℝ}
    (hfin : walkHitTime r ω ≠ ⊤) : partialSum ω (ladderTime ω r) ≤ -(r : ℝ) := by
  have heq : walkHitTime r ω = (ladderTime ω r : ℕ∞) :=
    (ENat.natCast_toNat hfin).symm
  conv_lhs at heq => rw [walkHitTime, ← iInf_subtype'']
  obtain ⟨⟨⟨k, hk⟩, heqk⟩, _⟩ := ENat.iInf_eq_natCast_iff.mp heq
  have hk' : k = ladderTime ω r := by exact_mod_cast heqk
  exact hk' ▸ hk

/-- Non-jump levels have equal left and right finite passage times.
Reference: Billingsley (1999), Chapter 3. -/
private theorem passageTimeMinus_eq_of_not_mem {M : ℝ≥0} {f : DLoc}
    (hf : GoodLongExtractionPath M f) {x : ℝ≥0} (hx : x ∉ passageJumpSet f) :
    passageTimeMinus x f = passageTime x f := by
  have hb : (⨆ y : Set.Iio x, firstPassageBelow y f) ≤ firstPassageBelow x f :=
    iSup_le fun y => firstPassageBelow_mono f y.2.le
  have hfin : (⨆ y : Set.Iio x, firstPassageBelow y f) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hf.finitePassage x]; exact WithTop.coe_ne_top) hb
  have heq : (⨆ y : Set.Iio x, firstPassageBelow y f) =
      (passageTimeMinus x f : WithTop ℝ≥0) := by
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hfin
    simp only [passageTimeMinus, ← ht, WithTop.untopD_coe]
  rw [heq, hf.finitePassage x] at hb
  have hle : passageTimeMinus x f ≤ passageTime x f := by exact_mod_cast hb
  by_cases hx0 : x = 0
  · subst x
    exact le_antisymm (by simpa [hf.passageZero] using hle)
      (by simp [hf.passageZero])
  · apply le_antisymm hle
    exact le_of_not_gt fun hlt => hx ⟨pos_iff_ne_zero.mpr hx0, hlt⟩

/-- Before passage at a non-jump positive level, a smaller barrier still has not been hit.
Reference: Billingsley (1999), Chapter 3. -/
theorem exists_lower_passage_barrier {M : ℝ≥0} {f : DLoc}
    (hf : GoodLongExtractionPath M f) {x t : ℝ≥0}
    (hx : x ∉ passageJumpSet f) (ht : t < passageTime x f) :
    ∃ y : ℝ≥0, y < x ∧ t < passageTime y f := by
  have hfin : (⨆ y : Set.Iio x, firstPassageBelow y f) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := firstPassageBelow x f)
    · rw [hf.finitePassage x]
      exact WithTop.coe_ne_top
    · exact iSup_le fun y => firstPassageBelow_mono f y.2.le
  have heq : (⨆ y : Set.Iio x, firstPassageBelow y f) =
      (passageTimeMinus x f : WithTop ℝ≥0) := by
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hfin
    simp only [passageTimeMinus, ← ht, WithTop.untopD_coe]
  rw [passageTimeMinus_eq_of_not_mem hf hx] at heq
  have hlt : (t : WithTop ℝ≥0) < ⨆ y : Set.Iio x, firstPassageBelow y f := by
    rw [heq]
    exact_mod_cast ht
  obtain ⟨y, hy⟩ := (lt_iSup_iff).mp hlt
  refine ⟨y, y.2, ?_⟩
  rw [hf.finitePassage y] at hy
  exact_mod_cast hy

end BGW.StableTrees
