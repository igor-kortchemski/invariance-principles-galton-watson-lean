/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionClocks

/-!
# Non-jump ladder-time convergence

Ladder times at non-jump levels converge under J1 convergence of the rescaled walks.
-/

@[expose] public section

open Filter Topology
open scoped NNReal
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees

/-- **Ladder times converge at non-jump levels.**  Level `x` is read at index `⌈x B_n⌉`. -/
theorem tendsto_ladderTime_of_not_mem_passageJumpSet {B : ℕ → ℝ}
    (hB : Tendsto B atTop atTop) {M : ℝ≥0} (ω : ℕ → ℕ → ℝ)
    (hω : ∀ n i, IsSkipFreeIncrement (ω n i)) {f : DLoc} (hf : GoodLongExtractionPath M f)
    (hu : Tendsto (fun n => realStepPath (M : ℝ) n (B n) (ω n)) atTop
      (𝓝 (DLoc.restrict M f)))
    {x : ℝ≥0} (hx : x ∉ passageJumpSet f) (hxM : passageTime x f < M) :
    (∀ᶠ n in atTop, walkHitTime ⌈(x : ℝ) * B n⌉₊ (ω n) ≠ ⊤) ∧
      Tendsto (fun n => (ladderTime (ω n) ⌈(x : ℝ) * B n⌉₊ : ℝ) / n) atTop
        (𝓝 ((passageTime x f : ℝ≥0) : ℝ)) := by
  -- Weak-hit continuity itself does not require the skip-free restriction; `hω` is kept in the
  -- statement as part of the interface shared with the other extraction theorems.
  have _hω := hω
  by_cases hx0 : x = 0
  · subst x
    have hhit (n : ℕ) : walkHitTime 0 (ω n) = 0 := by
      apply le_antisymm ?_ bot_le
      exact iInf_le_of_le 0 (iInf_le _ (by simp [partialSum]))
    constructor
    · exact Filter.Eventually.of_forall fun n => by simp [hhit]
    · simp [hf.passageZero, ladderTime, hhit]
  obtain ⟨σ, hσ, he⟩ := tendsto_iff_exists_timeChange.mp hu
  have hc : Tendsto (fun n => (⌈(x : ℝ) * B n⌉₊ : ℝ) / B n) atTop (𝓝 (x : ℝ)) :=
    (tendsto_nat_ceil_mul_div_atTop x.2).comp hB
  have hpos : ∀ᶠ n in atTop, 0 < B n := hB.eventually (eventually_gt_atTop 0)
  have hupper (b : ℝ) (hb : (passageTime x f : ℝ) < b) :
      ∀ᶠ n in atTop, walkHitTime ⌈(x : ℝ) * B n⌉₊ (ω n) ≠ ⊤ ∧
        (ladderTime (ω n) ⌈(x : ℝ) * B n⌉₊ : ℝ) / n < b := by
    let v : ℝ≥0 := min M (Real.toNNReal b)
    have hv : passageTime x f < v := by
      apply lt_min hxM
      exact_mod_cast (show (passageTime x f : ℝ) < (Real.toNNReal b : ℝ) by
        rw [Real.coe_toNNReal _ (le_trans (passageTime x f).2 hb.le)]
        exact hb)
    obtain ⟨t, htv, ht⟩ := exists_eval_lt_of_firstPassageBelow_lt
      (show firstPassageBelow x f < (v : WithTop ℝ≥0) by
        rw [hf.finitePassage x]
        exact_mod_cast hv)
    have htM : t < M := htv.trans_le (min_le_left _ _)
    have htb : (t : ℝ) < b := by
      have hvb : (v : ℝ) ≤ b := by
        dsimp [v]
        rw [NNReal.coe_min, Real.coe_toNNReal _
          (le_trans (passageTime x f).2 hb.le)]
        exact min_le_right _ _
      exact (show (t : ℝ) < v by exact_mod_cast htv).trans_le hvb
    let t' : Set.Icc (0 : ℝ) (M : ℝ) := ⟨t, t.2, by exact_mod_cast htM.le⟩
    have hs := tendsto_extraction_aligned_eval he t'
    have ht' : (DLoc.restrict M f) t' < -(x : ℝ) := ht
    filter_upwards [hpos, eventually_gt_atTop 0,
      hs.eventually_lt hc.neg ht',
      (tendsto_extraction_clock M.2 hσ t').eventually_lt_const htb] with n hn hn0 hnval hnt
    have hval : realStepPath (M : ℝ) n (B n) (ω n) (σ n t') ≤
        -(⌈(x : ℝ) * B n⌉₊ : ℝ) / B n := by
      simpa only [neg_div] using hnval.le
    obtain ⟨hfin, hbound⟩ := ladderTime_le_of_stepPath_le hn0 hn (σ n t') hval
    exact ⟨hfin, hbound.trans_lt hnt⟩
  have hfin : ∀ᶠ n in atTop, walkHitTime ⌈(x : ℝ) * B n⌉₊ (ω n) ≠ ⊤ :=
    (hupper ((passageTime x f : ℝ) + 1) (by linarith)).mono fun _ hn => hn.1
  refine ⟨hfin, tendsto_order.mpr ⟨?_, ?_⟩⟩
  · intro a ha
    by_cases ha0 : a < 0
    · exact Filter.Eventually.of_forall fun n =>
        ha0.trans_le (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have ha0 : 0 ≤ a := le_of_not_gt ha0
    obtain ⟨t, hat, htt⟩ := exists_between ha
    let t' : ℝ≥0 := ⟨t, ha0.trans hat.le⟩
    have htpass : t' < passageTime x f := htt
    obtain ⟨y, hyx, hyt⟩ := exists_lower_passage_barrier hf hx htpass
    have hxy : (y : ℝ) < x := by exact_mod_cast hyx
    let ε : ℝ := ((x : ℝ) - y) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    have hgap : -(x : ℝ) + ε < -(y : ℝ) := by dsimp [ε]; linarith
    let s : Set.Icc (0 : ℝ) (M : ℝ) :=
      ⟨t, t'.2, by exact_mod_cast (htpass.trans hxM).le⟩
    have hclock := (tendsto_extraction_clock M.2 hσ s).eventually_const_lt hat
    have hbarrier := (hc.neg.add_const ε).eventually_lt_const hgap
    filter_upwards [hfin, hpos, eventually_gt_atTop 0, hclock, hbarrier,
      eventually_extraction_error_lt he hε] with n hnfin hnB hn0 hnclock hnbar hnerr
    apply hnclock.trans_le
    by_contra hgt
    have htime : (ladderTime (ω n) ⌈(x : ℝ) * B n⌉₊ : ℝ) / n < (σ n s : ℝ) :=
      lt_of_not_ge hgt
    let k := ladderTime (ω n) ⌈(x : ℝ) * B n⌉₊
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    let q : Set.Icc (0 : ℝ) (M : ℝ) :=
      ⟨(k : ℝ) / n, div_nonneg (Nat.cast_nonneg _) hn'.le,
        htime.le.trans (σ n s).2.2⟩
    let z := (σ n).symm q
    have hzs : z ≤ s := by
      apply (σ n).le_iff_le.mp
      rw [show σ n z = q from (σ n).apply_symm_apply q]
      exact htime.le
    let zNN : ℝ≥0 := ⟨(z : ℝ), z.2.1⟩
    have hzpass : zNN < passageTime y f :=
      lt_of_le_of_lt (by exact_mod_cast hzs) hyt
    have hzval : -(y : ℝ) ≤ (DLoc.restrict M f) z := by
      apply le_eval_of_lt_strictPassageBelow (f := f)
        (s := zNN)
      change (zNN : WithTop ℝ≥0) < firstPassageBelow y f
      rw [hf.finitePassage y]
      exact_mod_cast hzpass
    have hgrid : realStepPath (M : ℝ) n (B n) (ω n) (σ n z) =
        partialSum (ω n) k / B n := by
      have hmul : (n : ℝ) * ((k : ℝ) / n) = k := by field_simp
      simp only [z, OrderIso.apply_symm_apply, realStepPath_apply, q, hmul,
        Nat.floor_natCast]
    have hhit : partialSum (ω n) k / B n ≤ -(⌈(x : ℝ) * B n⌉₊ : ℝ) / B n :=
      (div_le_div_iff_of_pos_right hnB).mpr (partialSum_ladderTime_le hnfin)
    have herr := hnerr z
    rw [hgrid, Real.dist_eq, abs_lt] at herr
    rw [neg_div] at hhit
    linarith [herr.1]
  · intro b hb
    exact (hupper b hb).mono fun _ hn => hn.2

end BGW.StableTrees
