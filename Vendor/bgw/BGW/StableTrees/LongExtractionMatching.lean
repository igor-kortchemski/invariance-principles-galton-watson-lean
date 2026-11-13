/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionPassage
public import BGW.StableTrees.LongExtractionInterior
public import BGW.StableTrees.LongExtractionPlateaus

/-!
# Matching a compact excursion interior to a discrete block

Absence of ladder hits in an interval forces that interval into one consecutive ladder block.
-/

@[expose] public section

open Filter Topology
open scoped NNReal
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees

/-- The level-zero ladder time is always zero.
Reference: Billingsley (1999), Chapter 3. -/
theorem ladderTime_zero (ω : ℕ → ℝ) : ladderTime ω 0 = 0 := by
  have hhit : walkHitTime 0 ω = 0 := by
    apply le_antisymm ?_ bot_le
    exact iInf_le_of_le 0 (iInf_le _ (by simp [partialSum]))
  simp only [ladderTime, hhit, ENat.toNat_zero]

/-- An interval avoiding all ladder hits lies in one finite consecutive ladder block.
Reference: Billingsley (1999), Chapter 3. -/
theorem exists_ladderBlock_spanning {ω : ℕ → ℝ} {n R : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hfin : walkHitTime R ω ≠ ⊤)
    (hR : b < (ladderTime ω R : ℝ) / n)
    (havoid : ∀ s ≤ R, ¬ (a ≤ (ladderTime ω s : ℝ) / n ∧
      (ladderTime ω s : ℝ) / n ≤ b)) :
    ∃ r, r < R ∧ walkHitTime (r + 1) ω ≠ ⊤ ∧
      (ladderTime ω r : ℝ) / n < a ∧ b < (ladderTime ω (r + 1) : ℝ) / n ∧
      ∀ s ≤ R, (ladderTime ω s : ℝ) / n < a → s ≤ r := by
  classical
  let P : ℕ → Prop := fun s => (ladderTime ω s : ℝ) / n < a
  have hP0 : P 0 := by simpa only [P, ladderTime_zero, Nat.cast_zero, zero_div] using ha
  let r := Nat.findGreatest P R
  have hrle : r ≤ R := Nat.findGreatest_le R
  have hPr : P r := Nat.findGreatest_spec (Nat.zero_le R) hP0
  have hrlt : r < R := by
    apply lt_of_le_of_ne hrle
    intro heq
    rw [heq] at hPr
    exact (not_lt_of_ge (hab.trans hR.le)) hPr
  have hnextfin := (ladderTime_mono_of_finite (Nat.succ_le_of_lt hrlt) hfin).1
  have hnexta : a ≤ (ladderTime ω (r + 1) : ℝ) / n := by
    apply le_of_not_gt
    intro h
    have hle : r + 1 ≤ r := Nat.le_findGreatest (Nat.succ_le_of_lt hrlt) h
    omega
  have hnextb : b < (ladderTime ω (r + 1) : ℝ) / n := by
    apply lt_of_not_ge
    intro h
    exact havoid (r + 1) (Nat.succ_le_of_lt hrlt) ⟨hnexta, h⟩
  exact ⟨r, hrlt, hnextfin, hPr, hnextb,
    fun s hs h => Nat.le_findGreatest hs h⟩

/-- A good long excursion forces the discrete walk to have a long block eventually.
Reference: Billingsley (1999), Chapter 3. -/
theorem eventually_longBlockSet_nonempty {B : ℕ → ℝ} (hB : Tendsto B atTop atTop)
    {M : ℝ≥0} (ω : ℕ → ℕ → ℝ) (hω : ∀ n i, IsSkipFreeIncrement (ω n i))
    {f : DLoc} (hf : GoodLongExtractionPath M f)
    (hu : Tendsto (fun n => realStepPath (M : ℝ) n (B n) (ω n)) atTop
      (𝓝 (DLoc.restrict M f))) :
    ∀ᶠ n in atTop, (longBlockSet n (ω n)).Nonempty := by
  let L := firstLongLabel f
  let g := passageTimeMinus L f
  let d := passageTime L f
  have hL := hf.isLeast_firstLongLabel
  have hgd : g < d := hL.1.1.2
  have hlength : 1 < (d : ℝ) - g := by
    have h := hL.1.2
    change 1 < d - g at h
    exact_mod_cast h
  let δ : ℝ := ((d : ℝ) - g - 1) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let a : ℝ≥0 := ⟨(g : ℝ) + δ, by positivity⟩
  let b : ℝ≥0 := ⟨(d : ℝ) - δ, by
    have heq : (d : ℝ) - δ = (3 * (d : ℝ) + g + 1) / 4 := by
      dsimp only [δ]
      ring
    rw [heq]
    positivity⟩
  have hga : g < a := by change (g : ℝ) < (g : ℝ) + δ; linarith
  have hab : a ≤ b := by change (g : ℝ) + δ ≤ (d : ℝ) - δ; dsimp [δ]; linarith
  have hbd : b < d := by change (d : ℝ) - δ < d; linarith
  have hspan : 1 < (b : ℝ) - a := by
    change 1 < ((d : ℝ) - δ) - ((g : ℝ) + δ)
    dsimp [δ]
    linarith
  obtain ⟨_, _, _, hbound, _, hafter⟩ := hf.regular L hL.1.1
  obtain ⟨c, hc, hR⟩ := hbound a b hga hab hbd
  obtain ⟨m, hdm, hmM⟩ := exists_between hf.end_lt
  have hdm' : d < m := hdm
  obtain ⟨z₁, z₂, _, hzz, _, hz₂, hd₁, hd₂⟩ :=
    hafter (m - d) (tsub_pos_of_lt hdm')
  have hzM : passageTime z₂ f < M := by
    rw [add_tsub_cancel_of_le hdm'.le] at hd₂
    exact hd₂.trans hmM
  have hzb : b < passageTime z₂ f := hbd.trans (hd₁.trans (hf.strictMono hzz))
  obtain ⟨hfinite, htimes⟩ := tendsto_ladderTime_of_not_mem_passageJumpSet
    hB ω hω hf hu hz₂ hzM
  obtain ⟨σ, hσ, he⟩ := tendsto_iff_exists_timeChange.mp hu
  have haM : a ≤ M := (hab.trans hbd.le).trans hf.end_lt.le
  have hbM : b ≤ M := hbd.le.trans hf.end_lt.le
  let a' : Set.Icc (0 : ℝ) (M : ℝ) := ⟨a, a.2, by exact_mod_cast haM⟩
  let b' : Set.Icc (0 : ℝ) (M : ℝ) := ⟨b, b.2, by exact_mod_cast hbM⟩
  have hσa := tendsto_extraction_clock M.2 hσ a'
  have hσb := tendsto_extraction_clock M.2 hσ b'
  have ha0 : (0 : ℝ) < a := (show (0 : ℝ) ≤ g from g.2).trans_lt hga
  have hσspan := (hσb.sub hσa).eventually_const_lt hspan
  have hσR := hσb.eventually_lt htimes (by exact_mod_cast hzb)
  have hBpos := hB.eventually (eventually_gt_atTop 0)
  filter_upwards [hfinite, eventually_gt_atTop 0, hBpos, hσspan, hσR,
    hσa.eventually_const_lt ha0, eventually_extraction_error_lt he (by positivity : 0 < c / 4)]
    with n hnfin hn hnB hnspan hnR hna hnerr
  let R := ⌈(z₂ : ℝ) * B n⌉₊
  have havoid (s : ℕ) (hs : s ≤ R) :
      ¬ ((σ n a' : ℝ) ≤ (ladderTime (ω n) s : ℝ) / n ∧
        (ladderTime (ω n) s : ℝ) / n ≤ (σ n b' : ℝ)) :=
    ladderTime_not_mem_aligned_interior hf.zero haM hbM hc
      (fun t ht₁ ht₂ => (hR t ht₁ ht₂).1) hn hnB (σ n) hnerr
      (ladderTime_mono_of_finite hs hnfin).1
  obtain ⟨r, _, hrfin, hrstart, hrend, _⟩ := exists_ladderBlock_spanning hna
    (show (σ n a' : ℝ) ≤ (σ n b' : ℝ) from (σ n).monotone hab) hnfin hnR havoid
  refine ⟨r, hrfin, ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hdiv : 1 < ((ladderTime (ω n) (r + 1) : ℝ) - ladderTime (ω n) r) / n := by
    rw [sub_div]
    exact hnspan.trans (sub_lt_sub hrend hrstart)
  have hlen : (n : ℝ) < (ladderTime (ω n) (r + 1) : ℝ) - ladderTime (ω n) r := by
    simpa only [one_mul] using (lt_div_iff₀ hn').mp hdiv
  have hmono := (ladderTime_lt_succ (hω n) hrfin).le
  have hlen' : (n : ℝ) ≤ (ladderTime (ω n) (r + 1) - ladderTime (ω n) r : ℕ) := by
    rw [Nat.cast_sub hmono]
    exact hlen.le
  exact_mod_cast hlen'

end BGW.StableTrees
