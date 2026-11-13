/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionPlateauLimit
public import BGW.StableTrees.LongExtractionPlateaus
import Mathlib.Topology.Sequences

/-!
# Excluding early long discrete blocks

A hypothetical sequence of early long blocks has compact endpoint limits. Their running
infima agree, contradicting the least-long-label property.
-/

@[expose] public section

open Filter Topology
open scoped NNReal
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees

/-- Long blocks cannot end before a fixed time strictly below the first start plus one.
Reference: Billingsley (1999), Chapter 3. -/
theorem eventually_no_early_longBlock {B : ℕ → ℝ} (hB : Tendsto B atTop atTop)
    {M : ℝ≥0} (ω : ℕ → ℕ → ℝ) (hω : ∀ n i, IsSkipFreeIncrement (ω n i))
    {f : DLoc} (hf : GoodLongExtractionPath M f)
    (hu : Tendsto (fun n => realStepPath (M : ℝ) n (B n) (ω n)) atTop
      (𝓝 (DLoc.restrict M f)))
    {H : ℝ≥0} (hHM : H ≤ M) (hH : H < passageTimeMinus (firstLongLabel f) f + 1) :
    ∀ᶠ n in atTop, ∀ r ∈ longBlockSet n (ω n),
      (H : ℝ) < (ladderTime (ω n) (r + 1) : ℝ) / n := by
  classical
  by_contra h
  have hbad : ∃ᶠ n in atTop, 0 < n ∧ ∃ r, r ∈ longBlockSet n (ω n) ∧
      (ladderTime (ω n) (r + 1) : ℝ) / n ≤ H := by
    have hfreq : ∃ᶠ n in atTop, ∃ r, r ∈ longBlockSet n (ω n) ∧
        (ladderTime (ω n) (r + 1) : ℝ) / n ≤ H := by
      simpa only [Filter.not_eventually, not_forall, not_lt, exists_prop] using h
    exact (hfreq.and_eventually (eventually_gt_atTop 0)).mono
      fun _ hn => ⟨hn.2, hn.1⟩
  obtain ⟨ns, hns, hbadns⟩ := exists_seq_forall_of_frequently hbad
  choose r hrmem hrH using fun k => (hbadns k).2
  have hfinite (k : ℕ) : walkHitTime (r k + 1) (ω (ns k)) ≠ ⊤ := (hrmem k).1
  have hmono (k : ℕ) : ladderTime (ω (ns k)) (r k) ≤
      ladderTime (ω (ns k)) (r k + 1) :=
    (ladderTime_mono_of_finite (Nat.le_succ _) (hfinite k)).2
  let ends (k : ℕ) : ℝ × ℝ :=
    ((ladderTime (ω (ns k)) (r k) : ℝ) / ns k,
      (ladderTime (ω (ns k)) (r k + 1) : ℝ) / ns k)
  have hends (k : ℕ) : ends k ∈ Set.Icc (0 : ℝ) (H : ℝ) ×ˢ Set.Icc (0 : ℝ) (H : ℝ) := by
    have hstart : (ends k).1 ≤ (ends k).2 := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast hmono k
    exact ⟨⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), hstart.trans (hrH k)⟩,
      ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), hrH k⟩⟩
  obtain ⟨v, hv, φ, hφ, hlim⟩ :=
    (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hends
  let a : ℝ≥0 := ⟨v.1, hv.1.1⟩
  let b : ℝ≥0 := ⟨v.2, hv.2.1⟩
  have hlen (k : ℕ) : (1 : ℝ) ≤ (ends k).2 - (ends k).1 := by
    have hn : (0 : ℝ) < ns k := by exact_mod_cast (hbadns k).1
    have hsize : (ns k : ℝ) ≤ (ladderTime (ω (ns k)) (r k + 1) : ℝ) -
        ladderTime (ω (ns k)) (r k) := by
      have hcast : (ns k : ℝ) ≤
          (ladderTime (ω (ns k)) (r k + 1) - ladderTime (ω (ns k)) (r k) : ℕ) := by
        exact_mod_cast (hrmem k).2
      rwa [Nat.cast_sub (hmono k)] at hcast
    change 1 ≤ _ / _ - _ / _
    rw [← sub_div]
    exact (le_div_iff₀ hn).mpr (by simpa only [one_mul] using hsize)
  have hlenlim : (1 : ℝ) ≤ (b : ℝ) - a :=
    ge_of_tendsto (hlim.snd_nhds.sub hlim.fst_nhds)
      (Filter.Eventually.of_forall fun k => hlen (φ k))
  have hab : a ≤ b := by
    change (a : ℝ) ≤ b
    linarith only [hlenlim]
  have hlenNN : (1 : ℝ≥0) ≤ b - a := by
    exact_mod_cast hlenlim
  let s (k : ℕ) : Set.Icc (0 : ℝ) (M : ℝ) :=
    ⟨(ends (φ k)).1, (hends (φ k)).1.1,
      (hends (φ k)).1.2.trans (by exact_mod_cast hHM)⟩
  let t (k : ℕ) : Set.Icc (0 : ℝ) (M : ℝ) :=
    ⟨(ends (φ k)).2, (hends (φ k)).2.1,
      (hends (φ k)).2.2.trans (by exact_mod_cast hHM)⟩
  have heq : runningInfLoc f a = runningInfLoc f b := by
    apply runningInf_eq_of_tendsto_ladderBlocks (a := a) (b := b)
      (Filter.Eventually.of_forall fun k => (hbadns (φ k)).1)
      (hB.comp (hns.comp hφ.tendsto_atTop))
      (fun k => ω (ns (φ k))) (fun k i => hω _ i) hf.infContinuous
      (hu.comp (hns.comp hφ.tendsto_atTop)) (fun k => r (φ k))
      (Filter.Eventually.of_forall fun k => hfinite (φ k)) s t
      (fun _ => rfl) (fun _ => rfl) hlim.fst_nhds hlim.snd_nhds
  have hb : b < passageTimeMinus (firstLongLabel f) f + 1 :=
    (show b ≤ H from hv.2.2).trans_lt hH
  exact no_long_runningInf_plateau_ending_early hf hlenNN hb heq

end BGW.StableTrees
