/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxRenewalRestart

/-!
# Occupation partition at weak ascending epochs

Finite weak epochs partition all integer times. The killed occupation at zero in
each cycle is the restarted occupation at that cycle's attained height.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

/-- Weak-epoch finiteness is preserved by every deterministic sequence shift. -/
theorem epochsFinite_shiftSeq {ω : ℕ → ℕ} (hω : EpochsFinite ω) (m : ℕ) :
    EpochsFinite (shiftSeq m ω) := by
  intro i
  let v := weakEpoch (shiftSeq m ω) i
  let u := weakEpoch ω (m + v + 1)
  have hbound : m + v + 1 ≤ u := (strictMono_weakEpoch hω).id_le _
  have hwalk : walk ω (m + v) ≤ walk ω u :=
    (reflGap_zero_iff_record ω u).mp (reflGap_weakEpoch hω _) (m + v) (by omega)
  refine ⟨u - m, by omega, ?_⟩
  rw [walk_shiftSeq, walk_shiftSeq, Nat.add_sub_of_le (by omega : m ≤ u)]
  exact sub_le_sub_right hwalk _

private theorem weakLadderCount_eq_iff {ω : ℕ → ℕ} (hω : EpochsFinite ω) (i n : ℕ) :
    weakLadderCount ω n = i ↔ weakEpoch ω i ≤ n ∧ n < weakEpoch ω (i + 1) := by
  constructor
  · intro he
    rw [← he]
    exact weakEpoch_bracket hω n
  · rintro ⟨hi, hi'⟩
    obtain ⟨hc, hc'⟩ := weakEpoch_bracket hω n
    have hle := (strictMono_weakEpoch hω).lt_iff_lt.mp (hc.trans_lt hi')
    have hge := (strictMono_weakEpoch hω).lt_iff_lt.mp (hi.trans_lt hc')
    omega

/-- Nonnegative sums over time split into finite weak-epoch cycles. -/
theorem tsum_eq_sum_weakCycles {ω : ℕ → ℕ} (hω : EpochsFinite ω) (f : ℕ → ℝ≥0∞) :
    ∑' n : ℕ, f n = ∑' i : ℕ,
      ∑ n ∈ Finset.Ico (weakEpoch ω i) (weakEpoch ω (i + 1)), f n := by
  rw [← ENNReal.tsum_fiberwise f (weakLadderCount ω)]
  apply tsum_congr
  intro i
  rw [tsum_subtype]
  rw [tsum_eq_sum (s := Finset.Ico (weakEpoch ω i) (weakEpoch ω (i + 1)))]
  · apply Finset.sum_congr rfl
    intro n hn
    apply Set.indicator_of_mem
    exact (weakLadderCount_eq_iff hω i n).mpr (Finset.mem_Ico.mp hn)
  · intro n hn
    apply Set.indicator_of_notMem
    intro he
    exact hn (Finset.mem_Ico.mpr ((weakLadderCount_eq_iff hω i n).mp he))

private theorem killedGapEvent_cycle_iff {ω : ℕ → ℕ} (hω : EpochsFinite ω)
    {i n : ℕ} (hi : weakEpoch ω i ≤ n) (hi' : n < weakEpoch ω (i + 1)) (m : ℕ) :
    ω ∈ killedGapEvent m m n ↔ walk ω n = 0 ∧ walk ω (weakEpoch ω i) < (m : ℤ) := by
  change (walk ω n = (m : ℤ) - m ∧ ∀ u ≤ n, walk ω u < (m : ℤ)) ↔ _
  rw [sub_self]
  constructor
  · rintro ⟨hn, hlt⟩
    exact ⟨hn, hlt _ hi⟩
  · rintro ⟨hn, hlt⟩
    refine ⟨hn, fun u hu => ?_⟩
    have he := reflGap_in_cycle hω hi hi'
    unfold reflGap at he
    have hm : (Finset.range (n + 1)).sup' ⟨0, by simp⟩ (walk ω) =
        walk ω (weakEpoch ω i) := by omega
    have hle := Finset.le_sup' (walk ω) (show u ∈ Finset.range (n + 1) by simp; omega)
    rw [hm] at hle
    exact hle.trans_lt hlt

/-- Restarting a cycle identifies its exact-level count with a finite interval count. -/
theorem levelOccupation_epochRestart {ω : ℕ → ℕ} (hω : EpochsFinite ω) (i h : ℕ) :
    levelOccupation h (epochRestart i ω) =
      (((Finset.Ico (weakEpoch ω i) (weakEpoch ω (i + 1))).filter
        (fun u => walk ω (weakEpoch ω i) - walk ω u = (h : ℤ))).card : ℝ≥0∞) := by
  have hs := epochsFinite_shiftSeq hω (weakEpoch ω i)
  unfold epochRestart
  rw [levelOccupation_eq_card hs]
  rw [weakEpoch_shift_duration hω i]
  congr 1
  symm
  apply Finset.card_bij (fun u _ => u - weakEpoch ω i)
  · intro u hu
    obtain ⟨hu, hp⟩ := Finset.mem_filter.mp hu
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hu
    have hn : u - weakEpoch ω i < weakEpoch (shiftSeq (weakEpoch ω i) ω) 1 := by
      rw [weakEpoch_shift_duration hω i]
      omega
    have hg := reflGap_in_cycle hs (i := 0) (u := u - weakEpoch ω i) (by simp) hn
    simp only [weakEpoch_zero] at hg
    have hz : walk (shiftSeq (weakEpoch ω i) ω) 0 = 0 := by simp [walk]
    rw [hz, walk_shiftSeq, Nat.add_sub_of_le hlo] at hg
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro u hu v hv he
    have hu' := (Finset.mem_Ico.mp (Finset.mem_filter.mp hu).1).1
    have hv' := (Finset.mem_Ico.mp (Finset.mem_filter.mp hv).1).1
    omega
  · intro u hu
    obtain ⟨hu, hp⟩ := Finset.mem_filter.mp hu
    obtain ⟨_, hhi⟩ := Finset.mem_Ico.mp hu
    refine ⟨weakEpoch ω i + u, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
      ⟨by omega, by omega⟩, ?_⟩, by omega⟩
    have hn : u < weakEpoch (shiftSeq (weakEpoch ω i) ω) 1 := by
      rwa [weakEpoch_shift_duration hω i]
    have hg := reflGap_in_cycle hs (i := 0) (u := u) (by simp) hn
    simp only [weakEpoch_zero] at hg
    have hz : walk (shiftSeq (weakEpoch ω i) ω) 0 = 0 := by simp [walk]
    rw [hz, walk_shiftSeq] at hg
    omega

private theorem killed_cycle_reward {ω : ℕ → ℕ} (hω : EpochsFinite ω) (i m : ℕ) :
    (∑ n ∈ Finset.Ico (weakEpoch ω i) (weakEpoch ω (i + 1)),
      (killedGapEvent m m n).indicator (fun _ => (1 : ℝ≥0∞)) ω) =
    ∑ h ∈ Finset.range m, {ξ | walk ξ (weakEpoch ξ i) = (h : ℤ)}.indicator
      (fun ξ => levelOccupation h (epochRestart i ξ)) ω := by
  let h := weakEpochHeight ω i
  have hcast : (h : ℤ) = walk ω (weakEpoch ω i) := weakEpochHeight_cast hω i
  by_cases hlt : walk ω (weakEpoch ω i) < (m : ℤ)
  · have hmem : h ∈ Finset.range m := Finset.mem_range.mpr (by omega)
    have he : (∑ h' ∈ Finset.range m, {ξ | walk ξ (weakEpoch ξ i) = (h' : ℤ)}.indicator
        (fun ξ => levelOccupation h' (epochRestart i ξ)) ω) =
        levelOccupation h (epochRestart i ω) := by
      rw [Finset.sum_eq_single h]
      · apply Set.indicator_of_mem
        exact hcast.symm
      · intro h' _ hne
        apply Set.indicator_of_notMem
        intro heq
        change walk ω (weakEpoch ω i) = (h' : ℤ) at heq
        have : h' = h := by omega
        exact hne this
      · exact fun hn => (hn hmem).elim
    rw [he, levelOccupation_epochRestart hω]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn, hn'⟩ := Finset.mem_Ico.mp hn
    have hk := killedGapEvent_cycle_iff hω hn hn' m
    have hg : walk ω (weakEpoch ω i) - walk ω n = (h : ℤ) ↔ walk ω n = 0 := by omega
    simp only [Set.indicator_apply, hk, hlt, and_true, hg]
    split_ifs <;> simp
  · have hleft : (∑ n ∈ Finset.Ico (weakEpoch ω i) (weakEpoch ω (i + 1)),
        (killedGapEvent m m n).indicator (fun _ => (1 : ℝ≥0∞)) ω) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      obtain ⟨hn, hn'⟩ := Finset.mem_Ico.mp hn
      apply Set.indicator_of_notMem
      intro hk
      exact hlt ((killedGapEvent_cycle_iff hω hn hn' m).mp hk).2
    rw [hleft]
    symm
    apply Finset.sum_eq_zero
    intro h' hh'
    apply Set.indicator_of_notMem
    intro heq
    change walk ω (weakEpoch ω i) = (h' : ℤ) at heq
    have h'm : h' < m := Finset.mem_range.mp hh'
    omega

/-- The killed occupation at zero splits into restarted occupations at epoch heights. -/
theorem killedOccupation_eq_cycle_rewards {ω : ℕ → ℕ} (hω : EpochsFinite ω) (m : ℕ) :
    (∑' n : ℕ, (killedGapEvent m m n).indicator (fun _ => (1 : ℝ≥0∞)) ω) =
    ∑' i : ℕ, ∑ h ∈ Finset.range m, {ξ | walk ξ (weakEpoch ξ i) = (h : ℤ)}.indicator
      (fun ξ => levelOccupation h (epochRestart i ξ)) ω := by
  rw [tsum_eq_sum_weakCycles hω]
  exact tsum_congr fun i => killed_cycle_reward hω i m

end BGW.StableTrees.DiscreteHeightApprox
