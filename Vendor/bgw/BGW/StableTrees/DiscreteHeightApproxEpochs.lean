/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxReversal

/-!
# Weak ascending epochs

Deterministic epoch characterizations assume `EpochsFinite`, which eliminates
the empty-set value of `sInf`. Weak epochs retain ties at the running maximum.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

/-- The next weak ascending epoch after the epoch `s` (junk `0` if none). -/
noncomputable def nextEpoch (ω : ℕ → ℕ) (s : ℕ) : ℕ :=
  sInf {u | s < u ∧ walk ω s ≤ walk ω u}

/-- The weak epochs `τ_0 = 0 < τ_1 < ...`: iterates of `nextEpoch` from `0`. -/
noncomputable def weakEpoch (ω : ℕ → ℕ) (i : ℕ) : ℕ := (nextEpoch ω)^[i] 0

/-- All epochs exist (the walk returns to each running-maximum level or above). -/
def EpochsFinite (ω : ℕ → ℕ) : Prop :=
  ∀ i : ℕ, ∃ u, weakEpoch ω i < u ∧ walk ω (weakEpoch ω i) ≤ walk ω u

/-- The number of times `u` in the cycle `[τ_i, τ_{i+1})` with gap `< a` below the epoch value:
the cycle visit count `V_i(a)`. -/
noncomputable def clusterVisits (ω : ℕ → ℕ) (a : ℝ) (i : ℕ) : ℕ :=
  ((Finset.Ico (weakEpoch ω i) (weakEpoch ω (i + 1))).filter
    (fun u => (((walk ω (weakEpoch ω i) - walk ω u : ℤ)) : ℝ) < a)).card

/-- The zeroth weak epoch is time zero. -/
@[simp] theorem weakEpoch_zero (ω : ℕ → ℕ) : weakEpoch ω 0 = 0 := rfl

/-- Consecutive epochs are related by the next-epoch map. -/
theorem weakEpoch_succ (ω : ℕ → ℕ) (i : ℕ) :
    weakEpoch ω (i + 1) = nextEpoch ω (weakEpoch ω i) := by
  exact Function.iterate_succ_apply' (nextEpoch ω) i 0

private theorem nextEpoch_spec {ω : ℕ → ℕ} (hω : EpochsFinite ω) (i : ℕ) :
    weakEpoch ω i < nextEpoch ω (weakEpoch ω i) ∧
      walk ω (weakEpoch ω i) ≤ walk ω (nextEpoch ω (weakEpoch ω i)) :=
  Nat.sInf_mem (hω i)

/-- The epochs are strictly increasing when finite. -/
theorem weakEpoch_lt_succ {ω : ℕ → ℕ} (hω : EpochsFinite ω) (i : ℕ) :
    weakEpoch ω i < weakEpoch ω (i + 1) := by
  rw [weakEpoch_succ]
  exact (nextEpoch_spec hω i).1

/-- Finiteness makes the epoch sequence strictly increasing. -/
theorem strictMono_weakEpoch {ω : ℕ → ℕ} (hω : EpochsFinite ω) :
    StrictMono (weakEpoch ω) :=
  strictMono_nat_of_lt_succ (weakEpoch_lt_succ hω)

private theorem walk_lt_in_cycle {ω : ℕ → ℕ} {i u : ℕ}
    (hiu : weakEpoch ω i < u) (hui : u < weakEpoch ω (i + 1)) :
    walk ω u < walk ω (weakEpoch ω i) := by
  by_contra hn
  have hle : nextEpoch ω (weakEpoch ω i) ≤ u := Nat.sInf_le ⟨hiu, by omega⟩
  rw [← weakEpoch_succ] at hle
  omega

/-- Every weak epoch attains the running maximum, including time zero. -/
theorem reflGap_weakEpoch {ω : ℕ → ℕ} (hω : EpochsFinite ω) (i : ℕ) :
    reflGap ω (weakEpoch ω i) = 0 := by
  rw [reflGap_zero_iff_record]
  induction i with
  | zero => simp only [weakEpoch_zero, Nat.le_zero]; intro v hv; simp [hv]
  | succ i ih =>
    intro v hv
    have hs := nextEpoch_spec hω i
    rw [← weakEpoch_succ] at hs
    by_cases hvi : v ≤ weakEpoch ω i
    · exact (ih v hvi).trans hs.2
    · by_cases he : v = weakEpoch ω (i + 1)
      · exact he ▸ le_rfl
      · exact (walk_lt_in_cycle (by omega) (by omega)).le.trans hs.2

/-- Every integer time belongs to some finite weak-epoch cycle. -/
theorem exists_weakEpoch_le_lt {ω : ℕ → ℕ} (hω : EpochsFinite ω) (k : ℕ) :
    ∃ i, weakEpoch ω i ≤ k ∧ k < weakEpoch ω (i + 1) := by
  have hs := strictMono_weakEpoch hω
  have hbound : k + 1 ≤ weakEpoch ω (k + 1) := hs.id_le (k + 1)
  have hex : ∃ i, k < weakEpoch ω i := ⟨k + 1, by omega⟩
  let i := Nat.find hex
  have hi : k < weakEpoch ω i := Nat.find_spec hex
  have hip : 0 < i := by
    by_contra hn
    have he : i = 0 := by omega
    rw [he, weakEpoch_zero] at hi
    omega
  refine ⟨i - 1, ?_, ?_⟩
  · have hn := Nat.find_min hex (show i - 1 < i by omega)
    omega
  · simpa only [Nat.sub_add_cancel hip] using hi

/-- At an epoch the running maximum is attained: `reflGap ω (τ_i) = 0` and the epochs are exactly
the zeros of `reflGap` (ties are weak records). -/
theorem reflGap_eq_zero_iff {ω : ℕ → ℕ} (hω : EpochsFinite ω) {u : ℕ} :
    (reflGap ω u = 0 ∧ 0 < u) ↔ ∃ i, 0 < i ∧ weakEpoch ω i = u := by
  constructor
  · rintro ⟨hr, hu⟩
    obtain ⟨i, hi, hi'⟩ := exists_weakEpoch_le_lt hω u
    have he : weakEpoch ω i = u := by
      by_contra hn
      have hlt := walk_lt_in_cycle (by omega : weakEpoch ω i < u) hi'
      have hle := (reflGap_zero_iff_record ω u).mp hr (weakEpoch ω i) hi
      omega
    refine ⟨i, ?_, he⟩
    by_contra hn
    have hiz : i = 0 := by omega
    rw [hiz, weakEpoch_zero] at he
    omega
  · rintro ⟨i, hi, rfl⟩
    exact ⟨reflGap_weakEpoch hω i, by
      have := (strictMono_weakEpoch hω) hi
      simpa only [weakEpoch_zero] using this⟩

private theorem weakLadderCount_eq_index {ω : ℕ → ℕ} (hω : EpochsFinite ω)
    {i k : ℕ} (hi : weakEpoch ω i ≤ k) (hi' : k < weakEpoch ω (i + 1)) :
    weakLadderCount ω k = i := by
  have hs := strictMono_weakEpoch hω
  have he : ((Finset.Icc 1 k).filter (fun u => reflGap ω u = 0)) =
      (Finset.Icc 1 i).image (weakEpoch ω) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hu1, huk⟩, hr⟩
      obtain ⟨j, hj, he⟩ := reflGap_eq_zero_iff hω |>.mp ⟨hr, hu1⟩
      refine ⟨j, ⟨hj, ?_⟩, he⟩
      by_contra hn
      have hle := hs.monotone (show i + 1 ≤ j by omega)
      omega
    · rintro ⟨j, ⟨hj, hji⟩, rfl⟩
      have hj' := hs hj
      simp only [weakEpoch_zero] at hj'
      exact ⟨⟨hj', (hs.monotone hji).trans hi⟩, reflGap_weakEpoch hω j⟩
  rw [weakLadderCount, he, Finset.card_image_of_injective _ hs.injective]
  simp

/-- The number of epochs `u ∈ [1,k]` is the last cycle index: `τ_H ≤ k < τ_{H+1}`. -/
theorem weakEpoch_bracket {ω : ℕ → ℕ} (hω : EpochsFinite ω) (k : ℕ) :
    weakEpoch ω (weakLadderCount ω k) ≤ k ∧ k < weakEpoch ω (weakLadderCount ω k + 1) := by
  obtain ⟨i, hi, hi'⟩ := exists_weakEpoch_le_lt hω k
  rw [weakLadderCount_eq_index hω hi hi']
  exact ⟨hi, hi'⟩

/-- Inside a cycle the running maximum remains equal to the initial epoch value. -/
theorem reflGap_in_cycle {ω : ℕ → ℕ} (hω : EpochsFinite ω) {i u : ℕ}
    (hi : weakEpoch ω i ≤ u) (hi' : u < weakEpoch ω (i + 1)) :
    reflGap ω u = walk ω (weakEpoch ω i) - walk ω u := by
  unfold reflGap
  congr 1
  apply le_antisymm
  · apply Finset.sup'_le
    intro v hv
    have hv' : v ≤ u := Nat.le_of_lt_succ (Finset.mem_range.mp hv)
    by_cases hvi : v ≤ weakEpoch ω i
    · exact (reflGap_zero_iff_record ω _).mp (reflGap_weakEpoch hω i) v hvi
    · exact (walk_lt_in_cycle (by omega) (by omega : v < weakEpoch ω (i + 1))).le
  · exact Finset.le_sup' _ (Finset.mem_range.mpr (by omega))

private noncomputable def bandPrefix (ω : ℕ → ℕ) (a : ℝ) (k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun u => (reflGap ω u : ℝ) < a)).card

private theorem bandPrefix_mono (ω : ℕ → ℕ) (a : ℝ) : Monotone (bandPrefix ω a) := by
  intro k l hkl
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hkl))

private theorem sum_clusterVisits {ω : ℕ → ℕ} (hω : EpochsFinite ω) (a : ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range N, clusterVisits ω a i = bandPrefix ω a (weakEpoch ω N) := by
  have hcluster (i : ℕ) : clusterVisits ω a i =
      ((Finset.Ico (weakEpoch ω i) (weakEpoch ω (i + 1))).filter
        (fun u => (reflGap ω u : ℝ) < a)).card := by
    unfold clusterVisits
    congr 1
    apply Finset.filter_congr
    intro u hu
    obtain ⟨hu, hu'⟩ := Finset.mem_Ico.mp hu
    rw [reflGap_in_cycle hω hu hu']
  induction N with
  | zero => simp [bandPrefix]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, hcluster]
    unfold bandPrefix
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      rw [← Finset.filter_union]
      congr 1
      ext u
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      have hs := weakEpoch_lt_succ hω N
      omega
    · apply Finset.disjoint_left.mpr
      intro u hu hv
      have hu' := Finset.mem_range.mp (Finset.mem_filter.mp hu).1
      have hv' := (Finset.mem_Ico.mp (Finset.mem_filter.mp hv).1).1
      omega

private theorem bandPrefix_succ (ω : ℕ → ℕ) (k : ℕ) {a : ℝ} (ha : 0 < a) :
    bandPrefix ω a (k + 1) = bandCount ω k a + 1 := by
  have he : Finset.range (k + 1) = insert 0 (Finset.Icc 1 k) := by
    ext u
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hz : reflGap ω 0 = 0 := by simp [reflGap, walk]
  simp [bandPrefix, bandCount, he, hz, ha, Finset.filter_insert, Nat.add_comm]

/-- (Deterministic stopped decomposition) With `H = weakLadderCount ω k` and `a > 0`:
`Σ_{i<H} V_i(a) - 1 ≤ bandCount ω k a ≤ Σ_{i ≤ H} V_i(a)`. -/
theorem bandCount_sandwich {ω : ℕ → ℕ} (hω : EpochsFinite ω) (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ((∑ i ∈ Finset.range (weakLadderCount ω k), clusterVisits ω a i : ℕ) : ℤ) - 1 ≤
        bandCount ω k a ∧
      bandCount ω k a ≤ ∑ i ∈ Finset.range (weakLadderCount ω k + 1), clusterVisits ω a i := by
  rw [sum_clusterVisits hω, sum_clusterVisits hω]
  obtain ⟨hlo, hhi⟩ := weakEpoch_bracket hω k
  have hle := bandPrefix_mono ω a (show weakEpoch ω (weakLadderCount ω k) ≤ k + 1 by omega)
  have hge := bandPrefix_mono ω a (show k + 1 ≤ weakEpoch ω (weakLadderCount ω k + 1) by omega)
  rw [bandPrefix_succ ω k ha] at hle hge
  constructor
  · omega
  · omega

end BGW.StableTrees.DiscreteHeightApprox
