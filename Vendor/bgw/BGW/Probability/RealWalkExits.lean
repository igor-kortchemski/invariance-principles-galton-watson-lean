/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.ExitPartition

/-!
# Measurability and fresh-start identities for real-walk exits

This file proves that restart exit times are measurable, determined by finite prefixes, and
strictly increasing before their absorbing sentinel.  It also expresses the next exit after a
deterministic time in terms of the shifted walk.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter

namespace BGW.Probability.RealWalk

private lemma nextExit_le' (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) (a : ℕ) :
    nextExit M r ω a ≤ M + 1 := by
  classical
  unfold nextExit
  split_ifs with h
  · exact (Nat.find_spec h).2.1.trans (Nat.le_succ M)
  · exact le_rfl

private lemma nextExit_spec' {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {a : ℕ}
    (h : nextExit M r ω a ≤ M) :
    a < nextExit M r ω a ∧
      r < |partialSum ω (nextExit M r ω a) - partialSum ω a| := by
  classical
  unfold nextExit at h ⊢
  split_ifs at h ⊢ with hex
  · exact ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2.2⟩
  · omega

private lemma lt_nextExit' {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {a : ℕ} (ha : a ≤ M) :
    a < nextExit M r ω a := by
  by_cases h : nextExit M r ω a ≤ M
  · exact (nextExit_spec' h).1
  · have heq := le_antisymm (nextExit_le' M r ω a) (Nat.succ_le_of_lt (lt_of_not_ge h))
    omega

private lemma nextExit_no_before' {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {a k : ℕ}
    (hak : a < k) (hkM : k ≤ M) (hk : k < nextExit M r ω a) :
    |partialSum ω k - partialSum ω a| ≤ r := by
  classical
  by_contra! hbad
  have hex : ∃ q, a < q ∧ q ≤ M ∧ r < |partialSum ω q - partialSum ω a| :=
    ⟨k, hak, hkM, hbad⟩
  have hfind : nextExit M r ω a = Nat.find hex := by simp [nextExit, hex]
  rw [hfind] at hk
  exact (Nat.not_le_of_lt hk) (Nat.find_le (⟨hak, hkM, hbad⟩ : _))

private lemma nextExit_eq_sentinel_iff {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {a : ℕ} :
    nextExit M r ω a = M + 1 ↔
      ∀ k, a < k → k ≤ M → |partialSum ω k - partialSum ω a| ≤ r := by
  classical
  constructor
  · intro h k hak hk
    exact nextExit_no_before' hak hk (by omega)
  · intro h
    apply le_antisymm (nextExit_le' M r ω a)
    by_contra! hlt
    have hspec := nextExit_spec' (Nat.le_of_lt_succ hlt)
    exact (not_lt_of_ge (h _ hspec.1 (Nat.le_of_lt_succ hlt))) hspec.2

private lemma nextExit_eq_iff {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {a k : ℕ} (hk : k ≤ M) :
    nextExit M r ω a = k ↔ a < k ∧ r < |partialSum ω k - partialSum ω a| ∧
      ∀ i, a < i → i < k → |partialSum ω i - partialSum ω a| ≤ r := by
  classical
  constructor
  · intro h
    have haM : a ≤ M := by
      by_contra! ha
      have hs : nextExit M r ω a = M + 1 := nextExit_eq_sentinel_iff.2 fun i hai hi => by
        omega
      omega
    have ha : a < k := h ▸ lt_nextExit' haM
    refine ⟨ha, h ▸ (nextExit_spec' (h.le.trans hk)).2, ?_⟩
    intro i hai hik
    exact nextExit_no_before' hai (hik.le.trans hk) (h ▸ hik)
  · rintro ⟨hak, hex, hmin⟩
    apply le_antisymm
    · by_contra! hlt
      exact (not_lt_of_ge (nextExit_no_before' hak hk hlt)) hex
    · by_contra! hlt
      have hle : nextExit M r ω a ≤ M := by
        have := nextExit_le' M r ω a
        omega
      have hspec := nextExit_spec' hle
      exact (not_lt_of_ge (hmin _ hspec.1 hlt)) hspec.2

private lemma measurableSet_abs_sub_partialSum_le (a k : ℕ) (r : ℝ) :
    MeasurableSet {ω : ℕ → ℝ | |partialSum ω k - partialSum ω a| ≤ r} := by
  apply measurableSet_le _ measurable_const
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using ((measurable_partialSum k).sub
    (measurable_partialSum a)).norm

private lemma measurableSet_abs_sub_partialSum_gt (a k : ℕ) (r : ℝ) :
    MeasurableSet {ω : ℕ → ℝ | r < |partialSum ω k - partialSum ω a|} := by
  apply measurableSet_lt measurable_const
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using ((measurable_partialSum k).sub
    (measurable_partialSum a)).norm

private lemma measurableSet_nextExit_eq (M : ℕ) (r : ℝ) (a k : ℕ) :
    MeasurableSet {ω : ℕ → ℝ | nextExit M r ω a = k} := by
  classical
  by_cases hk : k ≤ M
  · have heq : {ω : ℕ → ℝ | nextExit M r ω a = k} = {ω | a < k} ∩
        {ω | r < |partialSum ω k - partialSum ω a|} ∩
          ⋂ i ∈ Finset.range k, {ω | a < i →
            |partialSum ω i - partialSum ω a| ≤ r} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range]
      rw [nextExit_eq_iff hk]
      constructor
      · rintro ⟨ha, hex, h⟩
        exact ⟨⟨ha, hex⟩, fun i hai hik => h i hik hai⟩
      · rintro ⟨⟨ha, hex⟩, h⟩
        exact ⟨ha, hex, fun i hai hik => h i hik hai⟩
    rw [heq]
    have ha : MeasurableSet {ω : ℕ → ℝ | a < k} := by
      by_cases h : a < k <;> simp [h]
    refine (ha.inter (measurableSet_abs_sub_partialSum_gt a k r)).inter <|
      MeasurableSet.biInter (Finset.countable_toSet _) fun i _ => ?_
    by_cases hai : a < i
    · simpa [hai] using measurableSet_abs_sub_partialSum_le a i r
    · simp [hai]
  · by_cases hk' : k = M + 1
    · subst k
      have heq : {ω : ℕ → ℝ | nextExit M r ω a = M + 1} =
          ⋂ i ∈ Finset.range (M + 1), {ω | a < i →
            |partialSum ω i - partialSum ω a| ≤ r} := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
        rw [nextExit_eq_sentinel_iff]
        constructor
        · intro h i hai hi
          exact h i hi (Nat.le_of_lt_succ hai)
        · intro h i hai hi
          exact h i (Nat.lt_succ_of_le hi) hai
      rw [heq]
      refine MeasurableSet.biInter (Finset.countable_toSet _) fun i _ => ?_
      by_cases hai : a < i
      · simpa [hai] using measurableSet_abs_sub_partialSum_le a i r
      · simp [hai]
    · have heq : {ω : ℕ → ℝ | nextExit M r ω a = k} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        have := nextExit_le' M r ω a
        omega
      rw [heq]
      exact MeasurableSet.empty

/-- `nextExit M r · a` is measurable (the codomain `ℕ` carries the discrete σ-algebra). -/
theorem measurable_nextExit (M : ℕ) (r : ℝ) (a : ℕ) :
    Measurable fun ω : ℕ → ℝ => nextExit M r ω a := by
  refine measurable_to_countable' fun k => ?_
  exact measurableSet_nextExit_eq M r a k

private lemma measurable_nextExit_comp {τ : (ℕ → ℝ) → ℕ} (hτ : Measurable τ)
    (M : ℕ) (r : ℝ) : Measurable fun ω => nextExit M r ω (τ ω) := by
  refine measurable_to_countable' fun k => ?_
  change MeasurableSet {ω | nextExit M r ω (τ ω) = k}
  have heq : {ω | nextExit M r ω (τ ω) = k} =
      ⋃ a, {ω | τ ω = a} ∩ {ω | nextExit M r ω a = k} := by
    ext ω
    simp
  rw [heq]
  exact MeasurableSet.iUnion fun a =>
    (hτ (measurableSet_singleton a)).inter (measurableSet_nextExit_eq M r a k)

/-- Every restart exit time is measurable. -/
theorem measurable_exitTimes (M : ℕ) (r : ℝ) (j : ℕ) :
    Measurable fun ω : ℕ → ℝ => exitTimes M r ω j := by
  induction j with
  | zero => simp [exitTimes]
  | succ j ih =>
      simp only [exitTimes]
      exact Measurable.ite (measurableSet_le ih measurable_const)
        (measurable_nextExit_comp ih M r) measurable_const

private lemma exitCount_eq_sum (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) :
    exitCount M r ω = ∑ j ∈ Finset.range (M + 1),
      if 1 ≤ j ∧ exitTimes M r ω j ≤ M then 1 else 0 := by
  classical
  simp [exitCount]

/-- The finite count of actual exits is measurable. -/
theorem measurable_exitCount (M : ℕ) (r : ℝ) :
    Measurable fun ω : ℕ → ℝ => exitCount M r ω := by
  have heq : (fun ω : ℕ → ℝ => exitCount M r ω) = fun ω => ∑ j ∈ Finset.range (M + 1),
      if 1 ≤ j ∧ exitTimes M r ω j ≤ M then 1 else 0 := by
    funext ω
    exact exitCount_eq_sum M r ω
  rw [heq]
  apply Finset.measurable_sum
  intro j hj
  have hset : MeasurableSet {ω : ℕ → ℝ | 1 ≤ j ∧ exitTimes M r ω j ≤ M} := by
    by_cases h : 1 ≤ j
    · simpa [h] using measurableSet_le (measurable_exitTimes M r j) measurable_const
    · simp [h]
  exact Measurable.ite hset measurable_const measurable_const

/-- The existence of a close successive pair of actual exits is measurable. -/
theorem measurableSet_closeExit (M : ℕ) (r : ℝ) (l : ℕ) :
    MeasurableSet {ω : ℕ → ℝ | closeExit M r l ω} := by
  have heq : {ω : ℕ → ℝ | closeExit M r l ω} = ⋃ j : ℕ,
      {ω | 1 ≤ j ∧ exitTimes M r ω (j + 1) ≤ M ∧
        exitTimes M r ω (j + 1) - exitTimes M r ω j ≤ l} := by
    ext ω
    simp [closeExit]
  rw [heq]
  refine MeasurableSet.iUnion fun j => ?_
  by_cases hj : 1 ≤ j
  · simp only [hj, true_and]
    exact (measurableSet_le (measurable_exitTimes M r (j + 1)) measurable_const).inter
      (measurableSet_le ((measurable_exitTimes M r (j + 1)).sub
        (measurable_exitTimes M r j)) measurable_const)
  · simp [hj]

/-- Exit times are strictly increasing as long as they are actual exits (`≤ M`). -/
theorem exitTimes_lt_succ {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {j : ℕ}
    (h : exitTimes M r ω j ≤ M) : exitTimes M r ω j < exitTimes M r ω (j + 1) := by
  simp only [exitTimes, h, ↓reduceIte]
  exact lt_nextExit' h

/-- Once the sentinel `M + 1` (or anything `> M`) is reached, all later exit times are
sentinel. -/
theorem exitTimes_eq_sentinel {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {j : ℕ}
    (h : M < exitTimes M r ω j) {i : ℕ} (hi : 1 ≤ i) :
    exitTimes M r ω (j + i) = M + 1 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hi
  induction i with
  | zero => simp [exitTimes, not_le_of_gt h]
  | succ i ih =>
      rw [show j + (1 + (i + 1)) = (j + (1 + i)) + 1 by omega, exitTimes]
      simp [ih (by omega)]

/-- The number of actual exits is at most `M`. -/
theorem exitCount_le (M : ℕ) (r : ℝ) (ω : ℕ → ℝ) : exitCount M r ω ≤ M := by
  classical
  unfold exitCount
  calc
    _ ≤ (Finset.Icc 1 M).card := by
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hj
      simp [Finset.mem_Icc, hj.2.1, hj.1]
    _ = M := by simp

private lemma partialSum_eq_of_prefix_eq {ω ω' : ℕ → ℝ} {k j : ℕ}
    (hω : ∀ i < k, ω i = ω' i) (hj : j ≤ k) : partialSum ω j = partialSum ω' j := by
  unfold partialSum
  apply Finset.sum_congr rfl
  intro i hi
  exact hω i ((Finset.mem_range.mp hi).trans_le hj)

/-- The exit event `{nextExit a = k}`, `k ≤ M`, depends only on the coordinates `< k`. -/
theorem nextExit_eq_of_prefix_eq {M : ℕ} {r : ℝ} {ω ω' : ℕ → ℝ} {a k : ℕ}
    (hk : k ≤ M)
    (hω : ∀ i < k, ω i = ω' i) (h : nextExit M r ω a = k) :
    nextExit M r ω' a = k := by
  rw [nextExit_eq_iff hk] at h ⊢
  rcases h with ⟨hak, hex, hmin⟩
  refine ⟨hak, ?_, ?_⟩
  · rw [← partialSum_eq_of_prefix_eq hω (j := k) le_rfl,
      ← partialSum_eq_of_prefix_eq hω (j := a) hak.le]
    exact hex
  · intro i hai hik
    rw [← partialSum_eq_of_prefix_eq hω (j := i) hik.le,
      ← partialSum_eq_of_prefix_eq hω (j := a) hak.le]
    exact hmin i hai hik

private lemma exitTimes_eq_of_prefix_eq {M : ℕ} {r : ℝ} {ω ω' : ℕ → ℝ} {j k : ℕ}
    (hk : k ≤ M) (hω : ∀ i < k, ω i = ω' i) (h : exitTimes M r ω j = k) :
    exitTimes M r ω' j = k := by
  induction j generalizing k with
  | zero => simpa [exitTimes] using h
  | succ j ih =>
      have hprev : exitTimes M r ω j ≤ M := by
        by_contra! hn
        simp [exitTimes, not_le_of_gt hn] at h
        omega
      have hnext : nextExit M r ω (exitTimes M r ω j) = k := by
        simpa [exitTimes, hprev] using h
      have hlt : exitTimes M r ω j < k := (nextExit_eq_iff hk).1 hnext |>.1
      have hprev' : exitTimes M r ω' j = exitTimes M r ω j :=
        ih hprev (fun i hi => hω i (hi.trans hlt)) rfl
      simp only [exitTimes, hprev', hprev, ↓reduceIte]
      exact nextExit_eq_of_prefix_eq hk hω hnext

private def prefixExtend (k : ℕ) (v : Fin k → ℝ) : ℕ → ℝ := fun i =>
  if h : i < k then v ⟨i, h⟩ else 0

private lemma measurable_prefixExtend (k : ℕ) : Measurable (prefixExtend k) := by
  unfold prefixExtend
  fun_prop

private lemma prefixExtend_prefixVec (k : ℕ) (ω : ℕ → ℝ) (i : ℕ) (hi : i < k) :
    prefixExtend k (prefixVec k ω) i = ω i := by
  simp [prefixExtend, prefixVec, hi]

/-- Prefix-determination of the `j`-th exit time at an actual exit. -/
theorem exists_prefixSet_exitTimes (M : ℕ) (r : ℝ) (j k : ℕ) (hk : k ≤ M) :
    ∃ A : Set (Fin k → ℝ), MeasurableSet A ∧
      {ω : ℕ → ℝ | exitTimes M r ω j = k} = prefixVec k ⁻¹' A := by
  let A : Set (Fin k → ℝ) := {v | exitTimes M r (prefixExtend k v) j = k}
  refine ⟨A, (measurable_exitTimes M r j).comp (measurable_prefixExtend k)
    (measurableSet_singleton k), ?_⟩
  ext ω
  change exitTimes M r ω j = k ↔ exitTimes M r (prefixExtend k (prefixVec k ω)) j = k
  constructor
  · apply exitTimes_eq_of_prefix_eq hk
    intro i hi
    exact (prefixExtend_prefixVec k ω i hi).symm
  · apply exitTimes_eq_of_prefix_eq hk
    intro i hi
    exact prefixExtend_prefixVec k ω i hi

private lemma partialSum_shift_sub (ω : ℕ → ℝ) (a m : ℕ) :
    partialSum (shift a ω) m = partialSum ω (a + m) - partialSum ω a := by
  have h := partialSum_add ω a m
  rw [blockSum_eq_partialSum_shift] at h
  linarith

private lemma nextExit_add_shift {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {k : ℕ} (hk : k ≤ M) :
    nextExit M r ω k = k + nextExit (M - k) r (shift k ω) 0 := by
  by_cases h : nextExit (M - k) r (shift k ω) 0 ≤ M - k
  · let i := nextExit (M - k) r (shift k ω) 0
    have hi : i ≤ M - k := h
    have heq : nextExit (M - k) r (shift k ω) 0 = i := rfl
    have hs := (nextExit_eq_iff hi).1 heq
    apply (nextExit_eq_iff (show k + i ≤ M by omega)).2
    refine ⟨by omega, ?_, ?_⟩
    · rw [← partialSum_shift_sub]
      simpa [partialSum] using hs.2.1
    · intro q hkq hqi
      have hn : q - k < i := by omega
      have hp := hs.2.2 (q - k) (by omega) hn
      rw [show q = k + (q - k) by omega, ← partialSum_shift_sub]
      simpa [partialSum] using hp
  · have hi : nextExit (M - k) r (shift k ω) 0 = M - k + 1 :=
      le_antisymm (nextExit_le' _ _ _ _) (by omega)
    rw [hi, show k + (M - k + 1) = M + 1 by omega, nextExit_eq_sentinel_iff]
    intro q hkq hqM
    have hs := (nextExit_eq_sentinel_iff.1 hi) (q - k) (by omega) (by omega)
    rw [show q = k + (q - k) by omega, ← partialSum_shift_sub]
    simpa [partialSum] using hs

/-- The next exit after an actual `j`-th exit is computed by the shifted walk. -/
theorem exitTimes_succ_eq_shift {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {j k : ℕ} (hk : k ≤ M)
    (h : exitTimes M r ω j = k) :
    exitTimes M r ω (j + 1) = k + nextExit (M - k) r (shift k ω) 0 := by
  simp only [exitTimes, h, hk, ↓reduceIte]
  exact nextExit_add_shift hk

end BGW.Probability.RealWalk
