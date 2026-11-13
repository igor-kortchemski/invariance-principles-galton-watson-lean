/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Probability.RealWalk
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Maximal inequalities for real iid walks

This file defines finite-horizon exceedance probabilities and proves Ottaviani's maximal
inequality using first-exit events and fresh-start independence.

Reference: P. Billingsley, *Convergence of Probability Measures*, 2nd ed., 1999, Theorem 9.7
(Ottaviani's inequality).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BGW.Probability.RealWalk

/-- The finite-horizon exceedance event `{∃ k ≤ m, r < |S_k|}`. -/
def maxExceed (m : ℕ) (r : ℝ) : Set (ℕ → ℝ) :=
  {ω | ∃ k ≤ m, r < |partialSum ω k|}

theorem measurableSet_maxExceed (m : ℕ) (r : ℝ) : MeasurableSet (maxExceed m r) := by
  have heq : maxExceed m r =
      ⋃ k ∈ Finset.range (m + 1), {ω | r < |partialSum ω k|} := by
    ext ω
    simp [maxExceed]
  rw [heq]
  exact MeasurableSet.biUnion (Finset.countable_toSet _) fun k _ => by
    exact measurableSet_lt measurable_const (by
      simpa only [Real.norm_eq_abs] using (measurable_partialSum k).norm)

/-- `maxTail ν m r = P(max_{k ≤ m} |S_k| > r)`: the genuine maximum probability, not a
supremum of marginal probabilities. -/
noncomputable def maxTail (ν : ProbabilityMeasure ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  (iidLaw ν : Measure (ℕ → ℝ)).real (maxExceed m r)

theorem maxTail_nonneg (ν : ProbabilityMeasure ℝ) (m : ℕ) (r : ℝ) :
    0 ≤ maxTail ν m r := by
  exact measureReal_nonneg

theorem maxTail_le_one (ν : ProbabilityMeasure ℝ) (m : ℕ) (r : ℝ) :
    maxTail ν m r ≤ 1 := by
  exact measureReal_le_one

/-- Monotone in the length. -/
theorem maxTail_mono_length (ν : ProbabilityMeasure ℝ) {m m' : ℕ} (h : m ≤ m') (r : ℝ) :
    maxTail ν m r ≤ maxTail ν m' r := by
  refine measureReal_mono ?_ (measure_ne_top _ _)
  rintro ω ⟨k, hk, hkr⟩
  exact ⟨k, hk.trans h, hkr⟩

/-- Antitone in the threshold. -/
theorem maxTail_anti_threshold (ν : ProbabilityMeasure ℝ) (m : ℕ) {r r' : ℝ} (h : r ≤ r') :
    maxTail ν m r' ≤ maxTail ν m r := by
  refine measureReal_mono ?_ (measure_ne_top _ _)
  rintro ω ⟨k, hk, hkr⟩
  exact ⟨k, hk, h.trans_lt hkr⟩

/-- Block translation: the maximum of `|S_{a+k} - S_a|`, `k ≤ m`, has the same exceedance
probability as the walk started at `0` (fresh start at the deterministic index `a`). -/
theorem measureReal_exceed_block (ν : ProbabilityMeasure ℝ) (a m : ℕ) (r : ℝ) :
    (iidLaw ν : Measure (ℕ → ℝ)).real {ω | ∃ k ≤ m, r < |blockSum ω a k|} =
      maxTail ν m r := by
  change (iidLaw ν : Measure (ℕ → ℝ)).real (shift a ⁻¹' maxExceed m r) = maxTail ν m r
  rw [maxTail, ← map_measureReal_apply (measurable_shift a) (measurableSet_maxExceed m r),
    iidLaw_map_shift]


private def prefixPartialSum (k j : ℕ) (v : Fin k → ℝ) : ℝ :=
  ∑ i ∈ Finset.range j, if h : i < k then v ⟨i, h⟩ else 0

private def firstExceed (k : ℕ) (r : ℝ) : Set (ℕ → ℝ) :=
  {ω | r < |partialSum ω k| ∧ ∀ j < k, |partialSum ω j| ≤ r}

private def firstExceedPrefix (k : ℕ) (r : ℝ) : Set (Fin k → ℝ) :=
  {v | r < |prefixPartialSum k k v| ∧ ∀ j < k, |prefixPartialSum k j v| ≤ r}

private lemma measurable_prefixPartialSum (k j : ℕ) :
    Measurable (prefixPartialSum k j) := by
  unfold prefixPartialSum
  fun_prop

private lemma measurableSet_firstExceedPrefix (k : ℕ) (r : ℝ) :
    MeasurableSet (firstExceedPrefix k r) := by
  have habs (j : ℕ) : Measurable fun v : Fin k → ℝ => |prefixPartialSum k j v| := by
    simpa only [Real.norm_eq_abs] using (measurable_prefixPartialSum k j).norm
  have heq : firstExceedPrefix k r =
      {v | r < |prefixPartialSum k k v|} ∩
        ⋂ j ∈ Finset.range k, {v | |prefixPartialSum k j v| ≤ r} := by
    ext v
    simp [firstExceedPrefix]
  rw [heq]
  exact (measurableSet_lt measurable_const (habs k)).inter <|
    MeasurableSet.biInter (Finset.countable_toSet _) fun j _ => measurableSet_le (habs j)
      measurable_const

private lemma prefixPartialSum_prefixVec (ω : ℕ → ℝ) {j k : ℕ} (h : j ≤ k) :
    prefixPartialSum k j (prefixVec k ω) = partialSum ω j := by
  unfold prefixPartialSum partialSum
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i < k := (Finset.mem_range.mp hi).trans_le h
  simp [prefixVec, hik]

private lemma firstExceed_eq_preimage (k : ℕ) (r : ℝ) :
    firstExceed k r = prefixVec k ⁻¹' firstExceedPrefix k r := by
  ext ω
  constructor
  · rintro ⟨hk, h⟩
    refine ⟨?_, ?_⟩
    · rw [prefixPartialSum_prefixVec ω le_rfl]
      exact hk
    · intro j hj
      rw [prefixPartialSum_prefixVec ω hj.le]
      exact h j hj
  · rintro ⟨hk, h⟩
    refine ⟨?_, ?_⟩
    · rw [← prefixPartialSum_prefixVec ω (le_refl k)]
      exact hk
    · intro j hj
      rw [← prefixPartialSum_prefixVec ω hj.le]
      exact h j hj

private lemma maxExceed_eq_iUnion_firstExceed (m : ℕ) (r : ℝ) :
    maxExceed m r = ⋃ k ∈ Finset.range (m + 1), firstExceed k r := by
  ext ω
  constructor
  · intro h
    have hex : ∃ k, k ≤ m ∧ r < |partialSum ω k| := h
    let k := Nat.find hex
    have hk := Nat.find_spec hex
    apply Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le hk.1))
    refine ⟨hk.2, fun j hj => le_of_not_gt fun hjr => ?_⟩
    exact Nat.find_min hex hj ⟨hj.le.trans hk.1, hjr⟩
  · intro h
    rcases Set.mem_iUnion.mp h with ⟨k, h⟩
    rcases Set.mem_iUnion.mp h with ⟨hk, h⟩
    exact ⟨k, Nat.le_of_lt_succ (Finset.mem_range.mp hk), h.1⟩

private lemma pairwiseDisjoint_firstExceed (m : ℕ) (r : ℝ) :
    Set.PairwiseDisjoint (↑(Finset.range (m + 1))) (fun k => firstExceed k r) := by
  intro a _ b _ hab
  rw [Function.onFun, Set.disjoint_left]
  intro ω ha hb
  rcases lt_or_gt_of_ne hab with h | h
  · exact (not_lt_of_ge (hb.2 a h)) ha.1
  · exact (not_lt_of_ge (ha.2 b h)) hb.1

private lemma measurableSet_firstExceed (k : ℕ) (r : ℝ) :
    MeasurableSet (firstExceed k r) := by
  rw [firstExceed_eq_preimage]
  exact measurable_prefixVec k (measurableSet_firstExceedPrefix k r)

private lemma measurableSet_abs_partialSum_le (n : ℕ) (r : ℝ) :
    MeasurableSet {ω : ℕ → ℝ | |partialSum ω n| ≤ r} := by
  apply measurableSet_le _ measurable_const
  simpa only [Real.norm_eq_abs] using (measurable_partialSum n).norm

private lemma firstExceed_inter_blockSafe_eq (k n : ℕ) (r t : ℝ) :
    firstExceed k t ∩ {ω | |blockSum ω k n| ≤ r} =
      prefixVec k ⁻¹' firstExceedPrefix k t ∩
        shift k ⁻¹' {ω | |partialSum ω n| ≤ r} := by
  rw [firstExceed_eq_preimage]
  rfl

private lemma measureReal_firstExceed_inter_blockSafe (ν : ProbabilityMeasure ℝ)
    (k n : ℕ) (r t : ℝ) :
    (iidLaw ν : Measure (ℕ → ℝ)).real
        (firstExceed k t ∩ {ω | |blockSum ω k n| ≤ r}) =
      (iidLaw ν : Measure (ℕ → ℝ)).real (firstExceed k t) *
        (sumLaw ν n : Measure ℝ).real {x | |x| ≤ r} := by
  rw [firstExceed_inter_blockSafe_eq]
  have hreal :
      (iidLaw ν : Measure (ℕ → ℝ)).real
          (prefixVec k ⁻¹' firstExceedPrefix k t ∩
            shift k ⁻¹' {ω | |partialSum ω n| ≤ r}) =
        (iidLaw ν : Measure (ℕ → ℝ)).real
            (prefixVec k ⁻¹' firstExceedPrefix k t) *
          (iidLaw ν : Measure (ℕ → ℝ)).real {ω | |partialSum ω n| ≤ r} := by
    simp only [measureReal_def, measure_prefix_inter_shift ν k
      (measurableSet_firstExceedPrefix k t) (measurableSet_abs_partialSum_le n r),
      ENNReal.toReal_mul]
  rw [hreal, ← firstExceed_eq_preimage]
  congr 1
  have hC : MeasurableSet {x : ℝ | |x| ≤ r} := by
    apply measurableSet_le _ measurable_const
    have hnorm : Measurable (fun x : ℝ => ‖x‖) := measurable_id.norm
    have heq : (fun x : ℝ => ‖x‖) = (fun x : ℝ => |x|) := by
      funext x
      exact Real.norm_eq_abs x
    rwa [heq] at hnorm
  rw [coe_sumLaw, map_measureReal_apply (measurable_partialSum n) hC]
  rfl

private lemma firstExceed_inter_blockSafe_subset (m k : ℕ) (r : ℝ) (hk : k ≤ m) :
    firstExceed k (2 * r) ∩ {ω | |blockSum ω k (m - k)| ≤ r} ⊆
      firstExceed k (2 * r) ∩ {ω | r < |partialSum ω m|} := by
  rintro ω ⟨hfirst, hsafe⟩
  refine ⟨hfirst, ?_⟩
  have hsum : partialSum ω m = partialSum ω k + blockSum ω k (m - k) := by
    rw [← partialSum_add, Nat.add_sub_of_le hk]
  have htri : |partialSum ω k| ≤ |partialSum ω m| + |blockSum ω k (m - k)| := by
    rw [hsum]
    calc
      |partialSum ω k| = |partialSum ω k + blockSum ω k (m - k) -
          blockSum ω k (m - k)| := by congr 1; ring
      _ ≤ |partialSum ω k + blockSum ω k (m - k)| +
          |blockSum ω k (m - k)| := abs_sub _ _
  change r < |partialSum ω m|
  change |blockSum ω k (m - k)| ≤ r at hsafe
  linarith [hfirst.1]

private lemma measureReal_partialSum (ν : ProbabilityMeasure ℝ) (m : ℕ) (r : ℝ) :
    (iidLaw ν : Measure (ℕ → ℝ)).real {ω | r < |partialSum ω m|} =
      (sumLaw ν m : Measure ℝ).real {x | r < |x|} := by
  have hC : MeasurableSet {x : ℝ | r < |x|} := by
    apply measurableSet_lt measurable_const
    have hnorm : Measurable (fun x : ℝ => ‖x‖) := measurable_id.norm
    have heq : (fun x : ℝ => ‖x‖) = (fun x : ℝ => |x|) := by
      funext x
      exact Real.norm_eq_abs x
    rwa [heq] at hnorm
  rw [coe_sumLaw, map_measureReal_apply (measurable_partialSum m) hC]
  rfl


private lemma measureReal_firstExceed_le_two_inter (ν : ProbabilityMeasure ℝ)
    (m k : ℕ) (r : ℝ) (hk : k ≤ m)
    (hsafe : ∀ j ≤ m, (1 / 2 : ℝ) ≤ (sumLaw ν j : Measure ℝ).real {x | |x| ≤ r}) :
    (iidLaw ν : Measure (ℕ → ℝ)).real (firstExceed k (2 * r)) ≤
      2 * (iidLaw ν : Measure (ℕ → ℝ)).real
        (firstExceed k (2 * r) ∩ {ω | r < |partialSum ω m|}) := by
  have hfactor := measureReal_firstExceed_inter_blockSafe ν k (m - k) r (2 * r)
  have hs := hsafe (m - k) (Nat.sub_le m k)
  have hp : 0 ≤ (iidLaw ν : Measure (ℕ → ℝ)).real (firstExceed k (2 * r)) :=
    measureReal_nonneg
  have hmul : (iidLaw ν : Measure (ℕ → ℝ)).real (firstExceed k (2 * r)) * (1 / 2) ≤
      (iidLaw ν : Measure (ℕ → ℝ)).real
        (firstExceed k (2 * r) ∩ {ω | |blockSum ω k (m - k)| ≤ r}) := by
    rw [hfactor]
    exact mul_le_mul_of_nonneg_left hs hp
  have hsub : (iidLaw ν : Measure (ℕ → ℝ)).real
        (firstExceed k (2 * r) ∩ {ω | |blockSum ω k (m - k)| ≤ r}) ≤
      (iidLaw ν : Measure (ℕ → ℝ)).real
        (firstExceed k (2 * r) ∩ {ω | r < |partialSum ω m|}) :=
    measureReal_mono (firstExceed_inter_blockSafe_subset m k r hk) (measure_ne_top _ _)
  linarith

/-- Ottaviani's maximal inequality for real iid sums (Node 6). If every partial sum `S_j`,
`j ≤ m`, lies in `[-r, r]` with probability `≥ 1/2` (the "safe remainder" hypothesis, applied to
the independent remainder `S_m - S_k` of length `m - k ≤ m`), then
`P(max_{k ≤ m} |S_k| > 2 r) ≤ 2 P(|S_m| > r)`. -/
theorem maximal_le_two_mul_tail (ν : ProbabilityMeasure ℝ) (m : ℕ) (r : ℝ)
    (hsafe : ∀ j ≤ m, (1 / 2 : ℝ) ≤ (sumLaw ν j : Measure ℝ).real {x | |x| ≤ r}) :
    maxTail ν m (2 * r) ≤ 2 * (sumLaw ν m : Measure ℝ).real {x | r < |x|} := by
  have hT : MeasurableSet {ω : ℕ → ℝ | r < |partialSum ω m|} := by
    apply measurableSet_lt measurable_const
    simpa only [Real.norm_eq_abs] using (measurable_partialSum m).norm
  have hInter : ∀ k ∈ Finset.range (m + 1),
      MeasurableSet (firstExceed k (2 * r) ∩ {ω | r < |partialSum ω m|}) := by
    intro k _
    exact (measurableSet_firstExceed k (2 * r)).inter hT
  have hdisjInter : Set.PairwiseDisjoint (↑(Finset.range (m + 1)))
      (fun k => firstExceed k (2 * r) ∩ {ω | r < |partialSum ω m|}) := by
    intro a ha b hb hab
    exact (pairwiseDisjoint_firstExceed m (2 * r) ha hb hab).mono
      Set.inter_subset_left Set.inter_subset_left
  have hUnionSubset : (⋃ k ∈ Finset.range (m + 1),
      firstExceed k (2 * r) ∩ {ω | r < |partialSum ω m|}) ⊆
        {ω | r < |partialSum ω m|} := by
    intro ω h
    rcases Set.mem_iUnion.mp h with ⟨k, h⟩
    rcases Set.mem_iUnion.mp h with ⟨-, h⟩
    exact h.2
  rw [maxTail, maxExceed_eq_iUnion_firstExceed,
    measureReal_biUnion_finset (pairwiseDisjoint_firstExceed m (2 * r))
      (fun k _ => measurableSet_firstExceed k (2 * r))]
  calc
    (∑ k ∈ Finset.range (m + 1),
        (iidLaw ν : Measure (ℕ → ℝ)).real (firstExceed k (2 * r))) ≤
        ∑ k ∈ Finset.range (m + 1), 2 * (iidLaw ν : Measure (ℕ → ℝ)).real
          (firstExceed k (2 * r) ∩ {ω | r < |partialSum ω m|}) := by
      apply Finset.sum_le_sum
      intro k hk
      exact measureReal_firstExceed_le_two_inter ν m k r
        (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hsafe
    _ = 2 * ∑ k ∈ Finset.range (m + 1), (iidLaw ν : Measure (ℕ → ℝ)).real
          (firstExceed k (2 * r) ∩ {ω | r < |partialSum ω m|}) := by
      rw [Finset.mul_sum]
    _ = 2 * (iidLaw ν : Measure (ℕ → ℝ)).real (⋃ k ∈ Finset.range (m + 1),
          firstExceed k (2 * r) ∩ {ω | r < |partialSum ω m|}) := by
      rw [measureReal_biUnion_finset hdisjInter hInter]
    _ ≤ 2 * (iidLaw ν : Measure (ℕ → ℝ)).real {ω | r < |partialSum ω m|} := by
      exact mul_le_mul_of_nonneg_left
        (measureReal_mono hUnionSubset (measure_ne_top _ _)) (by norm_num)
    _ = 2 * (sumLaw ν m : Measure ℝ).real {x | r < |x|} := by
      rw [measureReal_partialSum]

end BGW.Probability.RealWalk
