/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Probability.SeparableRepresentationCoupling
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Finite cells and block thresholds

This file constructs the geometric thresholds and the finite families of cells used in Dudley's
shared-uniform construction. Weak convergence gives strictly increasing time thresholds after which
all cells in the corresponding finite family have the required one-sided mass bound.
See Dudley, "Distances of probability measures and random variables" (1968), and *Real
Analysis and Probability* (2002), Theorem 11.7.2.
-/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal unitInterval

namespace BGW.Probability

/-- The lower threshold on the common-branch probability at level `k`. -/
noncomputable def blockThreshold (k : ℕ) : I :=
  ⟨1 - (2⁻¹ : ℝ) ^ k, sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num)),
    by
      have hp : 0 ≤ (2⁻¹ : ℝ) ^ k := pow_nonneg (by norm_num) _
      change 1 - (2⁻¹ : ℝ) ^ k ≤ 1
      linarith⟩

/-- The same threshold as an extended nonnegative real. -/
noncomputable def blockFactor (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal (blockThreshold k : ℝ)

/-- The block factor is strictly below one. -/
private lemma blockFactor_lt_one (k : ℕ) : blockFactor k < 1 := by
  rw [blockFactor, ENNReal.ofReal_lt_one]
  change 1 - (2⁻¹ : ℝ) ^ k < 1
  have hp : 0 < (2⁻¹ : ℝ) ^ k := pow_pos (by norm_num) _
  linarith

/-- The volume above the level-`k` threshold is exactly `2 ^ (-k)`. -/
lemma volume_Ici_blockThreshold (k : ℕ) :
    volume (Ici (blockThreshold k)) = (2⁻¹ : ℝ≥0∞) ^ k := by
  rw [unitInterval.volume_Ici]
  rw [show (blockThreshold k : ℝ) = 1 - (2⁻¹ : ℝ) ^ k from rfl, sub_sub_cancel]
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num),
    ENNReal.ofReal_ofNat]

/-- A one-sided cell-mass bound implies the corresponding lower bound on the common-branch
probability. -/
theorem le_cellStayProbability_of_mul_le {S : Type*} [MeasurableSpace S]
    {μ ν : Measure S} [IsProbabilityMeasure ν] {A : ℕ → Set S} {i : ℕ} {t : I}
    (hi : ν (A i) ≠ 0) (h : ENNReal.ofReal (t : ℝ) * ν (A i) ≤ μ (A i)) :
    t ≤ cellStayProbability μ ν A i := by
  have hfin : min (μ (A i)) (ν (A i)) * (ν (A i))⁻¹ ≠ ∞ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      min (μ (A i)) (ν (A i)) * (ν (A i))⁻¹ ≤ ν (A i) * (ν (A i))⁻¹ := by
        gcongr
        exact min_le_right _ _
      _ = 1 := ENNReal.mul_inv_cancel hi (measure_ne_top _ _)
  have ht : ENNReal.ofReal (t : ℝ) ≤ min (μ (A i)) (ν (A i)) * (ν (A i))⁻¹ := by
    calc
      ENNReal.ofReal (t : ℝ) =
          (ENNReal.ofReal (t : ℝ) * ν (A i)) * (ν (A i))⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hi (measure_ne_top _ _), mul_one]
      _ ≤ min (μ (A i)) (ν (A i)) * (ν (A i))⁻¹ := by
        gcongr
        refine le_min h ?_
        calc
          ENNReal.ofReal (t : ℝ) * ν (A i) ≤ 1 * ν (A i) := by
            gcongr
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal t.2.2
          _ = ν (A i) := one_mul _
  change (t : ℝ) ≤ (min (μ (A i)) (ν (A i)) * (ν (A i))⁻¹).toReal
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp ht

/-- Finite initial segments of a countable probability partition eventually carry at least
`1 - 2 ^ (-k)` of the mass. -/
theorem exists_finite_cell_union {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] {A : ℕ → Set S}
    (hmeas : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcover : ⋃ i, A i = univ) (k : ℕ) :
    ∃ M : ℕ, 1 - (2⁻¹ : ℝ≥0∞) ^ k ≤ ν (⋃ i ∈ Finset.range M, A i) := by
  have hsum : ∑' i, ν (A i) = 1 := by
    rw [← measure_iUnion hdisj hmeas, hcover, measure_univ]
  have hs : HasSum (fun i => ν (A i)) 1 := by
    simpa only [hsum] using (ENNReal.summable (f := fun i => ν (A i))).hasSum
  have hp : 0 < (2⁻¹ : ℝ≥0∞) ^ k :=
    bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num))
  have hlt : 1 - (2⁻¹ : ℝ≥0∞) ^ k < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top (by norm_num) hp.ne'
  have hev := hs.tendsto_sum_nat.eventually (Ioi_mem_nhds hlt)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  refine ⟨M, ?_⟩
  have hd : (↑(Finset.range M) : Set ℕ).PairwiseDisjoint A := fun _ _ _ _ hij => hdisj hij
  rw [measure_biUnion_finset hd (fun i _ => hmeas i)]
  exact (hM M le_rfl).le

/-- Weak convergence provides strictly increasing block thresholds with one-sided mass bounds on
all cells in prescribed finite families. -/
theorem exists_strictMono_block_thresholds {S : Type*} [PseudoMetricSpace S]
    [MeasurableSpace S] [BorelSpace S] {P : ℕ → ProbabilityMeasure S} {Q : ProbabilityMeasure S}
    (h : Tendsto P atTop (𝓝 Q)) {A : ℕ → ℕ → Set S}
    (hnull : ∀ k i, (Q : Measure S) (frontier (A k i)) = 0) (M : ℕ → ℕ) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ (∀ k, k ≤ N k) ∧ ∀ k n, N k ≤ n →
      ∀ i ∈ Finset.range (M k), blockFactor k * (Q : Measure S) (A k i) ≤
        (P n : Measure S) (A k i) := by
  have hk (k : ℕ) : ∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ Finset.range (M k),
      blockFactor k * (Q : Measure S) (A k i) ≤ (P n : Measure S) (A k i) := by
    have hi (i : ℕ) : ∃ N : ℕ, ∀ n ≥ N,
        blockFactor k * (Q : Measure S) (A k i) ≤ (P n : Measure S) (A k i) := by
      by_cases hi : (Q : Measure S) (A k i) = 0
      · exact ⟨0, fun _ _ => by simp [hi]⟩
      · have hcell := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h
          (hnull k i)
        have hlt : blockFactor k * (Q : Measure S) (A k i) <
            (Q : Measure S) (A k i) := by
          have hm := ENNReal.mul_lt_mul_left hi (measure_ne_top _ _) (blockFactor_lt_one k)
          simpa only [one_mul] using hm
        obtain ⟨N, hN⟩ := eventually_atTop.mp (hcell.eventually (Ioi_mem_nhds hlt))
        exact ⟨N, fun n hn => (hN n hn).le⟩
    choose Ni hNi using hi
    refine ⟨∑ i ∈ Finset.range (M k), Ni i, fun n hn i hi => hNi i n ?_⟩
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le (Ni j)) hi).trans hn
  choose raw hraw using hk
  let N : ℕ → ℕ := Nat.rec (raw 0) (fun k r => max (r + 1) (raw (k + 1)))
  have hN0 : N 0 = raw 0 := rfl
  have hNsucc (k : ℕ) : N (k + 1) = max (N k + 1) (raw (k + 1)) := rfl
  have hrawN (k : ℕ) : raw k ≤ N k := by
    cases k with
    | zero => exact le_of_eq hN0.symm
    | succ k => rw [hNsucc]; exact le_max_right _ _
  have hkN (k : ℕ) : k ≤ N k := by
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => rw [hNsucc]; omega
  have hNmono : StrictMono N := strictMono_nat_of_lt_succ fun k => by
    rw [hNsucc]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  refine ⟨N, hNmono, hkN, fun k n hn => hraw k n ((hrawN k).trans hn)⟩

end BGW.Probability
