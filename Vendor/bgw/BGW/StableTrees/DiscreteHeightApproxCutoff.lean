/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxLadderScale
public import BGW.StableTrees.RealWalkTightness

/-!
# Weak-epoch cutoff removal

Before a bounded walk maximum, many weak epochs force their attained height to
remain bounded. The ladder transform controls this event exponentially.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest BGW.Probability.RealWalk

namespace BGW.StableTrees.DiscreteHeightApprox

/-- The finite offspring-walk maximum has the canonical real iid-walk tail. -/
theorem measure_walk_maximum (μ : PMF ℕ) (k : ℕ) (r : ℝ) :
    (offspringSeqLaw μ).toMeasure {ω | ∃ u ≤ k, r < |(walk ω u : ℝ)|} =
      ENNReal.ofReal (maxTail (realOffspringStepLaw μ) k r) := by
  have hm : Measurable (fun (ω : ℕ → ℕ) i => ((ω i : ℤ) - 1 : ℝ)) := by
    apply Measurable.of_eval
    intro i
    exact (measurable_of_countable (fun j : ℕ => ((j : ℤ) - 1 : ℝ))).comp
      (measurable_pi_apply i)
  have he := Measure.map_apply (μ := (offspringSeqLaw μ).toMeasure) hm (measurableSet_maxExceed k r)
  rw [map_offspringSeqLaw_realIncrements] at he
  rw [← ofReal_measureReal] at he
  change _ = ENNReal.ofReal ((iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)).real
    (maxExceed k r))
  rw [he]
  congr 1
  ext ω
  change (∃ u ≤ k, r < |(walk ω u : ℝ)|) ↔
    ∃ u ≤ k, r < |partialSum (fun i => ((ω i : ℤ) - 1 : ℝ)) u|
  have hw (u : ℕ) : (walk ω u : ℝ) =
      partialSum (fun i => ((ω i : ℤ) - 1 : ℝ)) u := by
    simp only [walk, partialSum, Int.cast_sum, Int.cast_sub, Int.cast_one]
  simp_rw [hw]

/-- Many epochs before time `k` force either a large walk maximum or a low attained height. -/
theorem ladderCount_large_subset {ω : ℕ → ℕ} (hω : EpochsFinite ω)
    (k : ℕ) {b q x K : ℝ} (hb : 0 < b) (hq : 0 < q)
    (hlarge : x < (b / q) * (weakLadderCount ω k : ℝ)) :
    (∃ u ≤ k, K * b < |(walk ω u : ℝ)|) ∨
      (weakEpochHeight ω ⌈x * q / b⌉₊ : ℝ) ≤ K * b := by
  by_cases hex : ∃ u ≤ k, K * b < |(walk ω u : ℝ)|
  · exact Or.inl hex
  right
  have hH : ⌈x * q / b⌉₊ ≤ weakLadderCount ω k := by
    apply Nat.ceil_le.mpr
    have he : (b / q) * (weakLadderCount ω k : ℝ) =
        (weakLadderCount ω k : ℝ) * b / q := by ring
    rw [he] at hlarge
    have hh := (lt_div_iff₀ hq).mp hlarge
    exact (div_le_iff₀ hb).mpr hh.le
  have hmono : Monotone (weakEpoch ω) :=
    (strictMono_nat_of_lt_succ (weakEpoch_lt_succ hω)).monotone
  have htime := (hmono hH).trans (weakEpoch_bracket hω k).1
  have hbound := le_of_not_gt (fun hlt => hex ⟨_, htime, hlt⟩)
  have he := weakEpochHeight_cast hω ⌈x * q / b⌉₊
  have heR : (weakEpochHeight ω ⌈x * q / b⌉₊ : ℝ) =
      (walk ω (weakEpoch ω ⌈x * q / b⌉₊) : ℝ) := by exact_mod_cast he
  rw [heR]
  exact (le_abs_self _).trans hbound

private theorem ladderCount_tail_bound {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (t : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ x : ℝ, 0 < x →
      limsup (fun n : ℕ => (offspringSeqLaw μ).toMeasure
        {ω | x < (B n / (n : ℝ)) *
          (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ)}) atTop ≤
        ENNReal.ofReal (η + Real.exp (K - x / 2)) := by
  obtain ⟨K, _, N, htail⟩ := h.isRealStableAttracted.horizon_max_tight
    (show (0 : ℝ) < (t : ℝ) + 1 by positivity) η hη
  refine ⟨K, fun x hx => ?_⟩
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop N,
    eventual_epochHeight_bound h hx K] with n hn hnN hheight
  have hB := h.pos n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsub : (offspringSeqLaw μ).toMeasure
      {ω | x < (B n / (n : ℝ)) *
        (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ)} ≤
      (offspringSeqLaw μ).toMeasure
        ({ω | ∃ u ≤ ⌊(n : ℝ) * (t : ℝ)⌋₊, K * B n < |(walk ω u : ℝ)|} ∪
          {ω | (weakEpochHeight ω ⌈x * (n : ℝ) / B n⌉₊ : ℝ) ≤ K * B n}) := by
    apply measure_mono_ae
    filter_upwards [ae_epochsFinite μ h.critical h.nondegenerate] with ω hω
    intro hh
    exact ladderCount_large_subset hω _ hB hnR hh
  refine hsub.trans ((measure_union_le _ _).trans ?_)
  have hmax : (offspringSeqLaw μ).toMeasure
      {ω | ∃ u ≤ ⌊(n : ℝ) * (t : ℝ)⌋₊, K * B n < |(walk ω u : ℝ)|} ≤
        ENNReal.ofReal η := by
    rw [measure_walk_maximum]
    apply ENNReal.ofReal_le_ofReal
    refine (maxTail_mono_length (realOffspringStepLaw μ)
      (Nat.floor_le_floor ?_) _).trans (htail n hnN)
    exact mul_le_mul_of_nonneg_left (by linarith) hnR.le
  calc
    _ ≤ ENNReal.ofReal η + ENNReal.ofReal (Real.exp (K - x / 2)) := add_le_add hmax hheight
    _ = _ := (ENNReal.ofReal_add hη.le (Real.exp_nonneg _)).symm

/-- The normalized weak ladder count is tight on every fixed finite horizon. -/
theorem weakLadderCount_tight_ascending {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (t : ℝ≥0) :
    Tendsto (fun x : ℝ => limsup (fun n : ℕ => (offspringSeqLaw μ).toMeasure
      {ω | x < (B n / (n : ℝ)) *
        (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ)}) atTop) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  by_cases he : ε = ∞
  · simp only [he, le_top, eventually_true]
  have hep := ENNReal.toReal_pos hε.ne' he
  let η := ε.toReal / 2
  have hη : 0 < η := div_pos hep (by norm_num)
  obtain ⟨K, hK⟩ := ladderCount_tail_bound h t hη
  have hbot : Tendsto (fun x : ℝ => K - x / 2) atTop atBot := by
    apply tendsto_atBot.mpr
    intro r
    filter_upwards [eventually_ge_atTop (2 * (K - r))] with x hx
    linarith
  have hexp := Real.tendsto_exp_atBot.comp hbot
  filter_upwards [eventually_gt_atTop 0, hexp.eventually (gt_mem_nhds hη)] with x hx hxe
  refine (hK x hx).trans ?_
  have hle : η + Real.exp (K - x / 2) ≤ ε.toReal := by dsimp [η] at *; linarith
  exact (ENNReal.ofReal_le_ofReal hle).trans_eq (ENNReal.ofReal_toReal he)

/-- **Cutoff removal**: the normalized ladder count `(B_n/n) H_{⌊nt⌋}` is tight (ladder-height
subordinator of index `θ-1` and sealed walk-supremum tightness: `{H_k ≥ N} = {τ_N ≤ k}`). -/
theorem weakLadderCount_tight {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (t : ℝ≥0) :
    Tendsto (fun x : ℝ =>
        limsup (fun n : ℕ => ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) :
          Measure (ℕ → ℕ))
          {ω | x < (B n / (n : ℝ)) * (forestHeight ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ)}) atTop)
      atTop (𝓝 0) := by
  have he (n : ℕ) (x : ℝ) : (offspringSeqLaw μ).toMeasure
      {ω | x < (B n / (n : ℝ)) * (forestHeight ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ)} =
      (offspringSeqLaw μ).toMeasure
        {ω | x < (B n / (n : ℝ)) * (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ)} := by
    let k := ⌊(n : ℝ) * (t : ℝ)⌋₊
    have hm : MeasurableSet {ω | x < (B n / (n : ℝ)) * (weakLadderCount ω k : ℝ)} :=
      measurableSet_lt measurable_const
      (measurable_const.mul ((measurable_of_countable (fun j : ℕ => (j : ℝ))).comp
        (measurable_weakLadderCount k)))
    have hmap := Measure.map_apply (μ := (offspringSeqLaw μ).toMeasure) (measurable_revSeq k) hm
    rw [map_revSeq_offspringSeqLaw] at hmap
    rw [hmap]
    congr 1
    ext ω
    simp only [k, Set.mem_preimage, Set.mem_ofPred_eq, forestHeight_eq_weakLadderCount]
  simp_rw [he]
  exact weakLadderCount_tight_ascending h t

end BGW.StableTrees.DiscreteHeightApprox
