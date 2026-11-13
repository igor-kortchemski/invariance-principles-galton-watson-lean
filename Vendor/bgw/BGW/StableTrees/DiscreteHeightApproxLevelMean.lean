/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxRecurrence

/-!
# Exact occupation mean in a weak ascending cycle

The nonnegative occupation series obtained by reversal agrees almost surely with
the finite first-cycle count. Its integral is one at every integer gap, including
zero. No second moment assumption is used for this normalization.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

/-- Before the first weak return, all positive-time walk values are strictly negative. -/
private theorem negativePrefix_iff_lt_epoch {ω : ℕ → ℕ} (hω : EpochsFinite ω) (n : ℕ) :
    NegativePrefix ω n ↔ n < weakEpoch ω 1 := by
  have hret : 0 < weakEpoch ω 1 ∧ 0 ≤ walk ω (weakEpoch ω 1) := by
    have he : 0 < nextEpoch ω 0 ∧ walk ω 0 ≤ walk ω (nextEpoch ω 0) :=
      Nat.sInf_mem (hω 0)
    rw [weakEpoch_succ, weakEpoch_zero]
    simpa only [walk, Finset.range_zero, Finset.sum_empty] using he
  constructor
  · intro hn
    by_contra hle
    have hneg := hn (weakEpoch ω 1) hret.1 (by omega)
    omega
  · intro hn u hu hun
    have hnret : ¬ (0 ≤ walk ω u) := by
      intro hw
      have hmin : nextEpoch ω 0 ≤ u := Nat.sInf_le ⟨hu, by simpa [walk] using hw⟩
      have hepoch : weakEpoch ω 1 = nextEpoch ω 0 := by rw [weakEpoch_succ]; rfl
      omega
    omega

/-- Pre-return occupation is exactly the finite first-cycle reflected-gap event. -/
private theorem negativeLevelEvent_iff {ω : ℕ → ℕ} (hω : EpochsFinite ω) (y n : ℕ) :
    ω ∈ negativeLevelEvent y n ↔ n < weakEpoch ω 1 ∧ reflGap ω n = (y : ℤ) := by
  have he (hn : n < weakEpoch ω 1) : reflGap ω n = -walk ω n := by
    simpa [walk] using reflGap_in_cycle hω (i := 0) (u := n) (by simp) hn
  constructor
  · rintro ⟨hw, hn⟩
    have hlt := (negativePrefix_iff_lt_epoch hω n).mp hn
    exact ⟨hlt, by rw [he hlt, hw]; omega⟩
  · rintro ⟨hn, hy⟩
    refine ⟨?_, (negativePrefix_iff_lt_epoch hω n).mpr hn⟩
    rw [he hn] at hy
    omega

/-- Nonnegative pre-return occupation series at one integer gap. -/
noncomputable def levelOccupation (y : ℕ) (ω : ℕ → ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, (negativeLevelEvent y n).indicator (fun _ => (1 : ℝ≥0∞)) ω

/-- The pre-return occupation series is measurable. -/
theorem measurable_levelOccupation (y : ℕ) : Measurable (levelOccupation y) :=
  Measurable.tsum fun n => measurable_const.indicator
    (measurableSet_negativeLevelEvent y n)

/-- The pre-return occupation series has nonnegative integral one. -/
theorem lintegral_levelOccupation (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (y : ℕ) : ∫⁻ ω, levelOccupation y ω ∂(offspringSeqLaw μ).toMeasure = 1 := by
  change (∫⁻ ω, ∑' n : ℕ, (negativeLevelEvent y n).indicator
    (fun _ => (1 : ℝ≥0∞)) ω ∂(offspringSeqLaw μ).toMeasure) = 1
  rw [lintegral_tsum (fun n => (measurable_const.indicator
    (measurableSet_negativeLevelEvent y n)).aemeasurable)]
  simp_rw [lintegral_indicator (measurableSet_negativeLevelEvent y _), lintegral_const,
    one_mul, Measure.restrict_apply_univ]
  exact tsum_negativeLevelEvent_mass μ hc hne y

/-- On finite paths, the occupation series is the finite first-cycle level count. -/
theorem levelOccupation_eq_card {ω : ℕ → ℕ} (hω : EpochsFinite ω) (y : ℕ) :
    levelOccupation y ω =
      (((Finset.Ico 0 (weakEpoch ω 1)).filter (fun u => reflGap ω u = (y : ℤ))).card : ℝ≥0∞) := by
  unfold levelOccupation
  rw [tsum_eq_sum (s := Finset.range (weakEpoch ω 1))]
  · simp only [Nat.Ico_zero_eq_range, Finset.card_eq_sum_ones, Nat.cast_sum,
      Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    have hlt := Finset.mem_range.mp hn
    have he := negativeLevelEvent_iff hω y n
    simp only [Set.indicator_apply, he, hlt, true_and]
    split_ifs <;> simp
  · intro n hn
    apply Set.indicator_of_notMem
    intro he
    have hlt := (negativeLevelEvent_iff hω y n).mp he |>.1
    exact hn (Finset.mem_range.mpr hlt)

/-- **Key normalization supplier (exact mean).**  In the first cycle `[0, τ_1)` the expected
number of times at gap exactly `y` equals `1` for every `y ∈ ℕ` (duality with the strict
descending ladder process, whose heights are `1` by downward skip-freeness). -/
theorem clusterLevelMean (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (y : ℕ) :
    ∫ ω, (((Finset.Ico 0 (weakEpoch ω 1)).filter (fun u => reflGap ω u = (y : ℤ))).card : ℝ)
      ∂((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)) = 1 := by
  have hm := measurable_levelOccupation y
  have hlin := lintegral_levelOccupation μ hc hne y
  have hfin := ae_lt_top hm (show ∫⁻ ω, levelOccupation y ω
      ∂(offspringSeqLaw μ).toMeasure ≠ ∞ by rw [hlin]; exact ENNReal.one_ne_top)
  have he : (fun ω =>
      (((Finset.Ico 0 (weakEpoch ω 1)).filter (fun u => reflGap ω u = (y : ℤ))).card : ℝ))
      =ᵐ[(offspringSeqLaw μ).toMeasure] (fun ω => (levelOccupation y ω).toReal) := by
    filter_upwards [ae_epochsFinite μ hc hne] with ω hω
    rw [levelOccupation_eq_card hω]
    simp
  rw [integral_congr_ae he, integral_toReal hm.aemeasurable hfin, hlin, ENNReal.toReal_one]

end BGW.StableTrees.DiscreteHeightApprox
