/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxLadderLaw

/-!
# Transform of attained weak ladder heights

Stopped restart gives the product formula for transforms of epoch heights. This
retains zero height increments and does not require finite increment variance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

/-- Successive attained heights add the first height of the restarted sequence. -/
theorem weakEpochHeight_succ {ω : ℕ → ℕ} (hω : EpochsFinite ω) (i : ℕ) :
    weakEpochHeight ω (i + 1) = weakEpochHeight ω i + weakEpochHeight (epochRestart i ω) 1 := by
  have hs := epochsFinite_shiftSeq hω (weakEpoch ω i)
  have he := weakEpochHeight_cast hs 1
  rw [weakEpoch_shift_duration hω i, walk_shiftSeq,
    Nat.add_sub_of_le (weakEpoch_lt_succ hω i).le] at he
  have hprev := weakEpochHeight_cast hω i
  have hnext := weakEpochHeight_cast hω (i + 1)
  change weakEpochHeight ω (i + 1) =
    weakEpochHeight ω i + weakEpochHeight (shiftSeq (weakEpoch ω i) ω) 1
  omega

/-- The nonnegative generating transform of the first weak ascending ladder height. -/
noncomputable def weakLadderPGF (μ : PMF ℕ) (s : ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, s ^ weakEpochHeight ω 1 ∂(offspringSeqLaw μ).toMeasure

private theorem measurable_epoch_power (s : ℝ≥0∞) (i : ℕ) :
    Measurable (fun ω => s ^ weakEpochHeight ω i) :=
  (measurable_of_countable (fun h : ℕ => s ^ h)).comp (measurable_weakEpochHeight i)

/-- A nonnegative observable of one attained epoch height integrates against its discrete law. -/
theorem lintegral_epochHeight (μ : PMF ℕ) (i : ℕ) (f : ℕ → ℝ≥0∞) :
    (∫⁻ ω, f (weakEpochHeight ω i) ∂(offspringSeqLaw μ).toMeasure) =
      ∑' h : ℕ, f h * (offspringSeqLaw μ).toMeasure {ω | weakEpochHeight ω i = h} := by
  rw [← lintegral_map (measurable_of_countable f) (measurable_weakEpochHeight i),
    lintegral_countable']
  apply tsum_congr
  intro h
  rw [Measure.map_apply (measurable_weakEpochHeight i) (measurableSet_singleton h)]
  rfl

/-- The first ladder-height PGF has offspring tails as its coefficients. -/
theorem weakLadderPGF_eq_tsum (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (s : ℝ≥0∞) :
    weakLadderPGF μ s = ∑' h : ℕ, s ^ h * μ.toMeasure (Set.Ici (h + 1)) := by
  rw [weakLadderPGF, lintegral_epochHeight]
  simp_rw [weakEpochHeight_one_law μ hc hne]

/-- The transform of the `i`th attained height is the `i`th power of the first-height transform. -/
theorem lintegral_epochHeight_pow (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (s : ℝ≥0∞) (i : ℕ) :
    (∫⁻ ω, s ^ weakEpochHeight ω i ∂(offspringSeqLaw μ).toMeasure) = (weakLadderPGF μ s) ^ i := by
  induction i with
  | zero => simp [weakEpochHeight, walk]
  | succ i ih =>
    let F (h : ℕ) (ω : ℕ → ℕ) : ℝ≥0∞ := {ξ | weakEpochHeight ξ i = h}.indicator
      (fun ξ => s ^ h * s ^ weakEpochHeight (epochRestart i ξ) 1) ω
    have hm (h : ℕ) : Measurable (F h) :=
      (measurable_const.mul ((measurable_epoch_power s 1).comp
        (measurable_epochRestart i))).indicator
          (measurableSet_eq_fun (measurable_weakEpochHeight i) measurable_const)
    have he : (fun ω => s ^ weakEpochHeight ω (i + 1)) =ᵐ[(offspringSeqLaw μ).toMeasure]
        (fun ω => ∑' h : ℕ, F h ω) := by
      filter_upwards [ae_epochsFinite μ hc hne] with ω hω
      rw [weakEpochHeight_succ hω i, pow_add]
      symm
      rw [tsum_eq_single (weakEpochHeight ω i)]
      · apply Set.indicator_of_mem
        rfl
      · intro h hh
        apply Set.indicator_of_notMem
        exact Ne.symm hh
    rw [lintegral_congr_ae he, lintegral_tsum (fun h => (hm h).aemeasurable)]
    have hterm (h : ℕ) : (∫⁻ ω, F h ω ∂(offspringSeqLaw μ).toMeasure) =
        (s ^ h * (offspringSeqLaw μ).toMeasure
          {ω | weakEpochHeight ω i = h}) * weakLadderPGF μ s := by
      change (∫⁻ ω, {ξ | weakEpochHeight ξ i = h}.indicator
        (fun ξ => s ^ h * s ^ weakEpochHeight (epochRestart i ξ) 1) ω
          ∂(offspringSeqLaw μ).toMeasure) = _
      have hr : Measurable (fun ω : ℕ → ℕ => s ^ weakEpochHeight (epochRestart i ω) 1) :=
        (measurable_epoch_power s 1).comp (measurable_epochRestart i)
      rw [lintegral_indicator (measurableSet_eq_fun (measurable_weakEpochHeight i)
        measurable_const), lintegral_const_mul (s ^ h) hr,
        lintegral_epochRestart_height μ hc hne i h (measurable_epoch_power s 1)]
      rw [mul_assoc]
      rfl
    simp_rw [hterm]
    rw [ENNReal.tsum_mul_right, ← lintegral_epochHeight μ i (fun h => s ^ h), ih, pow_succ]

end BGW.StableTrees.DiscreteHeightApprox
