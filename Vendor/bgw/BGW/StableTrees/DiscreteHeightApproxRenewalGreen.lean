/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxRenewalCycles

/-!
# The Green diagonal and weak ascending renewal

Splitting killed visits at weak epochs and applying the exact conditional level
mean identifies the Green diagonal with the expected number of epoch heights below
its level. Zero height increments remain included in this renewal function.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

/-- Renewal function expressed through the actual weak ascending epoch heights. -/
noncomputable def weakLadderRenewal (μ : PMF ℕ) (m : ℕ) : ℝ≥0∞ :=
  ∑' i : ℕ, (offspringSeqLaw μ).toMeasure {ω | weakEpochHeight ω i < m}

private def epochLevel (i h : ℕ) : Set (ℕ → ℕ) :=
  {ω | walk ω (weakEpoch ω i) = (h : ℤ)}

private theorem measurableSet_epochLevel (i h : ℕ) : MeasurableSet (epochLevel i h) :=
  measurableSet_eq_fun (measurable_walk_epoch i) measurable_const

private noncomputable def killedOccupation (m : ℕ) (ω : ℕ → ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, (killedGapEvent m m n).indicator (fun _ => 1) ω

private theorem lintegral_killedOccupation (μ : PMF ℕ) (m : ℕ) :
    ∫⁻ ω, killedOccupation m ω ∂(offspringSeqLaw μ).toMeasure = killedGapGreen μ m m := by
  change (∫⁻ ω, ∑' n : ℕ, (killedGapEvent m m n).indicator (fun _ => (1 : ℝ≥0∞)) ω
    ∂(offspringSeqLaw μ).toMeasure) = _
  rw [lintegral_tsum (fun n => (measurable_const.indicator
    (measurableSet_killedGapEvent m m n)).aemeasurable)]
  unfold killedGapGreen
  apply tsum_congr
  intro n
  exact lintegral_indicator_fun_one (measurableSet_killedGapEvent m m n)

private theorem sum_epoch_level_indicators {ω : ℕ → ℕ} (hω : EpochsFinite ω) (i m : ℕ) :
    (∑ h ∈ Finset.range m, (epochLevel i h).indicator (fun _ => (1 : ℝ≥0∞)) ω) =
      {ξ | weakEpochHeight ξ i < m}.indicator (fun _ => 1) ω := by
  have hcast := weakEpochHeight_cast hω i
  simp only [epochLevel, Set.indicator_apply, Set.mem_ofPred_eq, ← hcast, Int.natCast_inj]
  by_cases hh : weakEpochHeight ω i < m
  · rw [Finset.sum_eq_single (weakEpochHeight ω i)]
    · simp [hh]
    · intro h _ hne
      exact ite_eq_right (Ne.symm hne)
    · intro hn
      exact (hn (Finset.mem_range.mpr hh)).elim
  · rw [ite_eq_right hh]
    apply Finset.sum_eq_zero
    intro h hh'
    apply ite_eq_right
    intro he
    have hm := Finset.mem_range.mp hh'
    omega

private theorem sum_epoch_level_mass (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (i m : ℕ) :
    (∑ h ∈ Finset.range m, (offspringSeqLaw μ).toMeasure (epochLevel i h)) =
      (offspringSeqLaw μ).toMeasure {ω | weakEpochHeight ω i < m} := by
  have he : (fun ω => ∑ h ∈ Finset.range m,
      (epochLevel i h).indicator (fun _ => (1 : ℝ≥0∞)) ω) =ᵐ[(offspringSeqLaw μ).toMeasure]
        {ξ | weakEpochHeight ξ i < m}.indicator (fun _ => 1) := by
    filter_upwards [ae_epochsFinite μ hc hne] with ω hω
    exact sum_epoch_level_indicators hω i m
  have hint := lintegral_congr_ae he
  rw [lintegral_finsetSum (Finset.range m) (fun h _ =>
    measurable_const.indicator (measurableSet_epochLevel i h))] at hint
  simp_rw [lintegral_indicator_fun_one (measurableSet_epochLevel i _)] at hint
  rw [lintegral_indicator_fun_one (measurableSet_lt (measurable_weakEpochHeight i)
    measurable_const)] at hint
  exact hint

/-- The killed-gap Green diagonal equals the weak ascending height renewal function. -/
theorem killedGapGreen_diag_eq_renewal (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (m : ℕ) : killedGapGreen μ m m = weakLadderRenewal μ m := by
  let F (i h : ℕ) (ω : ℕ → ℕ) : ℝ≥0∞ := (epochLevel i h).indicator
    (fun ξ => levelOccupation h (epochRestart i ξ)) ω
  have hmF (i h : ℕ) : Measurable (F i h) :=
    ((measurable_levelOccupation h).comp (measurable_epochRestart i)).indicator
      (measurableSet_epochLevel i h)
  have hms (i : ℕ) : Measurable (fun ω => ∑ h ∈ Finset.range m, F i h ω) :=
    Finset.measurable_sum _ (fun h _ => hmF i h)
  have he : killedOccupation m =ᵐ[(offspringSeqLaw μ).toMeasure]
      (fun ω => ∑' i : ℕ, ∑ h ∈ Finset.range m, F i h ω) := by
    filter_upwards [ae_epochsFinite μ hc hne] with ω hω
    exact killedOccupation_eq_cycle_rewards hω m
  rw [← lintegral_killedOccupation μ m, lintegral_congr_ae he,
    lintegral_tsum (fun i => (hms i).aemeasurable)]
  change (∑' i : ℕ, ∫⁻ ω, ∑ h ∈ Finset.range m, F i h ω
    ∂(offspringSeqLaw μ).toMeasure) = _
  unfold weakLadderRenewal
  apply tsum_congr
  intro i
  rw [lintegral_finsetSum (Finset.range m) (fun h _ => hmF i h)]
  calc
    _ = ∑ h ∈ Finset.range m, (offspringSeqLaw μ).toMeasure (epochLevel i h) := by
      apply Finset.sum_congr rfl
      intro h _
      change (∫⁻ ω, (epochLevel i h).indicator
        (fun ξ => levelOccupation h (epochRestart i ξ)) ω ∂(offspringSeqLaw μ).toMeasure) = _
      rw [lintegral_indicator (measurableSet_epochLevel i h)]
      exact lintegral_epochRestart_level μ hc hne i h
    _ = _ := sum_epoch_level_mass μ hc hne i m

/-- The weak ascending height renewal function is finite at every finite level. -/
theorem weakLadderRenewal_lt_top (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (m : ℕ) :
    weakLadderRenewal μ m < ∞ := by
  rw [← killedGapGreen_diag_eq_renewal μ hc hne m]
  exact killedGapGreen_lt_top μ hc hne m m

/-- The weak ascending height renewal function is increasing in its cutoff level. -/
theorem weakLadderRenewal_mono (μ : PMF ℕ) : Monotone (weakLadderRenewal μ) := by
  intro m n hmn
  apply ENNReal.tsum_le_tsum
  intro i
  exact measure_mono (fun ω hω => lt_of_lt_of_le hω hmn)

end BGW.StableTrees.DiscreteHeightApprox
