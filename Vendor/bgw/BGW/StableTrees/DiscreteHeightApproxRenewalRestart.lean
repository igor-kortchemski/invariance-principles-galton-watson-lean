/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxSecondMoment

/-!
# Restart with the height of a weak ascending epoch

The complete restarted sequence is independent of every pre-stopped event. Applying
this to an epoch's attained walk value permits occupation at that random gap level.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

/-- The sequence restarted at the `i`th totalized natural weak epoch. -/
noncomputable def epochRestart (i : ℕ) (ω : ℕ → ℕ) : ℕ → ℕ := shiftSeq (weakEpoch ω i) ω

/-- Restart at a natural weak epoch is measurable on all sequences. -/
theorem measurable_epochRestart (i : ℕ) : Measurable (epochRestart i) := by
  apply Measurable.of_eval
  intro k
  have hm : Measurable (fun p : (ℕ → ℕ) × ℕ => p.1 (p.2 + k)) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply (n + k)
  exact hm.comp (measurable_id.prodMk (measurable_weakEpoch i))

/-- The nonnegative attained height of a weak ascending epoch. -/
noncomputable def weakEpochHeight (ω : ℕ → ℕ) (i : ℕ) : ℕ :=
  (walk ω (weakEpoch ω i)).toNat

/-- The walk value at a weak epoch is nonnegative on finite paths. -/
theorem walk_weakEpoch_nonneg {ω : ℕ → ℕ} (hω : EpochsFinite ω) (i : ℕ) :
    0 ≤ walk ω (weakEpoch ω i) := by
  have h := (reflGap_zero_iff_record ω _).mp (reflGap_weakEpoch hω i) 0 (Nat.zero_le _)
  simpa [walk] using h

/-- Natural epoch heights agree with the attained integer walk values on finite paths. -/
theorem weakEpochHeight_cast {ω : ℕ → ℕ} (hω : EpochsFinite ω) (i : ℕ) :
    (weakEpochHeight ω i : ℤ) = walk ω (weakEpoch ω i) :=
  Int.toNat_of_nonneg (walk_weakEpoch_nonneg hω i)

/-- Walk evaluation at a totalized natural weak epoch is measurable. -/
theorem measurable_walk_epoch (i : ℕ) :
    Measurable (fun ω => walk ω (weakEpoch ω i)) := by
  have hm : Measurable (fun p : (ℕ → ℕ) × ℕ => walk p.1 p.2) :=
    measurable_from_prod_countable_left fun n => measurable_walk n
  exact hm.comp (measurable_id.prodMk (measurable_weakEpoch i))

/-- Every attained natural epoch height is measurable. -/
theorem measurable_weakEpochHeight (i : ℕ) : Measurable (fun ω => weakEpochHeight ω i) :=
  (measurable_of_countable Int.toNat).comp (measurable_walk_epoch i)

private def stoppedEpochWalkEvent (i : ℕ) (h : ℤ) : Set (ℕ → ℕ) :=
  {ω | ∃ n : ℕ, weakEpochStop ω i = n ∧ walk ω n = h}

private theorem preStopped_epochWalkEvent (i : ℕ) (h : ℤ) :
    PreStopped (fun ω => weakEpochStop ω i) (stoppedEpochWalkEvent i h) := by
  intro n ω ξ hn he
  have hn' := (isSeqStoppingTime_weakEpochStop i n ω ξ hn he).1
  refine ⟨hn', ?_⟩
  constructor
  · rintro ⟨m, hm, hw⟩
    have hmn : m = n := ENat.natCast_inj.mp (hm.symm.trans hn)
    subst m
    exact ⟨n, hn', (walk_eq_of_agree he le_rfl) ▸ hw⟩
  · rintro ⟨m, hm, hw⟩
    have hmn : m = n := ENat.natCast_inj.mp (hm.symm.trans hn')
    subst m
    exact ⟨n, hn, (walk_eq_of_agree he le_rfl).symm ▸ hw⟩

private theorem stoppedEpochWalkEvent_ae_eq (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (i : ℕ) (h : ℤ) :
    stoppedEpochWalkEvent i h =ᵐ[(offspringSeqLaw μ).toMeasure]
      {ω | walk ω (weakEpoch ω i) = h} := by
  filter_upwards [ae_epochsFinite μ hc hne] with ω hω
  apply propext
  change (∃ n : ℕ, weakEpochStop ω i = n ∧ walk ω n = h) ↔ _
  rw [weakEpochStop_eq_epoch hω]
  simp only [ENat.natCast_inj]
  constructor
  · rintro ⟨n, hn, hw⟩
    rwa [← hn] at hw
  · intro hw
    exact ⟨weakEpoch ω i, rfl, hw⟩

/-- Restricted restart law for any pre-stopped event at a genuine weak epoch. -/
theorem map_epochRestart_restrict (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (i : ℕ) {E : Set (ℕ → ℕ)} (hE : PreStopped (fun ω => weakEpochStop ω i) E) :
    ((offspringSeqLaw μ).toMeasure.restrict E).map (epochRestart i) =
      (offspringSeqLaw μ).toMeasure E • (offspringSeqLaw μ).toMeasure := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_epochRestart i) hA,
    Measure.restrict_apply ((measurable_epochRestart i) hA), Measure.smul_apply, smul_eq_mul]
  have h := stoppedRestart μ (fun ω => weakEpochStop ω i)
    (isSeqStoppingTime_weakEpochStop i) (ae_weakEpochStop_ne_top μ hc hne i) hE hA
  have he : E ∩ {ω | ∃ n : ℕ, weakEpochStop ω i = n ∧ shiftSeq n ω ∈ A}
      =ᵐ[(offspringSeqLaw μ).toMeasure] epochRestart i ⁻¹' A ∩ E := by
    filter_upwards [ae_epochsFinite μ hc hne] with ω hω
    apply propext
    change (ω ∈ E ∧ ∃ n : ℕ, weakEpochStop ω i = n ∧ shiftSeq n ω ∈ A) ↔ _
    rw [weakEpochStop_eq_epoch hω]
    simp only [ENat.natCast_inj]
    constructor
    · rintro ⟨hmem, n, hn, hr⟩
      rw [← hn] at hr
      exact ⟨hr, hmem⟩
    · rintro ⟨hr, hmem⟩
      exact ⟨hmem, weakEpoch ω i, rfl, hr⟩
  rwa [measure_congr he] at h

/-- Nonnegative integrals factor at a weak epoch over any pre-stopped event. -/
theorem lintegral_epochRestart_restrict (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (i : ℕ) {E : Set (ℕ → ℕ)} (hE : PreStopped (fun ω => weakEpochStop ω i) E)
    {F : (ℕ → ℕ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω in E, F (epochRestart i ω) ∂(offspringSeqLaw μ).toMeasure =
      (offspringSeqLaw μ).toMeasure E * ∫⁻ ω, F ω ∂(offspringSeqLaw μ).toMeasure := by
  rw [← lintegral_map hF (measurable_epochRestart i), map_epochRestart_restrict μ hc hne i hE,
    lintegral_smul_measure, smul_eq_mul]

/-- The occupation of the epoch's attained integer gap has conditional mean one. -/
theorem lintegral_epochRestart_level (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (i h : ℕ) :
    ∫⁻ ω in {ω | walk ω (weakEpoch ω i) = (h : ℤ)},
        levelOccupation h (epochRestart i ω) ∂(offspringSeqLaw μ).toMeasure =
      (offspringSeqLaw μ).toMeasure {ω | walk ω (weakEpoch ω i) = (h : ℤ)} := by
  have he := stoppedEpochWalkEvent_ae_eq μ hc hne i (h : ℤ)
  rw [← Measure.restrict_congr_set he,
    lintegral_epochRestart_restrict μ hc hne i (preStopped_epochWalkEvent i (h : ℤ))
      (measurable_levelOccupation h), lintegral_levelOccupation μ hc hne h, mul_one,
    measure_congr he]

/-- Restarted nonnegative observables factor over each attained natural epoch height. -/
theorem lintegral_epochRestart_height (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (i h : ℕ) {F : (ℕ → ℕ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω in {ω | weakEpochHeight ω i = h}, F (epochRestart i ω)
        ∂(offspringSeqLaw μ).toMeasure =
      (offspringSeqLaw μ).toMeasure {ω | weakEpochHeight ω i = h} *
        ∫⁻ ω, F ω ∂(offspringSeqLaw μ).toMeasure := by
  have hn : {ω | walk ω (weakEpoch ω i) = (h : ℤ)} =ᵐ[(offspringSeqLaw μ).toMeasure]
      {ω | weakEpochHeight ω i = h} := by
    filter_upwards [ae_epochsFinite μ hc hne] with ω hω
    apply propext
    rw [← weakEpochHeight_cast hω i, Int.natCast_inj]
  have he := (stoppedEpochWalkEvent_ae_eq μ hc hne i (h : ℤ)).trans hn
  rw [← Measure.restrict_congr_set he,
    lintegral_epochRestart_restrict μ hc hne i (preStopped_epochWalkEvent i (h : ℤ)) hF,
    measure_congr he]

end BGW.StableTrees.DiscreteHeightApprox
