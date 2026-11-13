/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxCycleShift

/-!
# Restart and independence of weak ascending cycles

History events are saturated under agreement up to the genuine extended epoch.
They are pre-stopped events on every sequence, while agreeing almost surely with
the finite-cycle history. This keeps totalized epochs out of the stopping-time premise.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

private def stoppedHistory (i : ℕ) (E : Set (ℕ → ℕ)) : Set (ℕ → ℕ) :=
  {ω | ∃ ξ, EpochsFinite ξ ∧ weakEpochStop ξ i = weakEpochStop ω i ∧
    (∀ k < (weakEpochStop ω i).toNat, ξ k = ω k) ∧ ξ ∈ E}

private theorem preStopped_stoppedHistory (i : ℕ) (E : Set (ℕ → ℕ)) :
    PreStopped (fun ω => weakEpochStop ω i) (stoppedHistory i E) := by
  intro n ω ξ hn he
  have hn' := (isSeqStoppingTime_weakEpochStop i n ω ξ hn he).1
  have hN : weakEpochStop ω i = weakEpochStop ξ i := hn.trans hn'.symm
  refine ⟨hn', ?_⟩
  constructor
  · rintro ⟨η, hη, hηN, hp, hE⟩
    refine ⟨η, hη, hηN.trans hN, ?_, hE⟩
    intro k hk
    have hkn : k < n := by simpa only [hn', ENat.toNat_natCast] using hk
    exact (hp k (by simpa only [hn, ENat.toNat_natCast] using hkn)).trans (he k hkn)
  · rintro ⟨η, hη, hηN, hp, hE⟩
    refine ⟨η, hη, hηN.trans hN.symm, ?_, hE⟩
    intro k hk
    have hkn : k < n := by simpa only [hn, ENat.toNat_natCast] using hk
    exact (hp k (by simpa only [hn', ENat.toNat_natCast] using hkn)).trans (he k hkn).symm

private theorem stoppedHistory_cycle_ae_eq (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (a : ℝ) (i : ℕ) (S : Finset ℕ) (hS : ∀ j ∈ S, j < i) (A : ℕ → Set ℕ) :
    stoppedHistory i {ω | ∀ j ∈ S, clusterVisits ω a j ∈ A j} =ᵐ[(offspringSeqLaw μ).toMeasure]
      {ω | ∀ j ∈ S, clusterVisits ω a j ∈ A j} := by
  filter_upwards [ae_epochsFinite μ hc hne] with ω hω
  apply propext
  constructor
  · rintro ⟨ξ, hξ, hN, hp, hE⟩ j hj
    have hτ : weakEpoch ξ i = weakEpoch ω i := by
      rw [weakEpochStop_eq_epoch hξ, weakEpochStop_eq_epoch hω] at hN
      exact ENat.natCast_inj.mp hN
    have hpre : ∀ k < weakEpoch ξ i, ξ k = ω k := by
      simpa only [weakEpochStop_eq_epoch hω, ENat.toNat_natCast, ← hτ] using hp
    have he := clusterVisits_eq_of_agree hξ hpre le_rfl (hS j hj) a
    rw [← he]
    exact hE j hj
  · intro hE
    exact ⟨ω, hω, rfl, fun _ _ => rfl, hE⟩

/-- Restart at the next cycle factors its occupation from every preceding finite cycle history. -/
theorem clusterVisits_history_factor (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (a : ℝ) (i : ℕ) (S : Finset ℕ) (hS : ∀ j ∈ S, j < i)
    (A : ℕ → Set ℕ) {C : Set ℕ} (hC : MeasurableSet C) :
    (offspringSeqLaw μ).toMeasure
        ({ω | ∀ j ∈ S, clusterVisits ω a j ∈ A j} ∩ {ω | clusterVisits ω a i ∈ C}) =
      (offspringSeqLaw μ).toMeasure {ω | ∀ j ∈ S, clusterVisits ω a j ∈ A j} *
        (offspringSeqLaw μ).toMeasure {ω | clusterVisits ω a 0 ∈ C} := by
  let E : Set (ℕ → ℕ) := {ω | ∀ j ∈ S, clusterVisits ω a j ∈ A j}
  let D : Set (ℕ → ℕ) := {ω | clusterVisits ω a 0 ∈ C}
  let R : Set (ℕ → ℕ) := {ω | ∃ n : ℕ, weakEpochStop ω i = n ∧ shiftSeq n ω ∈ D}
  have hD : MeasurableSet D := (measurable_clusterVisits a 0) hC
  have hr := stoppedRestart μ (fun ω => weakEpochStop ω i)
    (isSeqStoppingTime_weakEpochStop i) (ae_weakEpochStop_ne_top μ hc hne i)
    (preStopped_stoppedHistory i E) hD
  have hhist : stoppedHistory i E =ᵐ[(offspringSeqLaw μ).toMeasure] E :=
    stoppedHistory_cycle_ae_eq μ hc hne a i S hS A
  have hR : R =ᵐ[(offspringSeqLaw μ).toMeasure] {ω | clusterVisits ω a i ∈ C} := by
    filter_upwards [ae_epochsFinite μ hc hne] with ω hω
    apply propext
    change (∃ n : ℕ, weakEpochStop ω i = n ∧ clusterVisits (shiftSeq n ω) a 0 ∈ C) ↔ _
    rw [weakEpochStop_eq_epoch hω]
    simp only [ENat.natCast_inj]
    constructor
    · rintro ⟨n, hn, hm⟩
      rw [← hn, ← clusterVisits_shift_zero hω a i] at hm
      exact hm
    · intro hm
      refine ⟨weakEpoch ω i, rfl, ?_⟩
      rwa [← clusterVisits_shift_zero hω a i]
  have hinter : stoppedHistory i E ∩ R =ᵐ[(offspringSeqLaw μ).toMeasure]
      E ∩ {ω | clusterVisits ω a i ∈ C} := by
    filter_upwards [hhist, hR] with ω hω hω'
    exact congrArg₂ And hω hω'
  change (offspringSeqLaw μ).toMeasure (stoppedHistory i E ∩ R) =
    (offspringSeqLaw μ).toMeasure (stoppedHistory i E) * (offspringSeqLaw μ).toMeasure D at hr
  rw [measure_congr hinter, measure_congr hhist] at hr
  exact hr

/-- Every weak-cycle occupation has the first cycle's distribution. -/
theorem map_clusterVisits_eq_zero (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (a : ℝ) (i : ℕ) :
    (offspringSeqLaw μ).toMeasure.map (fun ω => clusterVisits ω a i) =
      (offspringSeqLaw μ).toMeasure.map (fun ω => clusterVisits ω a 0) := by
  apply Measure.ext
  intro C hC
  rw [Measure.map_apply (measurable_clusterVisits a i) hC,
    Measure.map_apply (measurable_clusterVisits a 0) hC]
  change (offspringSeqLaw μ).toMeasure {ω | clusterVisits ω a i ∈ C} =
    (offspringSeqLaw μ).toMeasure {ω | clusterVisits ω a 0 ∈ C}
  have h := clusterVisits_history_factor μ hc hne a i ∅ (by simp) (fun _ => Set.univ) hC
  simpa using h

/-- Cycle occupations are independent across cycle indices, for any fixed real band. -/
private theorem iIndepFun_clusterVisits (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (a : ℝ) :
    iIndepFun (fun i ω => clusterVisits ω a i) (offspringSeqLaw μ).toMeasure := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S A hA
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert i S hS ih =>
    have hnot : i ∉ S := by intro hi; exact (hS i hi).false
    have hfac := clusterVisits_history_factor μ hc hne a i S hS A
      (hA i (Finset.mem_insert_self i S))
    have hmarg := congrArg (fun ν : Measure ℕ => ν (A i))
      (map_clusterVisits_eq_zero μ hc hne a i)
    rw [Measure.map_apply (measurable_clusterVisits a i) (hA i (Finset.mem_insert_self i S)),
      Measure.map_apply (measurable_clusterVisits a 0) (hA i (Finset.mem_insert_self i S))] at hmarg
    change (offspringSeqLaw μ).toMeasure {ω | clusterVisits ω a i ∈ A i} =
      (offspringSeqLaw μ).toMeasure {ω | clusterVisits ω a 0 ∈ A i} at hmarg
    have he : (⋂ j ∈ insert i S, (fun ω => clusterVisits ω a j) ⁻¹' A j) =
        {ω | ∀ j ∈ S, clusterVisits ω a j ∈ A j} ∩ {ω | clusterVisits ω a i ∈ A i} := by
      ext ω
      simp only [Set.mem_iInter, Finset.mem_insert, Set.mem_preimage, Set.mem_inter_iff,
        Set.mem_ofPred_eq]
      aesop
    rw [he, hfac, ← hmarg, Finset.prod_insert hnot]
    have ih' := ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))
    have he' : {ω | ∀ j ∈ S, clusterVisits ω a j ∈ A j} =
        ⋂ j ∈ S, (fun ω => clusterVisits ω a j) ⁻¹' A j := by ext ω; simp
    rw [he', ih', mul_comm]
    rfl

/-- (Stopped restart at the epochs) the cycle visit counts are iid under the offspring law. -/
theorem clusterVisits_iid (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) {a : ℝ} (ha : 0 < a) :
    iIndepFun (fun i ω => clusterVisits ω a i)
      ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)) ∧
    ∀ i, ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)).map
        (fun ω => clusterVisits ω a i) =
      ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)).map
        (fun ω => clusterVisits ω a 0) := by
  -- Restart holds even for nonpositive bands; retain the frozen positive-band hypothesis.
  have _ha := ha
  exact ⟨iIndepFun_clusterVisits μ hc hne a, map_clusterVisits_eq_zero μ hc hne a⟩

end BGW.StableTrees.DiscreteHeightApprox
