/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxEpochs
import Mathlib.Probability.Independence.InfinitePi

/-!
# Pre-return duality and finiteness of weak ascending epochs

Negative prefixes are expressed without a totalized hitting time, and finite reversal
identifies their level occupations with first downward passages. Duality thus computes
occupation before the first return without assuming its finiteness.
Factoring the final independent step and summing offspring tails gives return mass
one, since the offspring mean is one. Shift invariance then gives all weak epochs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

/-- Strict negativity at positive times through `n`, before the first weak return. -/
def NegativePrefix (ω : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ u, 1 ≤ u → u ≤ n → walk ω u < 0

/-- Occupation of gap `y` at time `n` before any weak ascending return. -/
def negativeLevelEvent (y n : ℕ) : Set (ℕ → ℕ) :=
  {ω | walk ω n = -(y : ℤ) ∧ NegativePrefix ω n}

/-- Negative level occupations are measurable finite-prefix events. -/
theorem measurableSet_negativeLevelEvent (y n : ℕ) :
    MeasurableSet (negativeLevelEvent y n) := by
  have hm : MeasurableSet {ω | NegativePrefix ω n} := by
    simp only [NegativePrefix, ofPred_forall]
    exact MeasurableSet.iInter fun u => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => measurableSet_lt (measurable_walk u) measurable_const
  exact (measurableSet_eq_fun (measurable_walk n) measurable_const).inter hm

/-- Finite reversal sends a negative-prefix occupation to a strict downward passage. -/
private theorem negativeLevelEvent_eq_preimage (y n : ℕ) :
    negativeLevelEvent y n = revSeq n ⁻¹' forestHit y n := by
  ext ω
  have hw : walk (revSeq n ω) n = walk ω n := by
    simpa [walk] using walk_revSeq ω (k := n) (u := n) le_rfl
  change (walk ω n = -(y : ℤ) ∧ NegativePrefix ω n) ↔
    (walk (revSeq n ω) n = -(y : ℤ) ∧
      ∀ i < n, -(y : ℤ) < walk (revSeq n ω) i)
  rw [hw]
  constructor
  · rintro ⟨he, hn⟩
    refine ⟨he, fun i hi => ?_⟩
    rw [walk_revSeq ω hi.le, he]
    have hlt := hn (n - i) (by omega) (by omega)
    omega
  · rintro ⟨he, hn⟩
    refine ⟨he, fun u hu hun => ?_⟩
    have hlt := hn (n - u) (by omega)
    rw [walk_revSeq ω (by omega), Nat.sub_sub_self hun, he] at hlt
    omega

/-- The occupation and downward first-passage events have equal probabilities. -/
private theorem negativeLevelEvent_mass (μ : PMF ℕ) (y n : ℕ) :
    (offspringSeqLaw μ).toMeasure (negativeLevelEvent y n) =
      (offspringSeqLaw μ).toMeasure (forestHit y n) := by
  rw [negativeLevelEvent_eq_preimage, ← Measure.map_apply (measurable_revSeq n)
    (measurableSet_forestHit y n), map_revSeq_offspringSeqLaw]

/-- The expected pre-return occupation of each integer gap is exactly one,
expressed as a nonnegative series without presupposing return finiteness. -/
theorem tsum_negativeLevelEvent_mass (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (y : ℕ) :
    ∑' n : ℕ, (offspringSeqLaw μ).toMeasure (negativeLevelEvent y n) = 1 := by
  simp_rw [negativeLevelEvent_mass]
  rcases y with _ | y
  · have he (n : ℕ) : forestHit 0 n = if n = 0 then Set.univ else ∅ := by
      split_ifs with hn
      · subst n
        ext ω
        simp [forestHit, walk]
      · apply Set.eq_empty_iff_forall_notMem.mpr
        intro ω hω
        have hlt := hω.2 0 (by omega)
        simp [walk] at hlt
    simp [he, apply_ite]
  · simp_rw [forestHit_mass μ (show 1 ≤ y + 1 by omega)]
    exact Scalar.tsum_forestWeight_eq_one hc hne (y + 1)

/-- A negative-level event is determined by the offspring prefix before its time. -/
theorem preStopped_negativeLevelEvent (y n : ℕ) :
    PreStopped (fun _ => (n : ℕ∞)) (negativeLevelEvent y n) := by
  intro m ω ξ hm he
  have hnm : n = m := ENat.natCast_inj.mp hm
  subst m
  refine ⟨rfl, ?_⟩
  have hw (u : ℕ) (hu : u ≤ n) := walk_eq_of_agree he hu
  change (walk ω n = -(y : ℤ) ∧ NegativePrefix ω n) ↔
    (walk ξ n = -(y : ℤ) ∧ NegativePrefix ξ n)
  simp only [NegativePrefix, hw n le_rfl]
  constructor <;> rintro ⟨heq, hn⟩
  · exact ⟨heq, fun u hu hun => (hw u hun) ▸ hn u hu hun⟩
  · exact ⟨heq, fun u hu hun => (hw u hun).symm ▸ hn u hu hun⟩

/-- Probability of the last independent step exiting the negative half-line from gap `y`. -/
private theorem negativeLevelEvent_exit_mass (μ : PMF ℕ) (y n : ℕ) :
    (offspringSeqLaw μ).toMeasure
        (negativeLevelEvent y n ∩ {ω | y + 1 ≤ ω n}) =
      (offspringSeqLaw μ).toMeasure (negativeLevelEvent y n) *
        μ.toMeasure (Set.Ici (y + 1)) := by
  let A : Set (ℕ → ℕ) := {ω | y + 1 ≤ ω 0}
  have hN : IsSeqStoppingTime (fun _ : ℕ → ℕ => (n : ℕ∞)) :=
    fun _ _ _ hm _ => ⟨hm, Iff.rfl⟩
  have hfin : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, (n : ℕ∞) ≠ ⊤ := by simp
  have hA : MeasurableSet A := measurableSet_le measurable_const (measurable_pi_apply 0)
  have hr := stoppedRestart μ (fun _ => (n : ℕ∞)) hN hfin
    (preStopped_negativeLevelEvent y n) hA
  have he : {ω : ℕ → ℕ | ∃ m : ℕ, (n : ℕ∞) = m ∧ shiftSeq m ω ∈ A} =
      {ω | y + 1 ≤ ω n} := by
    ext ω
    simp [A, shiftSeq]
  rw [he] at hr
  have hm : (offspringSeqLaw μ).toMeasure A = μ.toMeasure (Set.Ici (y + 1)) := by
    change (Measure.infinitePi (fun _ : ℕ => μ.toMeasure))
      ((fun ω : ℕ → ℕ => ω 0) ⁻¹' Set.Ici (y + 1)) = _
    rw [← Measure.map_apply (measurable_pi_apply 0) measurableSet_Ici,
      Measure.infinitePi_map_eval]
  rwa [hm] at hr

/-- The sum of offspring upper tails is exactly the offspring mean. -/
theorem tsum_offspring_tails (μ : PMF ℕ) (hc : IsCritical μ) :
    ∑' y : ℕ, μ.toMeasure (Set.Ici (y + 1)) = 1 := by
  simp_rw [PMF.toMeasure_apply_eq_tsum, Set.indicator_apply, Set.mem_Ici]
  rw [ENNReal.tsum_comm]
  have he (k : ℕ) : (∑' y : ℕ, if y + 1 ≤ k then μ k else 0) = (k : ℝ≥0∞) * μ k := by
    rw [tsum_eq_sum (s := Finset.range k)]
    · calc
        _ = ∑ _y ∈ Finset.range k, μ k := by
          apply Finset.sum_congr rfl
          intro y hy
          exact ite_eq_left (Nat.succ_le_of_lt (Finset.mem_range.mp hy))
        _ = (k : ℝ≥0∞) * μ k := by simp [nsmul_eq_mul]
    · intro y hy
      exact ite_eq_right (by have := Finset.mem_range.not.mp hy; omega)
  simp_rw [he]
  exact hc

/-- The first weak ascending return occurs at time `n + 1`. -/
private def firstWeakReturnEvent (n : ℕ) : Set (ℕ → ℕ) :=
  {ω | NegativePrefix ω n ∧ 0 ≤ walk ω (n + 1)}

/-- First-return events are measurable. -/
private theorem measurableSet_firstWeakReturnEvent (n : ℕ) :
    MeasurableSet (firstWeakReturnEvent n) := by
  have hm : MeasurableSet {ω | NegativePrefix ω n} := by
    simp only [NegativePrefix, ofPred_forall]
    exact MeasurableSet.iInter fun u => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => measurableSet_lt (measurable_walk u) measurable_const
  exact hm.inter (measurableSet_le measurable_const (measurable_walk (n + 1)))

private theorem firstWeakReturnEvent_eq_iUnion (n : ℕ) :
    firstWeakReturnEvent n = ⋃ y : ℕ, negativeLevelEvent y n ∩ {ω | y + 1 ≤ ω n} := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hn, hs⟩
    have hw : walk ω n ≤ 0 := by
      by_cases he : n = 0
      · simp [he, walk]
      · exact (hn n (by omega) le_rfl).le
    let y := (-walk ω n).toNat
    have hy : (y : ℤ) = -walk ω n := Int.toNat_of_nonneg (by omega)
    have hstep := walk_succ_eq ω n
    exact ⟨y, ⟨by omega, hn⟩, by omega⟩
  · rintro ⟨y, ⟨hy, hn⟩, hs⟩
    have hstep := walk_succ_eq ω n
    exact ⟨hn, by omega⟩

private theorem level_exit_disjoint (n : ℕ) : Pairwise (fun y z : ℕ =>
    Disjoint (negativeLevelEvent y n ∩ {ω | y + 1 ≤ ω n})
      (negativeLevelEvent z n ∩ {ω | z + 1 ≤ ω n})) := by
  intro y z hyz
  apply Set.disjoint_left.mpr
  intro ω hy hz
  have hey := hy.1.1
  have hez := hz.1.1
  have : y = z := by omega
  exact hyz this

/-- First-return probability, summed over the gap immediately before its last step. -/
private theorem firstWeakReturnEvent_mass (μ : PMF ℕ) (n : ℕ) :
    (offspringSeqLaw μ).toMeasure (firstWeakReturnEvent n) =
      ∑' y : ℕ, (offspringSeqLaw μ).toMeasure (negativeLevelEvent y n) *
        μ.toMeasure (Set.Ici (y + 1)) := by
  rw [firstWeakReturnEvent_eq_iUnion, measure_iUnion (level_exit_disjoint n)
    (fun y => (measurableSet_negativeLevelEvent y n).inter
      (measurableSet_le measurable_const (measurable_pi_apply n)))]
  exact tsum_congr fun y => negativeLevelEvent_exit_mass μ y n

/-- First weak return has total probability one under criticality and nondegeneracy. -/
private theorem tsum_firstWeakReturnEvent_mass (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∑' n : ℕ, (offspringSeqLaw μ).toMeasure (firstWeakReturnEvent n) = 1 := by
  simp_rw [firstWeakReturnEvent_mass]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_right, tsum_negativeLevelEvent_mass μ hc hne, one_mul]
  exact tsum_offspring_tails μ hc

private theorem firstWeakReturnEvent_disjoint :
    Pairwise (fun n m : ℕ => Disjoint (firstWeakReturnEvent n) (firstWeakReturnEvent m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro ω hn hm
  rcases lt_or_gt_of_ne hnm with hlt | hlt
  · have hneg := hm.1 (n + 1) (by omega) (by omega)
    exact (not_lt_of_ge hn.2) hneg
  · have hneg := hn.1 (m + 1) (by omega) (by omega)
    exact (not_lt_of_ge hm.2) hneg

/-- A critical nondegenerate walk has a positive-time weak upward return almost surely. -/
theorem ae_hasWeakReturn (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, ∃ u : ℕ, 0 < u ∧ 0 ≤ walk ω u := by
  have hmass : (offspringSeqLaw μ).toMeasure (⋃ n, firstWeakReturnEvent n) = 1 := by
    rw [measure_iUnion firstWeakReturnEvent_disjoint measurableSet_firstWeakReturnEvent]
    exact tsum_firstWeakReturnEvent_mass μ hc hne
  have ha := (mem_ae_iff_prob_eq_one
    (MeasurableSet.iUnion measurableSet_firstWeakReturnEvent)).mpr hmass
  filter_upwards [ha] with ω hω
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hω
  exact ⟨n + 1, by omega, hn.2⟩

/-- Critical nondegenerate walks oscillate: all weak epochs are a.s. finite. -/
theorem ae_epochsFinite (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∀ᵐ ω ∂((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) : Measure (ℕ → ℕ)),
      EpochsFinite ω := by
  have ha (m : ℕ) : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure,
      ∃ u : ℕ, 0 < u ∧ 0 ≤ walk (shiftSeq m ω) u := by
    have h := ae_hasWeakReturn μ hc hne
    rw [← map_shiftSeq_offspringSeqLaw μ m] at h
    exact ae_of_ae_map (measurable_shiftSeq m).aemeasurable h
  have hall := ae_all_iff.mpr ha
  filter_upwards [hall] with ω hω
  intro i
  obtain ⟨u, hu, hw⟩ := hω (weakEpoch ω i)
  rw [walk_shiftSeq] at hw
  exact ⟨weakEpoch ω i + u, by omega, by omega⟩

end BGW.StableTrees.DiscreteHeightApprox
