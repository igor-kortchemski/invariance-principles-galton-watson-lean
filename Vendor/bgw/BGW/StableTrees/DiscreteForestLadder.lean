/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestHitMass

/-!
# Almost sure finiteness of ladder times

Extinction normalizes the law of first passage to level `-1`, so the walk reaches `-1`
almost surely. Shift invariance then gives such a passage below every starting value,
simultaneously at every integer time. This avoids a separate general random-walk
oscillation theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Classical

namespace BGW.StableTrees.DiscreteForest

private theorem forestHit_disjoint (j : ℕ) :
    Pairwise (fun i k => Disjoint (forestHit j i) (forestHit j k)) := by
  intro i k hik
  apply Set.disjoint_left.mpr
  intro ω hi hk
  rcases lt_or_gt_of_ne hik with h | h
  · have hn := hk.2 i h
    rw [hi.1] at hn
    omega
  · have hn := hi.2 k h
    rw [hk.1] at hn
    omega

private theorem ae_hits_neg_one (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, ∃ k, walk ω k = -1 := by
  have hmass : (offspringSeqLaw μ).toMeasure (⋃ n, forestHit 1 n) = 1 := by
    rw [measure_iUnion (forestHit_disjoint 1) (measurableSet_forestHit 1)]
    simp_rw [forestHit_mass μ le_rfl]
    exact Scalar.tsum_forestWeight_eq_one hc hne 1
  have ha := (mem_ae_iff_prob_eq_one
    (MeasurableSet.iUnion (measurableSet_forestHit 1))).mpr hmass
  filter_upwards [ha] with ω hω
  obtain ⟨n, hn⟩ := mem_iUnion.mp hω
  exact ⟨n, by simpa using hn.1⟩

/-- Critical nondegenerate walks reach every level downward a.s. -/
theorem ae_ladderFinite (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, LadderFinite ω := by
  have ha (m : ℕ) : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure,
      ∃ k, walk (shiftSeq m ω) k = -1 := by
    have h := ae_hits_neg_one μ hc hne
    rw [← map_shiftSeq_offspringSeqLaw μ m] at h
    exact ae_of_ae_map (measurable_shiftSeq m).aemeasurable h
  have hall : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure,
      ∀ m : ℕ, ∃ k, walk (shiftSeq m ω) k = -1 := ae_all_iff.mpr ha
  filter_upwards [hall] with ω hω
  intro r
  induction r with
  | zero => exact ⟨0, by simp [walk]⟩
  | succ r ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨k, hk⟩ := hω m
    rw [walk_shiftSeq, hm] at hk
    exact ⟨m + k, by omega⟩

end BGW.StableTrees.DiscreteForest
