/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.WalkLaw
public import BGW.Tree.ForestCycle
import Lean.Elab.Tactic.Omega

/-!
# Kemperman's identity for forests

For an offspring probability measure `μ`, `ℓ ≥ 1` and every `n`, the total weight
`forestWeight (fun d => μ {d}) ℓ n` of the ordered forests of `ℓ` trees with `n` vertices satisfies

`n * forestWeight μ ℓ n = ℓ * Measure.pi (fun _ : Fin n => μ) {ω | ∑ i, ω i + ℓ = n}`,

that is `n P(|𝒢_ℓ| = n) = ℓ P(S_n = -ℓ)` for `ℓ` independent trees and the Łukasiewicz walk of
independent offspring counts (`natCast_mul_forestWeight_eq_pi`). No criticality, aperiodicity or
positivity is assumed; both sides vanish when `n < ℓ`, and `ℓ = 1` is the identity for trees
(`forestWeight_one_eq_bienaymeLaw_sizeEvent`, `countForestBridges_one`). The multiplied form is
kept: no division and no conditioning event is involved. Adapted from
`PoissonDeclumping/Bridge/Kemperman.lean`; the first-passage convolution, the conditional bridge law
and local limits are not part of this module.
-/

@[expose] public section

namespace BGW

open MeasureTheory
open scoped ENNReal BigOperators

/-- Offspring-count vectors whose walk `∑ (ω i - 1)` ends at `-ℓ`. -/
def countForestBridges (ℓ n : ℕ) : Set (Fin n → ℕ) := {ω | ∑ i, ω i + ℓ = n}

theorem countForestBridges_one (n : ℕ) : countForestBridges 1 n = countBridges n := rfl

theorem countForestBridges_eq_empty_of_lt {ℓ n : ℕ} (h : n < ℓ) : countForestBridges ℓ n = ∅ := by
  ext ω
  simp only [countForestBridges, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  omega

theorem stepWord_mem_forestBridgeWords_iff {ℓ n : ℕ} (ω : Fin n → ℕ) :
    stepWord ω ∈ forestBridgeWords ℓ n ↔ ω ∈ countForestBridges ℓ n := by
  have hsum : (stepWord ω).sum = ((∑ i, ω i : ℕ) : ℤ) - n := by
    simp [stepWord, List.sum_ofFn, Finset.sum_sub_distrib]
  unfold forestBridgeWords countForestBridges
  simp only [Set.mem_ofPred_eq, stepWord, List.length_ofFn, true_and]
  constructor
  · rintro ⟨-, hs⟩
    have : ((∑ i, ω i : ℕ) : ℤ) - n = -(ℓ : ℤ) := by rw [← hsum]; exact hs
    omega
  · intro h
    refine ⟨fun a ha => ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      omega
    · have : ((∑ i, ω i : ℕ) : ℤ) - n = -(ℓ : ℤ) := by omega
      rw [← this, ← hsum]; rfl

/-- Reindexing the forest bridge words by offspring-count vectors. -/
theorem tsum_forestBridgeWords_walkWeight (p : ℕ → ℝ≥0∞) (ℓ n : ℕ) :
    ∑' x : List ℤ, Set.indicator (forestBridgeWords ℓ n) (walkWeight p) x =
      ∑' ω : Fin n → ℕ, Set.indicator (countForestBridges ℓ n) (fun ω => ∏ i, p (ω i)) ω := by
  have hrange : Function.support (Set.indicator (forestBridgeWords ℓ n) (walkWeight p)) ⊆
      Set.range (stepWord (n := n)) := by
    intro x hx
    by_contra hrange
    apply hx
    have hx' : x ∉ forestBridgeWords ℓ n := fun h =>
      hrange (exists_stepWord_eq_of_entries h.1 h.2.1)
    exact Set.indicator_of_notMem hx' _
  rw [← stepWord_injective.tsum_eq hrange]
  refine tsum_congr fun ω => ?_
  by_cases h : ω ∈ countForestBridges ℓ n
  · rw [Set.indicator_of_mem ((stepWord_mem_forestBridgeWords_iff ω).mpr h),
      Set.indicator_of_mem h, walkWeight_stepWord]
  · rw [Set.indicator_of_notMem (mt (stepWord_mem_forestBridgeWords_iff ω).mp h),
      Set.indicator_of_notMem h]

/-- The mass of any set of count vectors under the product measure is the sum of its point
masses. -/
theorem pi_eq_tsum_indicator (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ}
    (A : Set (Fin n → ℕ)) :
    Measure.pi (fun _ : Fin n => μ) A =
      ∑' ω : Fin n → ℕ, Set.indicator A (fun ω => ∏ i, μ {ω i}) ω := by
  have hmeas : MeasurableSet A := (Set.to_countable _).measurableSet
  rw [← Measure.tsum_indicator_apply_singleton (Measure.pi fun _ : Fin n => μ) _ hmeas]
  simp only [Measure.pi_singleton]

/-- **Kemperman's identity for forests**: `n P(|𝒢_ℓ| = n) = ℓ P(S_n = -ℓ)`, for every offspring
probability measure, every `1 ≤ ℓ` and every `n`. -/
theorem natCast_mul_forestWeight_eq_pi (μ : Measure ℕ) [IsProbabilityMeasure μ] {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (n : ℕ) :
    (n : ℝ≥0∞) * forestWeight (fun d => μ {d}) ℓ n =
      (ℓ : ℝ≥0∞) * Measure.pi (fun _ : Fin n => μ) (countForestBridges ℓ n) := by
  rw [natCast_mul_forestWeight _ hℓ, tsum_forestBridgeWords_walkWeight, pi_eq_tsum_indicator]

/-- A forest of one tree is a tree. -/
theorem forestWeight_one (p : ℕ → ℝ≥0∞) (n : ℕ) :
    forestWeight p 1 n = ∑' t : PlaneTree, if t.size = n then PlaneTree.weight p t else 0 := by
  have hrange : Function.support (fun ts : PlaneForest =>
      if ts.length = 1 ∧ PlaneForest.size ts = n then (ts.map (PlaneTree.weight p)).prod
        else 0) ⊆ Set.range (fun t : PlaneTree => [t]) := by
    intro ts hts
    by_contra hr
    apply hts
    have : ¬ (ts.length = 1 ∧ PlaneForest.size ts = n) := fun h => by
      obtain ⟨t, rfl⟩ := List.length_eq_one_iff.mp h.1
      exact hr ⟨t, rfl⟩
    exact ite_eq_right this
  unfold forestWeight
  rw [← List.singleton_injective.tsum_eq hrange]
  refine tsum_congr fun t => ?_
  simp [PlaneForest.size]

theorem LocallyFinite.forestWeight_one_eq_bienaymeLaw_sizeEvent (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (n : ℕ) :
    forestWeight (fun d => μ {d}) 1 n =
      LocallyFinite.bienaymeLaw μ (LocallyFinite.sizeEvent n) := by
  rw [forestWeight_one, LocallyFinite.bienaymeLaw_sizeEvent]

end BGW
