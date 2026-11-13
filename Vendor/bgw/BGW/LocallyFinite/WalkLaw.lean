/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.SizeConditioning
public import Mathlib.MeasureTheory.Constructions.Pi
import Lean.Elab.Tactic.Omega

/-!
# The Łukasiewicz walk of offspring counts and the Kemperman identity for trees

Let `ω : Fin n → ℕ` be independent offspring counts with law `μ`, and let `S_n = ∑ (ω i - 1)`
(subtraction in `ℤ`) be the Łukasiewicz walk. The event `S_n = -1` is `∑ ω i + 1 = n`. Bridge
words of length `n` are exactly the step words `(ω i - 1)` of such vectors, and the walk weight of
the step word is `∏ μ {ω i}`, the mass of the point `ω` under `Measure.pi (fun _ => μ)`. Together
with the weighted cycle lemma this gives, for every offspring probability measure `μ` and every `n`,

`n * P(|T| = n) = P(S_n = -1)`

(`natCast_mul_bienaymeLaw_sizeEvent_eq_pi`), with no criticality, aperiodicity or positivity
assumption; both sides vanish for `n = 0`. The walk is the product measure on counts, not a
measure on `ℤ`, and only its endpoint at time `n` is considered. The forest version, the uniform
cyclic-shift representation and the conditional bridge law are not part of this module. Adapted
from `PoissonDeclumping/Lukasiewicz/BridgeLaw.lean` and `Cyclic/WalkBridge.lean`.
-/

@[expose] public section

namespace BGW

open MeasureTheory
open scoped ENNReal BigOperators

/-- The offspring-count vectors whose Łukasiewicz walk `∑ (ω i - 1)` ends at `-1`. -/
def countBridges (n : ℕ) : Set (Fin n → ℕ) := {ω | ∑ i, ω i + 1 = n}

/-- The step word `(ω i - 1)` of a vector of offspring counts, subtracting in `ℤ`. -/
def stepWord {n : ℕ} (ω : Fin n → ℕ) : List ℤ := List.ofFn fun i => (ω i : ℤ) - 1

theorem stepWord_injective {n : ℕ} : Function.Injective (stepWord (n := n)) := by
  intro ω ω' h
  funext i
  have := congrFun (List.ofFn_injective h) i
  omega

theorem stepWord_mem_bridgeWords_iff {n : ℕ} (ω : Fin n → ℕ) :
    stepWord ω ∈ bridgeWords n ↔ ω ∈ countBridges n := by
  have hsum : (stepWord ω).sum = ((∑ i, ω i : ℕ) : ℤ) - n := by
    simp [stepWord, List.sum_ofFn, Finset.sum_sub_distrib]
  unfold bridgeWords countBridges
  simp only [Set.mem_ofPred_eq, stepWord, List.length_ofFn, true_and]
  constructor
  · rintro ⟨-, hs⟩
    have : ((∑ i, ω i : ℕ) : ℤ) - n = -1 := by rw [← hsum]; exact hs
    omega
  · intro h
    refine ⟨fun a ha => ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      omega
    · have : ((∑ i, ω i : ℕ) : ℤ) - n = -1 := by omega
      rw [← this, ← hsum]; rfl

theorem walkWeight_stepWord (p : ℕ → ℝ≥0∞) {n : ℕ} (ω : Fin n → ℕ) :
    walkWeight p (stepWord ω) = ∏ i, p (ω i) := by
  rw [walkWeight, stepWord, List.map_ofFn, List.prod_ofFn]
  simp

/-- Every word of length `n` with entries at least `-1` is a step word. -/
theorem exists_stepWord_eq_of_entries {x : List ℤ} {n : ℕ} (hlen : x.length = n)
    (hge : ∀ a ∈ x, -1 ≤ a) : ∃ ω : Fin n → ℕ, stepWord ω = x := by
  subst hlen
  refine ⟨fun i => (x.get i + 1).toNat, ?_⟩
  have h : (fun i : Fin x.length => (((x.get i + 1).toNat : ℕ) : ℤ) - 1) = x.get := by
    funext i
    have := hge (x.get i) (List.get_mem x i)
    omega
  simp only [stepWord, h]
  exact List.ofFn_get x

theorem exists_stepWord_eq {x : List ℤ} {n : ℕ} (hx : x ∈ bridgeWords n) :
    ∃ ω : Fin n → ℕ, stepWord ω = x :=
  exists_stepWord_eq_of_entries hx.1 hx.2.1

/-- Reindexing the bridge words by offspring-count vectors. -/
theorem tsum_bridgeWords_walkWeight (p : ℕ → ℝ≥0∞) (n : ℕ) :
    ∑' x : List ℤ, Set.indicator (bridgeWords n) (walkWeight p) x =
      ∑' ω : Fin n → ℕ, Set.indicator (countBridges n) (fun ω => ∏ i, p (ω i)) ω := by
  have hrange : Function.support (Set.indicator (bridgeWords n) (walkWeight p)) ⊆
      Set.range (stepWord (n := n)) := by
    intro x hx
    by_contra hrange
    apply hx
    have hx' : x ∉ bridgeWords n := fun h => hrange (exists_stepWord_eq h)
    exact Set.indicator_of_notMem hx' _
  rw [← stepWord_injective.tsum_eq hrange]
  refine tsum_congr fun ω => ?_
  by_cases h : ω ∈ countBridges n
  · rw [Set.indicator_of_mem ((stepWord_mem_bridgeWords_iff ω).mpr h), Set.indicator_of_mem h,
      walkWeight_stepWord]
  · rw [Set.indicator_of_notMem (mt (stepWord_mem_bridgeWords_iff ω).mp h),
      Set.indicator_of_notMem h]

/-- The mass of `countBridges n` under the product measure is the sum of its point masses. -/
theorem pi_countBridges (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) :
    Measure.pi (fun _ : Fin n => μ) (countBridges n) =
      ∑' ω : Fin n → ℕ, Set.indicator (countBridges n) (fun ω => ∏ i, μ {ω i}) ω := by
  have hmeas : MeasurableSet (countBridges n) := (Set.to_countable _).measurableSet
  rw [← Measure.tsum_indicator_apply_singleton (Measure.pi fun _ : Fin n => μ) _ hmeas]
  simp only [Measure.pi_singleton]

/-- Kemperman's identity for trees: `n * P(|T| = n) = P(S_n = -1)`. -/
theorem LocallyFinite.natCast_mul_bienaymeLaw_sizeEvent_eq_pi (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (n : ℕ) :
    (n : ℝ≥0∞) * LocallyFinite.bienaymeLaw μ (LocallyFinite.sizeEvent n) =
      Measure.pi (fun _ : Fin n => μ) (countBridges n) := by
  rw [LocallyFinite.natCast_mul_bienaymeLaw_sizeEvent, tsum_bridgeWords_walkWeight,
    pi_countBridges]

end BGW
