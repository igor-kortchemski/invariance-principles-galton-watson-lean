/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteBridgeBasic

/-!
# Finite-vector bridge prefix masses

Restriction of the infinite iid product to `Fin n` transports K02's conditional
prefix mass identity to offspring vectors.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

namespace BGW.StableTrees.DiscreteBridge

open BGW BGW.StableTrees.DiscreteForest

/-- Discrete measurable structure for degree words, local to the prefix adapter. -/
local instance prefixWordMeasurable : MeasurableSpace (List ℕ) := ⊤
/-- Degree-word singletons are measurable in the local structure. -/
local instance prefixWordSingleton : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

/-- Conditional on `W_n = -1`, the mass of the first `m` degrees `a` is
`∏ μ(a_i) * walkProb μ (n-m) (-1-W_m(a)) / walkProb μ n (-1)`. -/
theorem bridgeVecPrefix_cond_mass (μ : PMF ℕ) {n m : ℕ} {a : List ℕ} (ham : a.length = m)
    (hmn : m ≤ n) (hpos : 0 < walkProb μ n (-1)) :
    ((offspringVec μ n)[|countBridges n]).real
        {ω | (List.ofFn ω).take m = a} =
      degreeWeight μ a * (walkProb μ ((n - m : ℕ) : ℤ) (-1 - prefixWalk a) /
        walkProb μ n (-1)) := by

  unfold offspringVec
  let r : (ℕ → ℕ) → Fin n → ℕ := fun ω i => ω i
  have hr : Measurable r := by fun_prop
  have hp : r ⁻¹' {ω | (List.ofFn ω).take m = a} = {ω | seqPrefix m ω = a} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, r, ← seqPrefix_eq_ofFn, take_seqPrefix n m ω hmn]
  have hb : r ⁻¹' countBridges n = {ω | walk ω n = -1} := by
    ext ω
    have hs : (stepWord (r ω)).sum = walk ω n := by
      rw [stepWord, List.sum_ofFn]
      exact Fin.sum_univ_eq_sum_range (fun j => (ω j : ℤ) - 1) n
    change r ω ∈ countBridges n ↔ walk ω n = -1
    rw [← stepWord_mem_bridgeWords_iff]
    constructor
    · intro hx
      exact hs ▸ hx.2.2
    · intro hw
      exact ⟨by simp [stepWord], fun j hj => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
        omega, hs.trans hw⟩
  have hcond : ((Measure.pi fun _ : Fin n => μ.toMeasure)[|countBridges n]).real
      {ω | (List.ofFn ω).take m = a} =
      (((offspringSeqLaw μ).toMeasure)[|{ω | walk ω n = -1}]).real
        {ω | seqPrefix m ω = a} := by
    simp only [measureReal_def]
    have hpa : MeasurableSet {ω : Fin n → ℕ | (List.ofFn ω).take m = a} :=
      (Set.to_countable _).measurableSet
    have hpb : MeasurableSet {ω : ℕ → ℕ | seqPrefix m ω = a} :=
      (measurable_seqPrefix m) (measurableSet_singleton a)
    rw [cond_apply' hpa, cond_apply' hpb,
      ← map_offspringSeqLaw_initial μ n]
    change ((((offspringSeqLaw μ).toMeasure.map r) (countBridges n))⁻¹ *
      ((offspringSeqLaw μ).toMeasure.map r)
        (countBridges n ∩ {ω | (List.ofFn ω).take m = a})).toReal = _
    rw [Measure.map_apply hr (Set.to_countable _).measurableSet,
      Measure.map_apply hr (Set.to_countable _).measurableSet,
      preimage_inter, hp, hb]
  rw [hcond, bridgePrefix_cond_mass μ ham hmn hpos, bridgePrefixDensity]

end BGW.StableTrees.DiscreteBridge
