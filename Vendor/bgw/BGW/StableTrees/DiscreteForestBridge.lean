/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestWordMass

/-!
# Prefix masses for the offspring walk bridge

Deterministic splitting at the end of a word and the product law identify the
remaining endpoint mass. Conditioning divides by the full bridge mass.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

namespace BGW.StableTrees.DiscreteForest

/-- A local discrete structure for bridge degree-word observables. -/
local instance bridgeWordMeasurable : MeasurableSpace (List ℕ) := ⊤
/-- Degree-word singletons are measurable in the bridge's local structure. -/
local instance bridgeWordSingleton : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

/-- The word walk agrees with the walk of its originating sequence. -/
theorem prefixWalk_seqPrefix (m : ℕ) (ω : ℕ → ℕ) :
    prefixWalk (seqPrefix m ω) = walk ω m := by
  rw [prefixWalk_eq_sum_steps, sum_seqPrefix]

/-- A scalar walk atom as the real mass of an offspring-sequence event. -/
theorem walk_event_real (μ : PMF ℕ) (n : ℕ) (z : ℤ) :
    (offspringSeqLaw μ).toMeasure.real {ω | walk ω n = z} = walkProb μ n z := by
  rw [walkProb, ite_eq_left (Int.natCast_nonneg n), Int.toNat_natCast]
  rw [← map_offspringSeqLaw_walk μ n]
  simp only [measureReal_def, Measure.map_apply (measurable_walk n)
    (measurableSet_singleton z)]
  rfl

/-- Bridge prefix mass:
`P(first m degrees = a, W_n = -1) = ∏μ(a_i) * P(W_{n-m} = -1 - W_m(a))`, for `m ≤ n`. -/
theorem bridgePrefix_mass (μ : PMF ℕ) {n m : ℕ} {a : List ℕ} (ham : a.length = m)
    (hmn : m ≤ n) :
    ((offspringSeqLaw μ).toMeasure).real {ω | seqPrefix m ω = a ∧ walk ω n = -1} =
      degreeWeight μ a * walkProb μ ((n - m : ℕ) : ℤ) (-1 - prefixWalk a) := by
  have heq : {ω | seqPrefix m ω = a ∧ walk ω n = -1} =
      {ω | seqPrefix m ω = a} ∩
        shiftSeq m ⁻¹' {η | walk η (n - m) = -1 - prefixWalk a} := by
    ext ω
    change (seqPrefix m ω = a ∧ walk ω n = -1) ↔
      (seqPrefix m ω = a ∧ walk (shiftSeq m ω) (n - m) = -1 - prefixWalk a)
    have hw (ha : seqPrefix m ω = a) : walk ω m = prefixWalk a := by
      rw [← prefixWalk_seqPrefix m ω, ha]
    constructor
    · rintro ⟨ha, hn⟩
      refine ⟨ha, ?_⟩
      rw [walk_shiftSeq, Nat.add_sub_of_le hmn, hn, hw ha]
    · rintro ⟨ha, hn⟩
      have h := walk_shiftSeq ω m (n - m)
      rw [Nat.add_sub_of_le hmn, hw ha, hn] at h
      exact ⟨ha, by omega⟩
  rw [heq]
  have hm := seqPrefix_inter_shift_mass μ a (A := {η | walk η (n - m) =
    -1 - prefixWalk a}) (measurableSet_eq_fun (measurable_walk _) measurable_const)
  rw [ham] at hm
  change ((offspringSeqLaw μ).toMeasure (_)).toReal = _
  rw [hm, ENNReal.toReal_mul]
  change degreeWeight μ a * (offspringSeqLaw μ).toMeasure.real _ = _
  rw [walk_event_real]

/-- Conditional on `W_n = -1`, the prefix mass is `∏μ(a_i)` times the bridge-prefix density
(positive denominator). -/
theorem bridgePrefix_cond_mass (μ : PMF ℕ) {n m : ℕ} {a : List ℕ} (ham : a.length = m)
    (hmn : m ≤ n) (hpos : 0 < walkProb μ n (-1)) :
    (((offspringSeqLaw μ).toMeasure)[|{ω | walk ω n = -1}]).real
        {ω | seqPrefix m ω = a} =
      degreeWeight μ a * bridgePrefixDensity μ n m (prefixWalk a) := by
  have hp : MeasurableSet {ω | seqPrefix m ω = a} :=
    (measurable_seqPrefix m) (measurableSet_singleton a)
  rw [measureReal_def, cond_apply' hp, ENNReal.toReal_mul, ENNReal.toReal_inv]
  change ((offspringSeqLaw μ).toMeasure.real {ω | walk ω n = -1})⁻¹ *
    (offspringSeqLaw μ).toMeasure.real ({ω | walk ω n = -1} ∩
      {ω | seqPrefix m ω = a}) = _
  rw [walk_event_real, Set.inter_comm]
  change (walkProb μ n (-1))⁻¹ *
    (offspringSeqLaw μ).toMeasure.real {ω | seqPrefix m ω = a ∧ walk ω n = -1} = _
  rw [bridgePrefix_mass μ ham hmn, bridgePrefixDensity]
  field_simp [(ne_of_gt hpos)]

end BGW.StableTrees.DiscreteForest
