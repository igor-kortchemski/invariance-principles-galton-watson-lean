/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ForestLocalLimit

/-!
# Discrete forest mass adapters

The definitions of admissibility, forest masses, tails and prefix weights are
shared with the sealed periodic local-limit interface.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical

namespace BGW.StableTrees.DiscreteForest

/-- The series `∑ f_j` converges. -/
theorem summable_forestMass (μ : PMF ℕ) (j : ℕ) : Summable (fun r => forestMass μ j r) :=
  Scalar.summable_forestWeight_toReal μ j

/-- The shifted-sum form of `forestTail` agrees with the indicator form of K03. -/
theorem forestTail_eq_tsum_shift (μ : PMF ℕ) (j r : ℕ) (hs : Summable (forestMass μ j)) :
    forestTail μ j r = ∑' k, forestMass μ j (r + k) := by
  unfold forestTail
  rw [← (hs.indicator (Ici r)).sum_add_tsum_nat_add r]
  have hzero : ∑ k ∈ Finset.range r, (Ici r).indicator (forestMass μ j) k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    apply Set.indicator_of_notMem
    simpa only [Set.mem_Ici, not_le] using Finset.mem_range.mp hk
  rw [hzero, zero_add]
  apply tsum_congr
  intro k
  simp [Nat.add_comm]

/-- Admissibility is positivity of the forest weight `f_1 (n)`. -/
theorem admissible_iff_forestWeight_pos (μ : PMF ℕ) (n : ℕ) :
    Admissible μ n ↔ 0 < (BGW.forestWeight μ 1 n).toReal := by
  change Admissible μ n ↔ 0 < forestMass μ 1 n
  rw [forestMass_one_eq_sizeProb, measureReal_def, ENNReal.toReal_pos_iff]
  simp [Admissible, pos_iff_ne_zero]

/-- The tail mass is `G_1(n)` (infinite trees are null under criticality and `μ 1 ≠ 1`). -/
theorem tailMass_eq_forestTail (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    (BGW.LocallyFinite.bienaymeLaw μ.toMeasure (Attraction.sizeGeEvent n)).toReal =
      forestTail μ 1 n := (forestTail_one_eq_sizeGe hc hne n).symm

end BGW.StableTrees.DiscreteForest
