/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Defs
public import BGW.GeneratingFunction
import Mathlib.Tactic.Push

/-!
# Support of a nondegenerate critical offspring law

A critical probability mass function other than the point mass at one assigns
positive mass to zero and to some integer at least two. These scalar facts
supply the support assumptions used in lattice Fourier inversion.

Adapted from `PoissonDeclumping/Bienayme/Normalization.lean` in
`igor-kortchemski/rare-subtree-patterns`, commit
`fc5ef722392b1af41e8b9d5fc45d5a521b7823dd` (Apache-2.0).
The second proof reuses the generating-function theorem on measures already
available in `BGW.GeneratingFunction` through the PMF-to-measure map.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BGW.StableTrees

variable {μ : PMF ℕ}

/-- A critical law with `μ 1 ≠ 1` assigns positive mass to some `j ≥ 2`. -/
theorem IsCritical.exists_two_le_ne_zero (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∃ j, 2 ≤ j ∧ μ j ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  have hc' := hc
  rw [IsCritical, tsum_eq_single 1] at hc'
  · simpa using hc'
  · intro j hj
    rcases j with _ | _ | j
    · simp
    · exact absurd rfl hj
    · simp [h (j + 2) (by omega)]

/-- A critical law with `μ 1 ≠ 1` assigns positive mass to zero. -/
theorem IsCritical.apply_zero_ne_zero (hc : IsCritical μ) (hne : μ 1 ≠ 1) : μ 0 ≠ 0 := by
  intro h0
  have hm : ∑' j : ℕ, (j : ℝ≥0∞) * μ.toMeasure {j} = 1 := by
    simpa only [IsCritical,
      PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hc
  have hne' : μ.toMeasure {1} ≠ 1 := by
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hne
  have hfix : BGW.offspringGF μ.toMeasure 0 = 0 := by
    rw [BGW.offspringGF_zero, PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton _), h0]
  have h := BGW.eq_one_of_offspringGF_eq μ.toMeasure hm.le hne' zero_le hfix
  exact zero_ne_one h

end BGW.StableTrees
