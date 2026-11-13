/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Rational approximation in nonnegative reals

This module records the density of nonnegative rationals in `ℝ≥0` in the form used for
countable rational approximations of real-valued constructions.
-/

@[expose] public section

open scoped NNReal

namespace BGW.Probability

/-- Every strict inequality between nonnegative reals has a nonnegative rational strictly
between its endpoints. -/
theorem exists_nnrat_btwn {a b : ℝ≥0} (h : a < b) :
    ∃ q : ℚ≥0, a < (q : ℝ≥0) ∧ (q : ℝ≥0) < b := by
  obtain ⟨r, hr, ha, hb⟩ := (NNReal.lt_iff_exists_rat_btwn a b).1 h
  let q : ℚ≥0 := ⟨r, hr⟩
  have heq : (q : ℝ≥0) = Real.toNNReal (r : ℝ) := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (Rat.cast_nonneg.2 hr)]
    exact NNRat.cast_mk r hr
  exact ⟨q, heq.symm ▸ ha, heq.symm ▸ hb⟩

end BGW.Probability
