/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.Extinction
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Normalization for offspring laws of mean at most one

If the offspring law `μ` has mean `∫⁻ k, k ∂μ ≤ 1` and `μ {1} ≠ 1`, then `1` is the only fixed point
of the generating function in `[0, 1]` (`eq_one_of_offspringGF_eq`). Since the probability of
finiteness is such a fixed point (`isLeast_bienaymeLaw_finiteVertices`), it equals one: the tree is
almost surely finite, and the weights of the finite plane trees sum to one. The hypothesis
`μ {1} ≠ 1` is necessary: for `μ = dirac 1` the mean is one, `f s = s` for all `s`, and the
probability of finiteness is zero. The mean is the expectation `∫⁻ k, k ∂μ` in `[0, ∞]`; laws of
infinite mean and the supercritical classification are not treated here.
Adapted from `PoissonDeclumping/Bienayme/Normalization.lean`, where the mean is exactly one.
-/

@[expose] public section

namespace BGW.LocallyFinite

open MeasureTheory
open scoped ENNReal

/-- For mean at most one and `μ {1} ≠ 1`, the tree is finite with probability one. -/
theorem bienaymeLaw_finiteVertices_eq_one (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ ≤ 1) (hne : μ {1} ≠ 1) :
    bienaymeLaw μ {T | FiniteVertices T} = 1 := by
  rw [lintegral_countable'] at hm
  obtain ⟨hq1, hqfix⟩ := (isLeast_bienaymeLaw_finiteVertices μ).1
  exact eq_one_of_offspringGF_eq μ hm hne hq1 hqfix

/-- For mean at most one and `μ {1} ≠ 1`, the weights of the finite plane trees sum to one. -/
theorem tsum_weight_eq_one (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ ≤ 1) (hne : μ {1} ≠ 1) :
    ∑' t : PlaneTree, PlaneTree.weight (fun d => μ {d}) t = 1 := by
  rw [← bienaymeLaw_finiteVertices]
  exact bienaymeLaw_finiteVertices_eq_one μ hm hne

/-- For mean at most one and `μ {1} ≠ 1`, almost every tree has finitely many vertices. -/
theorem ae_finiteVertices_bienaymeLaw (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : ∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ ≤ 1) (hne : μ {1} ≠ 1) :
    ∀ᵐ T ∂bienaymeLaw μ, FiniteVertices T := by
  have h := bienaymeLaw_finiteVertices_eq_one μ hm hne
  rw [← prob_compl_eq_zero_iff measurableSet_finiteVertices] at h
  exact h

end BGW.LocallyFinite
