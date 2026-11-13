/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Logic.Encodable.Basic

import BGW.Probability.ConvergenceInMeasure

/-!
# Diagonal extraction for predicates on subsequences

Nested extractions have a strictly increasing diagonal. Its tail lies in the range of
each fixed stage, so every predicate stable under eventual subsequences holds on the diagonal.
The predicates may concern unrelated probability spaces.
-/

@[expose] public section

namespace BGW.StableTrees

/-- A limit along one increasing subsequence is inherited by every increasing sequence
whose tail lies in its range. -/
theorem tendsto_comp_of_eventual_subseq {α : Type*} {u : ℕ → α} {l : Filter α}
    {φ ψ : ℕ → ℕ} (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hsub : ∃ N, ∀ k ≥ N, ∃ j, ψ k = φ j)
    (hu : Filter.Tendsto (u ∘ φ) Filter.atTop l) :
    Filter.Tendsto (u ∘ ψ) Filter.atTop l := by
  obtain ⟨N, hN⟩ := hsub
  rw [Filter.tendsto_def] at hu ⊢
  intro A hA
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (hu A hA)
  filter_upwards [Filter.eventually_ge_atTop N,
    hψ.tendsto_atTop.eventually_ge_atTop (φ M)] with k hk hkg
  obtain ⟨j, hj⟩ := hN k hk
  have hMj : M ≤ j := hφ.le_iff_le.mp (hj ▸ hkg)
  change u (ψ k) ∈ A
  rw [hj]
  exact hM j hMj

end BGW.StableTrees
