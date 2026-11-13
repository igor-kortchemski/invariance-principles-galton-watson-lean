/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Regularly varying sequences

This directory is a real-analysis toolbox about a monotone sequence `a : ℕ → ℝ`,
positive at every `n ≥ 1`, that is regularly varying of an index `ρ`.
For the scalar stable normalizers, the relevant index is `ρ = 1/α ∈ [1/2, 1)`.

The sequential form of regular variation used here is

  `a ⌊c n⌋ / a n → c ^ ρ` for every `c > 0`.


Adapted from `PoissonDeclumping/RegularVariation/Defs.lean` in
`igor-kortchemski/rare-subtree-patterns`, commit
`fc5ef722392b1af41e8b9d5fc45d5a521b7823dd` (Apache-2.0).
-/

@[expose] public section

open Filter
open scoped Topology

namespace BGW.StableTrees

/-- A real sequence `a` is regularly varying of index `ρ` (sequential form):
`a ⌊c n⌋₊ / a n → c ^ ρ` as `n → ∞`, for every `c > 0`. -/
def RegularlyVaryingSeq (ρ : ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → Tendsto (fun n : ℕ => a ⌊c * n⌋₊ / a n) atTop (𝓝 (c ^ ρ))

end BGW.StableTrees

