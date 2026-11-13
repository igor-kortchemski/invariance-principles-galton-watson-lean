/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForest

/-!
# Discrete occupation and reversal

Finite-time reversal identifies the forest record count and the occupation count
with weak ascending records and reflected bands, with both endpoints retained.
The height scaling is `B n / n`, with constant exactly one.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

/-- The discrete occupation count at level `a`:
`#{j < k | ∀ l ∈ [j,k], W_j - W_l < a}`, i.e. `W_j - min_{[j,k]} W < a`.  -/
noncomputable def discreteCount (ω : ℕ → ℕ) (k : ℕ) (a : ℝ) : ℕ :=
  ((Finset.range k).filter
    (fun j => ∀ l, j ≤ l → l ≤ k → ((walk ω j : ℝ) - (walk ω l : ℝ)) < a)).card

/-- The discrete `ε`-occupation `(n ε)⁻¹ #{j < ⌊n t⌋ | W_j - min_{[j,⌊nt⌋]} W < ε B_n}`:
mesh `1/n`, level `ε B_n`; the discrete analogue of `heightApprox ε`. -/
noncomputable def discreteOccupation (B : ℕ → ℝ) (n : ℕ) (ε : ℝ) (ω : ℕ → ℕ) (t : ℝ≥0) : ℝ :=
  (1 / ((n : ℝ) * ε)) * (discreteCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ (ε * B n) : ℝ)

/-- The normalized discrete height `(B_n / n) · H_{⌊n t⌋}` (the constant is `1`, see the module
docstring; at `θ = 2` it converges to `X_t - I_t`). -/
noncomputable def scaledHeight (B : ℕ → ℝ) (n : ℕ) (ω : ℕ → ℕ) (t : ℝ≥0) : ℝ :=
  (B n / (n : ℝ)) * (forestHeight ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ)

/-- The sequence reversed at `k`: `i ↦ ω (k-1-i)` for `i < k`, unchanged afterwards. -/
def revSeq (k : ℕ) (ω : ℕ → ℕ) : ℕ → ℕ := fun i => if i < k then ω (k - 1 - i) else ω i

/-- The reflected gap `M_u - W_u` of the walk, `M_u = max_{v ≤ u} W_v` (an integer, `≥ 0`). -/
noncomputable def reflGap (ω : ℕ → ℕ) (u : ℕ) : ℤ :=
  (Finset.range (u + 1)).sup' ⟨0, by simp⟩ (walk ω) - walk ω u

/-- The number of weak ascending ladder epochs `u ∈ [1,k]` (`W_u ≥ W_v` for all `v ≤ u`). -/
noncomputable def weakLadderCount (ω : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.Icc 1 k).filter (fun u => reflGap ω u = 0)).card

/-- The number of times `u ∈ [1,k]` with reflected gap `< a`. -/
noncomputable def bandCount (ω : ℕ → ℕ) (k : ℕ) (a : ℝ) : ℕ :=
  ((Finset.Icc 1 k).filter (fun u => (reflGap ω u : ℝ) < a)).card

/-- One step of the walk: `W_{n+1} = W_n + ω_n - 1`. -/
theorem walk_succ_eq (ω : ℕ → ℕ) (n : ℕ) :
    walk ω (n + 1) = walk ω n + (ω n : ℤ) - 1 := by
  simp only [walk, Finset.sum_range_succ]
  ring

/-- Agreement of the first `n` offspring coordinates determines the walk through time `n`. -/
theorem walk_eq_of_agree {ω ξ : ℕ → ℕ} {n : ℕ}
    (he : ∀ i < n, ω i = ξ i) {u : ℕ} (hu : u ≤ n) : walk ω u = walk ξ u := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [he i (by have := Finset.mem_range.mp hi; omega)]

/-- Measurability of the discrete height and occupation. -/
theorem measurable_scaledHeight (B : ℕ → ℝ) (n : ℕ) (t : ℝ≥0) :
    Measurable (fun ω => scaledHeight B n ω t) := by
  exact measurable_const.mul ((measurable_of_countable (fun x : ℕ => (x : ℝ))).comp
    (measurable_forestHeight _))

/-- Each finite discrete occupation count is measurable. -/
theorem measurable_discreteCount (k : ℕ) (a : ℝ) :
    Measurable (fun ω => discreteCount ω k a) := by
  simp only [discreteCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.measurable_sum
  intro j _
  apply Measurable.ite _ measurable_const measurable_const
  have hm (j l : ℕ) : MeasurableSet
      {ω | ((walk ω j : ℝ) - (walk ω l : ℝ)) < a} :=
    measurableSet_lt
      (((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp (measurable_walk j)).sub
        ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp (measurable_walk l)))
      measurable_const
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun l => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => hm j l

/-- Every fixed-time discrete occupation is measurable. -/
theorem measurable_discreteOccupation (B : ℕ → ℝ) (n : ℕ) (ε : ℝ) (t : ℝ≥0) :
    Measurable (fun ω => discreteOccupation B n ε ω t) := by
  exact measurable_const.mul ((measurable_of_countable (fun x : ℕ => (x : ℝ))).comp
    (measurable_discreteCount _ _))

end BGW.StableTrees.DiscreteHeightApprox
