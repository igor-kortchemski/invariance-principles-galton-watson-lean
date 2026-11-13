/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.Weight
public import BGW.Tree.Excursion
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Walk weights of Łukasiewicz words

For step masses `p : ℕ → ℝ≥0∞`, the weight of an integer word `x₁, …, xₙ` with all `xᵢ ≥ -1` is
`∏ p (xᵢ + 1)`: the steps are `k - 1` for an offspring count `k`. The weight of a finite plane tree
is the walk weight of its increments (`walkWeight_increments`), and the total weight of the trees of
size `n` is the total walk weight of the tree excursions of length `n`
(`tsum_weight_size_eq_tsum_excursions`). No assumption is made on `p`. Adapted from
`PoissonDeclumping/Lukasiewicz/Excursion.lean` (`walkWeight`, `weight_eq_walkWeight`), where `p` is
a probability mass function and the excursions are defined through a first-passage time.
-/

@[expose] public section

namespace BGW

open scoped ENNReal

/-- The product of `p (x + 1)` over the entries of a word of steps `x ≥ -1`. An entry below `-1`
would silently contribute `p 0`; such words are never used, since excursions have all entries
at least `-1`. -/
noncomputable def walkWeight (p : ℕ → ℝ≥0∞) (xs : List ℤ) : ℝ≥0∞ :=
  (xs.map fun a => p (a + 1).toNat).prod

namespace PlaneTree

/-- The weight of a tree is the walk weight of its Łukasiewicz increments. -/
theorem walkWeight_increments (p : ℕ → ℝ≥0∞) (t : PlaneTree) :
    walkWeight p t.increments = weight p t := by
  have h : (fun a : ℤ => p (a + 1).toNat) ∘ (fun d : ℕ => (d : ℤ) - 1) = p := by
    funext d
    simp
  rw [walkWeight, weight, increments, List.map_map, h]

/-- Total weight of the trees of size `n` as a total walk weight of the excursions of length `n`. -/
theorem tsum_weight_size_eq_tsum_excursions (p : ℕ → ℝ≥0∞) (n : ℕ) :
    ∑' t : PlaneTree, (if t.size = n then weight p t else 0) =
      ∑' x : List ℤ,
        Set.indicator {x : List ℤ | IsTreeExcursion x ∧ x.length = n} (walkWeight p) x := by
  have hrange : Function.support
      (Set.indicator {x : List ℤ | IsTreeExcursion x ∧ x.length = n} (walkWeight p)) ⊆
        Set.range increments := by
    intro x hx
    by_contra hrange
    apply hx
    have hx' : x ∉ {x : List ℤ | IsTreeExcursion x ∧ x.length = n} := fun h =>
      hrange (by
        obtain ⟨t, ht, -⟩ := (isTreeExcursion_iff_existsUnique x).mp h.1
        exact ⟨t, ht⟩)
    exact Set.indicator_of_notMem hx' _
  rw [← increments_injective.tsum_eq hrange]
  refine tsum_congr fun t => ?_
  by_cases ht : t.size = n
  · have hmem : t.increments ∈ {x : List ℤ | IsTreeExcursion x ∧ x.length = n} :=
      ⟨isTreeExcursion_increments t, by rw [length_increments, ht]⟩
    rw [ite_eq_left ht, Set.indicator_of_mem hmem, walkWeight_increments]
  · have hmem : t.increments ∉ {x : List ℤ | IsTreeExcursion x ∧ x.length = n} := fun h =>
      ht (by rw [← length_increments]; exact h.2)
    rw [ite_eq_right ht, Set.indicator_of_notMem hmem]

end PlaneTree

end BGW
