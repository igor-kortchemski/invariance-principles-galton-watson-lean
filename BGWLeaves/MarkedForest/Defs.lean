module

public import BGW.Tree.DegreeCount
public import BGW.LocallyFinite.ForestWalkLaw

/-!
# Leaf-marked forests: definitions

Source: arXiv:1110.2163v4, `largetrees_final.tex`, Section 1.3 (`eq:kemperman`) and
Proposition 1.6 (`prop:K`, `eq:LambdaUtile`), step 3 of the proof.

* `forestLeafCount ts` is the number of leaves (vertices without children) of the ordered forest
  `ts`, the sum over its trees of the number of vertices of outdegree `0`.
* `forestLeafWeight w j p n` is the total weight `F_w(j, p, n)` of the ordered forests with `j`
  trees, `p` vertices and `n` leaves, the weight of a forest being the product over its vertices
  of `w` evaluated at their outdegrees.
* `leafMarkedForestBridges j p n` is the set of offspring-count vectors `ω : Fin p → ℕ` with
  `∑ i, ω i + j = p` (the walk `∑ (ω i - 1)` ends at `-j`) and exactly `n` coordinates equal to
  `0` (exactly `n` steps equal to `-1`).
-/

@[expose] public section

namespace BGWLeaves

open BGW
open scoped ENNReal

/-- The number of leaves of an ordered forest: vertices of outdegree `0`, over all its trees. -/
def forestLeafCount (ts : PlaneForest) : ℕ := (ts.map fun t => t.degreeCount 0).sum

/-- `F_w(j, p, n)`: the total weight of the ordered forests with `j` trees, `p` vertices in total
and `n` leaves in total. The weight of a forest is the product of the weights of its trees, and
the weight of a tree is the product of `w` over the outdegrees of its vertices. -/
noncomputable def forestLeafWeight (w : ℕ → ℝ≥0∞) (j p n : ℕ) : ℝ≥0∞ :=
  ∑' ts : PlaneForest,
    if ts.length = j ∧ PlaneForest.size ts = p ∧ forestLeafCount ts = n then
      (ts.map (PlaneTree.weight w)).prod
    else 0

/-- Offspring-count vectors `ω : Fin p → ℕ` with `∑ i, ω i + j = p` and exactly `n` coordinates
equal to `0`. -/
def leafMarkedForestBridges (j p n : ℕ) : Set (Fin p → ℕ) :=
  {ω | ∑ i, ω i + j = p ∧ (Finset.univ.filter fun i => ω i = 0).card = n}

end BGWLeaves
