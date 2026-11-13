/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.DFS
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Degree-product weights of finite plane trees

For `p : ℕ → ℝ≥0∞` (in applications, the point masses of an offspring law), the weight of a
tree is the product of `p` over the outdegrees of all its vertices, each occurrence counted.
Nothing is assumed about `p`; in particular it need not be summable to one. For the point masses of
an offspring law the total weight of all finite trees is at most one (`tsum_weight_le_one`), and
equality is not claimed here. This follows `PoissonDeclumping/Bienayme/Basic.lean`.
-/

@[expose] public section

namespace BGW.PlaneTree

open scoped ENNReal BigOperators

/-- The product of `p` over the outdegrees of all vertices, with multiplicity. -/
noncomputable def weight (p : ℕ → ℝ≥0∞) (t : PlaneTree) : ℝ≥0∞ := (t.degrees.map p).prod

theorem weight_node (p : ℕ → ℝ≥0∞) (ts : List PlaneTree) :
    weight p (node ts) = p ts.length * (ts.map (weight p)).prod := by
  simp only [weight, degrees_node, List.map_cons, List.prod_cons]
  congr 1
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [List.map_cons, List.flatten_cons, List.map_append, List.prod_append, ih, List.map_cons,
      List.prod_cons]
    rfl

theorem weight_node_ofFn (p : ℕ → ℝ≥0∞) {k : ℕ} (f : Fin k → PlaneTree) :
    weight p (node (List.ofFn f)) = p k * ∏ i, weight p (f i) := by
  rw [weight_node, List.length_ofFn, List.map_ofFn, List.prod_ofFn]
  rfl

@[simp] theorem weight_leaf (p : ℕ → ℝ≥0∞) : weight p leaf = p 0 := by
  simp [leaf, weight_node]

/-- The weight vanishes exactly when some vertex has an outdegree of zero `p`-mass. -/
theorem weight_eq_zero_iff (p : ℕ → ℝ≥0∞) (t : PlaneTree) :
    weight p t = 0 ↔ ∃ d ∈ t.degrees, p d = 0 := by
  simp [weight, List.prod_eq_zero_iff]

theorem weight_ne_zero_iff (p : ℕ → ℝ≥0∞) (t : PlaneTree) :
    weight p t ≠ 0 ↔ ∀ d ∈ t.degrees, p d ≠ 0 := by
  rw [Ne, weight_eq_zero_iff]
  simp

end BGW.PlaneTree
