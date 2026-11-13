/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.Fringe
public import BGW.Tree.Vertices
public import Mathlib.Topology.MetricSpace.Defs
import Lean.Elab.Tactic.Omega

/-!
# Ancestors and graph distance on finite plane trees

The common ancestor of two addresses is their longest common prefix. The distance is the
sum of their depths minus twice that ancestor's depth. The definitions are total on addresses;
prefix closure ensures that the common ancestor of present vertices is present too.

`Vertex t` is only a name for the subtype of present addresses of `t`. Its metric is the real
cast of the natural distance. No metric or topology instance is introduced on all addresses,
and no separate graph representation is needed.
-/

@[expose] public section

namespace BGW.PlaneTree

/-- The longest common address prefix, with the root represented by the empty list. -/
def lca : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | _, [] => []
  | a :: u, b :: v => if a = b then a :: lca u v else []

@[simp] theorem lca_nil_left (u : List ℕ) : lca [] u = [] := rfl

@[simp] theorem lca_nil_right (u : List ℕ) : lca u [] = [] := by
  cases u <;> rfl

/-- An address is a prefix of the LCA exactly when it is a common prefix. -/
theorem prefix_lca_iff (w u v : List ℕ) :
    w <+: lca u v ↔ w <+: u ∧ w <+: v := by
  induction u generalizing w v with
  | nil =>
    simp only [lca_nil_left, List.prefix_nil]
    constructor
    · rintro rfl
      exact ⟨rfl, List.nil_prefix⟩
    · exact And.left
  | cons a u ih =>
    cases v with
    | nil =>
      simp only [lca_nil_right, List.prefix_nil]
      constructor
      · rintro rfl
        exact ⟨List.nil_prefix, rfl⟩
      · exact And.right
    | cons b v =>
      by_cases hab : a = b
      · subst b
        cases w with
        | nil => simp
        | cons c w =>
          change (c :: w <+: (if a = a then a :: lca u v else [])) ↔ _
          rw [ite_eq_left rfl]
          simp only [List.cons_prefix_cons]
          rw [ih]
          constructor
          · rintro ⟨hc, hu, hv⟩
            exact ⟨⟨hc, hu⟩, hc, hv⟩
          · rintro ⟨⟨hc, hu⟩, _, hv⟩
            exact ⟨hc, hu, hv⟩
      · cases w with
        | nil => simp
        | cons c w =>
          simp only [lca, ite_eq_right hab, List.prefix_nil, List.cons_ne_nil,
            false_iff, List.cons_prefix_cons]
          rintro ⟨⟨hca, _⟩, hcb, _⟩
          exact hab (hca.symm.trans hcb)

theorem lca_prefix_left (u v : List ℕ) : lca u v <+: u :=
  ((prefix_lca_iff (lca u v) u v).mp List.prefix_rfl).1

theorem lca_prefix_right (u v : List ℕ) : lca u v <+: v :=
  ((prefix_lca_iff (lca u v) u v).mp List.prefix_rfl).2

@[simp] theorem lca_self (u : List ℕ) : lca u u = u := by
  have h : u <+: lca u u := (prefix_lca_iff u u u).mpr ⟨List.prefix_rfl, List.prefix_rfl⟩
  exact (lca_prefix_left u u).eq_of_length_le h.length_le

theorem lca_comm (u v : List ℕ) : lca u v = lca v u := by
  have h : lca u v <+: lca v u :=
    (prefix_lca_iff _ _ _).mpr ⟨lca_prefix_right u v, lca_prefix_left u v⟩
  have h' : lca v u <+: lca u v :=
    (prefix_lca_iff _ _ _).mpr ⟨lca_prefix_right v u, lca_prefix_left v u⟩
  exact h.eq_of_length_le h'.length_le

theorem lca_eq_left_iff (u v : List ℕ) : lca u v = u ↔ u <+: v := by
  constructor
  · intro h
    rw [← h]
    exact lca_prefix_right u v
  · intro h
    have h' : u <+: lca u v := (prefix_lca_iff u u v).mpr ⟨List.prefix_rfl, h⟩
    exact (lca_prefix_left u v).eq_of_length_le h'.length_le

/-- The LCA of two present vertices remains a present vertex. -/
theorem isVertex_lca {t : PlaneTree} {u v : List ℕ}
    (hu : t.IsVertex u) (_hv : t.IsVertex v) : t.IsVertex (lca u v) := by
  obtain ⟨rest, hrest⟩ := lca_prefix_left u v
  rw [← hrest] at hu
  exact hu.prefix

/-- The natural parent-child distance between two addresses. -/
def graphDist (u v : List ℕ) : ℕ :=
  u.length + v.length - 2 * (lca u v).length

/-- The subtraction in `graphDist` never truncates a negative quantity. -/
theorem graphDist_add_two_lca (u v : List ℕ) :
    graphDist u v + 2 * (lca u v).length = u.length + v.length := by
  have hu := (lca_prefix_left u v).length_le
  have hv := (lca_prefix_right u v).length_le
  unfold graphDist
  omega

theorem graphDist_nonneg (u v : List ℕ) : 0 ≤ graphDist u v := Nat.zero_le _

@[simp] theorem graphDist_self (u : List ℕ) : graphDist u u = 0 := by
  rw [graphDist, lca_self]
  omega

theorem graphDist_comm (u v : List ℕ) : graphDist u v = graphDist v u := by
  unfold graphDist
  rw [lca_comm u v, Nat.add_comm]

@[simp] theorem graphDist_eq_zero_iff (u v : List ℕ) : graphDist u v = 0 ↔ u = v := by
  constructor
  · intro h
    have hd := graphDist_add_two_lca u v
    have hu := (lca_prefix_left u v).length_le
    have hv := (lca_prefix_right u v).length_le
    have heu : lca u v = u := (lca_prefix_left u v).eq_of_length (by omega)
    have hev : lca u v = v := (lca_prefix_right u v).eq_of_length (by omega)
    exact heu.symm.trans hev
  · rintro rfl
    exact graphDist_self u

theorem graphDist_triangle (u v w : List ℕ) :
    graphDist u w ≤ graphDist u v + graphDist v w := by
  have huv := graphDist_add_two_lca u v
  have hvw := graphDist_add_two_lca v w
  have huw := graphDist_add_two_lca u w
  rcases List.prefix_or_prefix_of_prefix (lca_prefix_right u v) (lca_prefix_left v w) with h | h
  · have hc : lca u v <+: lca u w :=
      (prefix_lca_iff _ _ _).mpr ⟨lca_prefix_left u v, h.trans (lca_prefix_right v w)⟩
    have hcl := hc.length_le
    have hv := (lca_prefix_left v w).length_le
    omega
  · have hc : lca v w <+: lca u w :=
      (prefix_lca_iff _ _ _).mpr ⟨h.trans (lca_prefix_left u v), lca_prefix_right v w⟩
    have hcl := hc.length_le
    have hv := (lca_prefix_right u v).length_le
    omega

@[simp] theorem graphDist_root (u : List ℕ) : graphDist [] u = u.length := by
  simp [graphDist]

/-- Every parent-child edge has unit length. -/
@[simp] theorem graphDist_append_singleton (u : List ℕ) (j : ℕ) :
    graphDist u (u ++ [j]) = 1 := by
  have hlca : lca u (u ++ [j]) = u :=
    (lca_eq_left_iff _ _).mpr (List.prefix_append _ _)
  simp only [graphDist, hlca, List.length_append, List.length_singleton]
  omega

/-- Removing the last address entry gives a present parent, with the root fixed. -/
theorem isVertex_dropLast {t : PlaneTree} {u : List ℕ} (hu : t.IsVertex u) :
    t.IsVertex u.dropLast := by
  obtain ⟨rest, hrest⟩ := List.dropLast_prefix u
  rw [← hrest] at hu
  exact hu.prefix

theorem graphDist_dropLast (u : List ℕ) (hu : u ≠ []) : graphDist u.dropLast u = 1 := by
  have hp : lca u.dropLast u = u.dropLast :=
    (lca_eq_left_iff _ _).mpr (List.dropLast_prefix u)
  have hpos : 0 < u.length := List.length_pos_iff.mpr hu
  simp only [graphDist, hp, List.length_dropLast]
  omega

/-- Present addresses of a fixed tree; this is a subtype, not a second tree representation. -/
def Vertex (t : PlaneTree) := {u : List ℕ // t.IsVertex u}

/-- The metric on vertices is the real cast of their natural parent-child distance. -/
noncomputable instance vertexMetricSpace (t : PlaneTree) : MetricSpace (Vertex t) where
  dist u v := (graphDist u.val v.val : ℝ)
  dist_self u := by simp only [graphDist_self, Nat.cast_zero]
  dist_comm u v := by rw [graphDist_comm]
  dist_triangle u v w := by
    have h : (graphDist u.val w.val : ℝ) ≤
        ((graphDist u.val v.val + graphDist v.val w.val : ℕ) : ℝ) :=
      Nat.cast_le.mpr (graphDist_triangle u.val v.val w.val)
    simpa only [Nat.cast_add] using h
  eq_of_dist_eq_zero h := by
    apply Subtype.ext
    exact (graphDist_eq_zero_iff _ _).mp (Nat.cast_eq_zero.mp h)

@[simp] theorem dist_vertex_eq_graphDist {t : PlaneTree} (u v : Vertex t) :
    dist u v = (graphDist u.val v.val : ℝ) := rfl

end BGW.PlaneTree
