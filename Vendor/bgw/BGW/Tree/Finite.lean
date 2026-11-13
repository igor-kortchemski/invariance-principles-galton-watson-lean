/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree
public import Mathlib.Data.Set.Finite.Basic

import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Set.Finite.List

/-!
# Finiteness of size classes

There are finitely many plane trees with a bounded number of vertices. The proof
uses the list of root-child subtrees: for a tree of size at most `n + 1`, there
are at most `n` children, each having size at most `n`.
-/

public section

namespace BGW.PlaneTree

/-- Only finitely many plane trees have at most `n` vertices. -/
theorem finite_size_le (n : ℕ) : {t : PlaneTree | t.size ≤ n}.Finite := by
  induction n with
  | zero =>
    apply Set.finite_empty.subset
    intro t ht
    have hp := size_pos t
    change t.size ≤ 0 at ht
    omega
  | succ n ih =>
    let Small := {t : PlaneTree // t.size ≤ n}
    let : Fintype Small := ih.fintype
    let assemble : List Small → PlaneTree := fun ts => node (ts.map Subtype.val)
    apply ((List.finite_length_le Small n).image assemble).subset
    intro t ht
    change t.size ≤ n + 1 at ht
    have hsum : (t.children.map size).sum ≤ n := by
      have hsize := size_node t.children
      rw [node_children] at hsize
      omega
    have hchildren : ∀ s ∈ t.children, s.size ≤ n := by
      intro s hs
      have hmem : s.size ∈ t.children.map size := List.mem_map_of_mem hs
      exact (List.le_sum_of_mem hmem).trans hsum
    have hlength : t.children.length ≤ n := by
      calc
        t.children.length = (t.children.map size).length := by simp
        _ ≤ (t.children.map size).sum := List.length_le_sum_of_one_le _ (by
          intro m hm
          obtain ⟨s, _, rfl⟩ := List.mem_map.mp hm
          exact Nat.succ_le_of_lt (size_pos s))
        _ ≤ n := hsum
    refine ⟨t.children.attachWith (fun s => s.size ≤ n) hchildren, ?_, ?_⟩
    · change (t.children.attachWith (fun s => s.size ≤ n) hchildren).length ≤ n
      rw [List.length_attachWith]
      exact hlength
    · dsimp only [assemble]
      rw [List.attachWith_map_subtype_val, node_children]

/-- Only finitely many plane trees have exactly `n` vertices. -/
theorem finite_size_eq (n : ℕ) : {t : PlaneTree | t.size = n}.Finite :=
  (finite_size_le n).subset fun _ ht => le_of_eq ht

end BGW.PlaneTree
