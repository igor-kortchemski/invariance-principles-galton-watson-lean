/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree

import Mathlib.Data.List.Indexes
import Mathlib.Data.List.Nodup

/-!
# Vertex addresses in depth-first order

The root address is `[]`. Each child contributes its vertex addresses prefixed
by its zero-based child index. Thus equal child subtrees still contribute
distinct vertex occurrences.

The depth of an address is its list length. For valid vertices, prefix ancestry
includes equality; strict ancestry uses a proper prefix. The parent of a
nonempty vertex address is obtained with `List.dropLast`.
-/

@[expose] public section

namespace BGW.PlaneTree

/-- All vertex addresses, listed in root-first depth-first order. -/
def vertices : PlaneTree → List (List ℕ) :=
  fold fun vs => [] :: (vs.mapIdx (fun i v => v.map (fun u => i :: u))).flatten

@[simp] theorem vertices_node (ts : List PlaneTree) :
    (node ts).vertices =
      [] :: (ts.mapIdx (fun i t => t.vertices.map (fun u => i :: u))).flatten := by
  simp only [vertices, fold_node, List.mapIdx_eq_ofFn, List.length_map, List.get_eq_getElem,
    List.getElem_map]
  rfl

@[simp] theorem vertices_leaf : leaf.vertices = [[]] := by simp [leaf]

/-- The enumeration contains exactly the addresses at which fringe lookup succeeds. -/
theorem mem_vertices_iff (t : PlaneTree) (u : List ℕ) :
    u ∈ t.vertices ↔ t.IsVertex u := by
  induction t generalizing u with
  | node ts ih =>
    cases u with
    | nil => simp [IsVertex]
    | cons i u =>
      simp only [vertices_node, List.mem_cons, reduceCtorEq, false_or, List.mem_flatten,
        List.mem_mapIdx, IsVertex, fringe?_node_cons]
      constructor
      · rintro ⟨_, ⟨j, hj, rfl⟩, hmem⟩
        obtain ⟨v, hv, heq⟩ := List.mem_map.mp hmem
        obtain ⟨rfl, rfl⟩ := List.cons.inj heq
        obtain ⟨s, hs⟩ := (ih _ (List.getElem_mem hj) v).mp hv
        exact ⟨s, by simpa [hj] using hs⟩
      · rintro ⟨s, hs⟩
        by_cases hi : i < ts.length
        · have hsub : IsVertex ts[i] u := ⟨s, by simpa [hi] using hs⟩
          exact ⟨_, ⟨i, hi, rfl⟩, List.mem_map_of_mem ((ih _ (List.getElem_mem hi) u).mpr hsub)⟩
        · simp [hi] at hs

/-- The address enumeration has one entry for each vertex counted by `size`. -/
@[simp] theorem length_vertices (t : PlaneTree) : t.vertices.length = t.size := by
  induction t with
  | node ts ih =>
    have hmap : (ts.mapIdx (fun i t => t.vertices.map (fun u => i :: u))).map List.length =
        ts.map size := by
      apply List.ext_getElem (by simp)
      intro j _ hj
      simp [ih _ (List.getElem_mem (by simpa using hj))]
    rw [vertices_node, size_node, List.length_cons, List.length_flatten, hmap, Nat.add_comm]

/-- Each vertex address occurs exactly once, including when subtrees are equal. -/
theorem nodup_vertices (t : PlaneTree) : t.vertices.Nodup := by
  induction t with
  | node ts ih =>
    rw [vertices_node, List.nodup_cons]
    constructor
    · intro h
      obtain ⟨_, hblock, hmem⟩ := List.mem_flatten.mp h
      obtain ⟨i, _, rfl⟩ := List.mem_mapIdx.mp hblock
      obtain ⟨u, _, heq⟩ := List.mem_map.mp hmem
      cases heq
    · rw [List.nodup_flatten]
      constructor
      · intro block hblock
        obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hblock
        exact List.Nodup.map (fun _ _ h => (List.cons.inj h).2) (ih _ (List.getElem_mem hi))
      · rw [List.pairwise_iff_getElem]
        intro i j _ _ hij
        apply List.disjoint_left.mpr
        intro u hu hv
        simp only [List.getElem_mapIdx] at hu hv
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hu
        obtain ⟨b, _, hb⟩ := List.mem_map.mp hv
        exact (ne_of_lt hij) (List.cons.inj hb).1.symm

/-- The number of vertices at depth `h`, with the root at depth zero. -/
def generationSize (t : PlaneTree) (h : ℕ) : ℕ :=
  t.vertices.countP (fun u => decide (u.length = h))

@[simp] theorem generationSize_zero (t : PlaneTree) : t.generationSize 0 = 1 := by
  cases t with
  | node ts =>
    simp [generationSize, List.mapIdx_eq_ofFn, List.countP_flatten, List.map_ofFn,
      Function.comp_def]

end BGW.PlaneTree
