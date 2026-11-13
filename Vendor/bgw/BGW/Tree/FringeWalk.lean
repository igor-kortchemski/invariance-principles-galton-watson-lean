/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.Excursion
public import BGW.Tree.Fringe
import Mathlib.Data.List.Rotate

/-!
# Fringe subtrees as contiguous DFS blocks

At the vertex in DFS position `i`, the fringe subtree occupies a contiguous block of the
increment word beginning at `i`. Rotating to this position and stopping at the first passage
to `-1` therefore recovers exactly that fringe subtree.

This is `eq:fringe` in Section 2.1 of Kortchemski–Vetter, *Rare subtree patterns in
size-conditioned Bienaymé trees* (source lines 691–696). The block induction adapts
`PoissonDeclumping/Lukasiewicz/Coding.lean`, `dfsSeq_fringeTrees_prefix`. Here the fringe is
identified by its actual address, and the decoder accepts an entire finite word; the bounded
prefix characterization does not claim that it accepts an untruncated rotation.
-/

@[expose] public section

namespace BGW.PlaneTree

private theorem map_fringe?_vertices_node (ts : List PlaneTree) :
    (node ts).vertices.map (fun u => (node ts).fringe? u) =
      some (node ts) :: (ts.map (fun t => t.vertices.map (fun u => t.fringe? u))).flatten := by
  simp only [vertices_node, List.map_cons, fringe?_nil, List.map_flatten]
  congr 2
  apply List.ext_getElem (by simp)
  intro j hj _
  have hj' : j < ts.length := by simpa using hj
  simp only [List.getElem_map, List.getElem_mapIdx, List.map_map]
  apply List.map_congr_left
  intro u _
  simp [hj']

private theorem forest_fringe_prefix {ts : List PlaneTree} {s : PlaneTree}
    (ih : ∀ t ∈ ts, ∀ i : ℕ,
      (t.vertices.map (fun u => t.fringe? u))[i]? = some (some s) →
        s.increments <+: t.increments.drop i)
    (i : ℕ)
    (h : ((ts.map (fun t => t.vertices.map (fun u => t.fringe? u))).flatten)[i]? =
      some (some s)) :
    s.increments <+: (ts.map increments).flatten.drop i := by
  induction ts generalizing i with
  | nil => simp at h
  | cons t ts ihl =>
    have hlen : t.increments.length = (t.vertices.map (fun u => t.fringe? u)).length := by
      simp
    simp only [List.map_cons, List.flatten_cons] at h ⊢
    by_cases hi : i < (t.vertices.map (fun u => t.fringe? u)).length
    · rw [List.getElem?_append_left hi] at h
      rw [List.drop_append_of_le_length (by omega)]
      exact (ih t (by simp) i h).trans (List.prefix_append _ _)
    · have hi' : (t.vertices.map (fun u => t.fringe? u)).length ≤ i := by omega
      rw [List.getElem?_append_right hi'] at h
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, hlen]
      exact ihl (fun r hr => ih r (by simp [hr])) _ h

private theorem increments_prefix_of_map_fringe_lookup (t s : PlaneTree) (i : ℕ)
    (h : (t.vertices.map (fun u => t.fringe? u))[i]? = some (some s)) :
    s.increments <+: t.increments.drop i := by
  induction t generalizing i with
  | node ts ih =>
    cases i with
    | zero =>
      have hs : node ts = s := by simpa [map_fringe?_vertices_node] using h
      subst s
      simp
    | succ i =>
      simp only [map_fringe?_vertices_node, List.getElem?_cons_succ] at h
      rw [increments_node, List.drop_succ_cons]
      exact forest_fringe_prefix ih i h

/-- The fringe at DFS index `i` occupies a contiguous block beginning at that index. -/
theorem increments_fringe_prefix {t s : PlaneTree} {u : List ℕ} {i : ℕ}
    (hi : t.vertices[i]? = some u) (hs : t.fringe? u = some s) :
    s.increments <+: t.increments.drop i := by
  apply increments_prefix_of_map_fringe_lookup
  rw [List.getElem?_map, hi]
  simp only [Option.map_some, hs]

/-- Rotating to a vertex and taking its fringe size gives exactly the fringe code.
Its total sum is `-1`, and every shorter prefix sum is nonnegative. -/
theorem take_rotate_increments_fringe {t s : PlaneTree} {u : List ℕ} {i : ℕ}
    (hi : t.vertices[i]? = some u) (hs : t.fringe? u = some s) :
    (t.increments.rotate i).take s.size = s.increments := by
  have hi' : i < t.size := by
    obtain ⟨hi', _⟩ := List.getElem?_eq_some_iff.mp hi
    simpa only [length_vertices] using hi'
  obtain ⟨rest, hrest⟩ := increments_fringe_prefix hi hs
  rw [List.rotate_eq_drop_append_take (by simpa only [length_increments] using hi'.le),
    ← hrest, List.append_assoc, ← length_increments s, List.take_append_length]

/-- The only accepted bounded prefix of a rotation is the complete fringe code at that vertex.
The bound on `m` prevents the saturation of `List.take` from giving longer apparent cut times. -/
theorem ofIncrements?_take_rotate_eq_some_iff {t s : PlaneTree} {u : List ℕ} {i m : ℕ}
    (hi : t.vertices[i]? = some u) (hm : m ≤ t.size) :
    ofIncrements? ((t.increments.rotate i).take m) = some s ↔
      t.fringe? u = some s ∧ m = s.size := by
  constructor
  · intro hparse
    obtain ⟨r, hr⟩ := (mem_vertices_iff t u).mp (List.mem_of_getElem? hi)
    have hcode := ofIncrements?_eq_some_iff.mp hparse
    have hsize : s.size = m := by
      have hlen := congrArg List.length hcode
      simpa only [length_increments, List.length_take, List.length_rotate, Nat.min_eq_left hm]
        using hlen
    have hblock := take_rotate_increments_fringe hi hr
    have hcut : m = r.size := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hp := sum_take_increments_nonneg r (i := m) (by simpa using hlt)
        have he : r.increments.take m = s.increments := by
          rw [← hblock, List.take_take, Nat.min_eq_left hlt.le, ← hcode]
        rw [he, sum_increments] at hp
        omega
      · have hp := sum_take_increments_nonneg s (i := r.size) (by simpa [hsize] using hgt)
        rw [hcode, List.take_take, Nat.min_eq_left hgt.le, hblock, sum_increments] at hp
        omega
    have hsr : s = r := increments_injective (by rw [hcode, hcut, hblock])
    subst r
    exact ⟨hr, hsize.symm⟩
  · rintro ⟨hs, rfl⟩
    rw [take_rotate_increments_fringe hi hs, ofIncrements?_increments]

end BGW.PlaneTree
