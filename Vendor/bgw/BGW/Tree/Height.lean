/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.FringeWalk
import Mathlib.Data.List.Indexes
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card

/-!
# Discrete height and ancestral minima of the Łukasiewicz path

Height is the length of a valid DFS vertex address, with the root at index zero.
The path is the integer sum of increments strictly before its time index.
The finite-height domain excludes the terminal path time. A fringe occupies one
contiguous address block, and its path first falls below its starting value at
the end of that block.

These are the discrete conventions used in Le Gall, *Random trees and applications*,
Proposition 1.2, and in the height/Łukasiewicz definitions of Kortchemski,
*A simple proof of Duquesne's theorem on contour processes of conditioned
Galton–Watson trees*, Section 1.1 (local source lines 424–445).
-/

@[expose] public section

namespace BGW.PlaneTree

/-- Height at an actual DFS vertex index; the terminal path index is excluded. -/
def height (t : PlaneTree) (i : Fin t.size) : ℕ :=
  (t.vertices[i.val]'(by simpa only [length_vertices] using i.isLt)).length

/-- Integer prefix sums of the DFS increments. This total function saturates after tree size. -/
def lukasiewicz (t : PlaneTree) (k : ℕ) : ℤ := (t.increments.take k).sum

private theorem prefix_of_flatten_lookup {α : Type*} {blocks : List (List α)}
    {out : List α} {u : α} {i : ℕ}
    (hblocks : ∀ c ∈ blocks, ∀ j, c[j]? = some u → out <+: c.drop j)
    (hi : blocks.flatten[i]? = some u) : out <+: blocks.flatten.drop i := by
  induction blocks generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
    simp only [List.flatten_cons] at hi ⊢
    by_cases hic : i < c.length
    · rw [List.getElem?_append_left hic] at hi
      rw [List.drop_append_of_le_length hic.le]
      exact (hblocks c List.mem_cons_self i hi).trans (List.prefix_append _ _)
    · have hci : c.length ≤ i := by omega
      rw [List.getElem?_append_right hci] at hi
      rw [List.drop_append, List.drop_eq_nil_of_le hci, List.nil_append]
      exact ih (fun d hd => hblocks d (List.mem_cons_of_mem c hd)) hi

/-- The reattached DFS addresses of a fringe form a contiguous block at its root index. -/
theorem vertices_fringe_prefix {t s : PlaneTree} {u : List ℕ} {i : ℕ}
    (hi : t.vertices[i]? = some u) (hs : t.fringe? u = some s) :
    (s.vertices.map (fun v => u ++ v)) <+: t.vertices.drop i := by
  induction t generalizing i u s with
  | node ts ih =>
    cases i with
    | zero =>
      have hu : [] = u := by simpa using hi
      subst u
      have ht : node ts = s := by simpa using hs
      subst s
      change (node ts).vertices.map id <+: (node ts).vertices
      simpa only [List.map_id] using List.prefix_refl (node ts).vertices
    | succ i =>
      rw [vertices_node, List.getElem?_cons_succ] at hi
      rw [vertices_node, List.drop_succ_cons]
      apply prefix_of_flatten_lookup ?_ hi
      intro c hc j hj
      obtain ⟨q, hq, rfl⟩ := List.mem_mapIdx.mp hc
      rw [List.getElem?_map] at hj
      obtain ⟨v, hjv, hveq⟩ := Option.map_eq_some_iff.mp hj
      subst u
      have hsub : fringe? ts[q] v = some s := by simpa [hq] using hs
      have hp := ih _ (List.getElem_mem hq) hjv hsub
      have hm := hp.map (List.cons q)
      simpa only [List.map_map, Function.comp_def, List.cons_append, List.map_drop] using hm

private theorem getElem?_eq_of_prefix {α : Type*} {xs ys : List α}
    (hp : xs <+: ys) {k : ℕ} (hk : k < xs.length) : xs[k]? = ys[k]? := by
  obtain ⟨rest, rfl⟩ := hp
  exact (List.getElem?_append_left hk).symm

/-- An address is a descendant exactly when its DFS index lies in the fringe block. -/
theorem isPrefix_iff_dfs_in_fringe {t s : PlaneTree} {u v : List ℕ} {j i : ℕ}
    (hj : t.vertices[j]? = some u) (hi : t.vertices[i]? = some v)
    (hs : t.fringe? u = some s) :
    u <+: v ↔ j ≤ i ∧ i < j + s.size := by
  have hp := vertices_fringe_prefix hj hs
  constructor
  · rintro ⟨w, rfl⟩
    have hw : s.IsVertex w := by
      obtain ⟨r, hr⟩ := (mem_vertices_iff t (u ++ w)).mp (List.mem_of_getElem? hi)
      exact ⟨r, by simpa only [fringe?_append, hs, Option.bind_some] using hr⟩
    have hm : u ++ w ∈ s.vertices.map (fun v => u ++ v) :=
      List.mem_map_of_mem ((mem_vertices_iff s w).mpr hw)
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hm
    have hkl := (List.getElem?_eq_some_iff.mp hk).1
    have hlookup := (getElem?_eq_of_prefix hp hkl).symm.trans hk
    rw [List.getElem?_drop] at hlookup
    have heq : i = j + k := (nodup_vertices t).eq_of_getElem?_eq
      (List.getElem?_eq_some_iff.mp hi).1 (hi.trans hlookup.symm)
    simp only [List.length_map, length_vertices] at hkl
    omega
  · rintro ⟨hji, hiend⟩
    have hk : i - j < (s.vertices.map (fun v => u ++ v)).length := by
      simp only [List.length_map, length_vertices]
      omega
    have hlookup : (s.vertices.map (fun w => u ++ w))[i - j]? = some v := by
      rw [getElem?_eq_of_prefix hp hk, List.getElem?_drop, Nat.add_sub_of_le hji, hi]
    obtain ⟨w, _, hw⟩ := List.mem_map.mp (List.mem_of_getElem? hlookup)
    exact ⟨w, hw⟩

/-- The complete fringe block ends no later than the tree's terminal path time. -/
theorem fringe_end_le_size {t s : PlaneTree} {u : List ℕ} {i : ℕ}
    (hi : t.vertices[i]? = some u) (hs : t.fringe? u = some s) : i + s.size ≤ t.size := by
  have hp := (increments_fringe_prefix hi hs).length_le
  simp only [length_increments, List.length_drop] at hp
  have hi' := (List.getElem?_eq_some_iff.mp hi).1
  rw [length_vertices] at hi'
  omega

private theorem take_drop_increments_fringe {t s : PlaneTree} {u : List ℕ} {i k : ℕ}
    (hi : t.vertices[i]? = some u) (hs : t.fringe? u = some s) (hk : k ≤ s.size) :
    (t.increments.drop i).take k = s.increments.take k := by
  obtain ⟨rest, hrest⟩ := increments_fringe_prefix hi hs
  rw [← hrest, List.take_append_of_le_length (by simpa only [length_increments] using hk)]

private theorem lukasiewicz_add (t : PlaneTree) (i k : ℕ) :
    t.lukasiewicz (i + k) = t.lukasiewicz i + ((t.increments.drop i).take k).sum := by
  simp only [lukasiewicz, List.take_add, List.sum_append]

/-- At the end of a fringe block, the path is one below its value at the fringe root. -/
theorem lukasiewicz_fringe_end {t s : PlaneTree} {u : List ℕ} {i : ℕ}
    (hi : t.vertices[i]? = some u) (hs : t.fringe? u = some s) :
    t.lukasiewicz (i + s.size) = t.lukasiewicz i - 1 := by
  have htake := take_drop_increments_fringe hi hs (Nat.le_refl s.size)
  have hslen : s.increments.take s.size = s.increments := by simp
  rw [hslen] at htake
  rw [lukasiewicz_add, htake, sum_increments]
  omega

/-- Before the fringe ends, every path value is at least its value at the fringe root. -/
theorem lukasiewicz_ge_at_fringe {t s : PlaneTree} {u : List ℕ} {i k : ℕ}
    (hi : t.vertices[i]? = some u) (hs : t.fringe? u = some s)
    (hik : i ≤ k) (hk : k < i + s.size) : t.lukasiewicz i ≤ t.lukasiewicz k := by
  have hlocal : k - i < s.size := by omega
  have hnonneg := sum_take_increments_nonneg s
    (i := k - i) (by simpa only [length_increments] using hlocal)
  have hsplit := lukasiewicz_add t i (k - i)
  rw [Nat.add_sub_of_le hik, take_drop_increments_fringe hi hs hlocal.le] at hsplit
  omega

/-- The weak running-minimum condition stops exactly at the end of the fringe block. -/
theorem lukasiewicz_recordMin_iff_before_fringe_end {t s : PlaneTree} {u : List ℕ}
    {j i : ℕ} (hj : t.vertices[j]? = some u) (hs : t.fringe? u = some s) (_hji : j ≤ i) :
    (∀ k, j ≤ k → k ≤ i → t.lukasiewicz j ≤ t.lukasiewicz k) ↔ i < j + s.size := by
  constructor
  · intro h
    by_contra hi
    have hend := h (j + s.size) (by omega) (by omega)
    rw [lukasiewicz_fringe_end hj hs] at hend
    omega
  · intro hi k hjk hki
    exact lukasiewicz_ge_at_fringe hj hs hjk (by omega)

/-- Among preceding vertices, ancestry is exactly a weak running-minimum condition.
The interval includes both the candidate ancestor and the target vertex. -/
theorem isPrefix_iff_lukasiewicz_recordMin {t : PlaneTree} {u v : List ℕ} {j i : ℕ}
    (hj : t.vertices[j]? = some v) (hi : t.vertices[i]? = some u) (hji : j ≤ i) :
    v <+: u ↔ ∀ k, j ≤ k → k ≤ i → t.lukasiewicz j ≤ t.lukasiewicz k := by
  obtain ⟨s, hs⟩ := (mem_vertices_iff t v).mp (List.mem_of_getElem? hj)
  rw [isPrefix_iff_dfs_in_fringe hj hi hs,
    lukasiewicz_recordMin_iff_before_fringe_end hj hs hji]
  exact and_iff_right hji

open scoped Classical in
/-- The length of a DFS address counts the strict preceding weak record minima.
The target index itself is excluded from the count and included in each tested interval. -/
theorem length_eq_card_recordMin_of_getElem?_vertices {t : PlaneTree} {u : List ℕ} {i : ℕ}
    (hi : t.vertices[i]? = some u) :
    u.length = ((Finset.range i).filter
      (fun j => ∀ k, j ≤ k → k ≤ i → t.lukasiewicz j ≤ t.lukasiewicz k)).card := by
  let S := (Finset.range i).filter
    (fun j => ∀ k, j ≤ k → k ≤ i → t.lukasiewicz j ≤ t.lukasiewicz k)
  have hi' := (List.getElem?_eq_some_iff.mp hi).1
  have hmem (j : ℕ) (hj : j ∈ S) :
      j < i ∧ ∀ k, j ≤ k → k ≤ i → t.lukasiewicz j ≤ t.lukasiewicz k := by
    simpa only [S, Finset.mem_filter, Finset.mem_range] using hj
  have hbound (j : ℕ) (hj : j ∈ S) : j < t.vertices.length :=
    lt_trans (hmem j hj).1 hi'
  let f (j : ℕ) (hj : j ∈ S) : ℕ := (t.vertices[j]'(hbound j hj)).length
  have hp (j : ℕ) (hj : j ∈ S) : t.vertices[j]'(hbound j hj) <+: u :=
    (isPrefix_iff_lukasiewicz_recordMin
      (List.getElem?_eq_getElem (hbound j hj)) hi (hmem j hj).1.le).mpr (hmem j hj).2
  have hcard : S.card = (Finset.range u.length).card := by
    apply Finset.card_bij f
    · intro j hj
      apply Finset.mem_range.mpr
      change (t.vertices[j]'(hbound j hj)).length < u.length
      have hle := (hp j hj).length_le
      have hne : (t.vertices[j]'(hbound j hj)).length ≠ u.length := by
        intro heq
        have hv := (hp j hj).eq_of_length heq
        have hidx : j = i := (nodup_vertices t).eq_of_getElem?_eq (hbound j hj) (by
          rw [List.getElem?_eq_getElem (hbound j hj), hv, hi])
        exact (Nat.ne_of_lt (hmem j hj).1) hidx
      omega
    · intro j hj k hk heq
      apply (nodup_vertices t).eq_of_getElem_eq (hbound j hj) (hbound k hk)
      change (t.vertices[j]'(hbound j hj)).length =
        (t.vertices[k]'(hbound k hk)).length at heq
      calc
        t.vertices[j]'(hbound j hj) = u.take (t.vertices[j]'(hbound j hj)).length :=
          List.prefix_iff_eq_take.mp (hp j hj)
        _ = u.take (t.vertices[k]'(hbound k hk)).length := by rw [heq]
        _ = t.vertices[k]'(hbound k hk) := (List.prefix_iff_eq_take.mp (hp k hk)).symm
    · intro h hh
      have hh' : h < u.length := Finset.mem_range.mp hh
      have hu : t.IsVertex u := (mem_vertices_iff t u).mp (List.mem_of_getElem? hi)
      have hpresent : t.IsVertex (u.take h) := by
        apply IsVertex.prefix (v := u.drop h)
        simpa only [List.take_append_drop] using hu
      obtain ⟨j, hj⟩ := List.getElem?_of_mem ((mem_vertices_iff t (u.take h)).mpr hpresent)
      obtain ⟨s, hs⟩ := hpresent
      have hprefix : u.take h <+: u := List.take_prefix h u
      have hjle := ((isPrefix_iff_dfs_in_fringe hj hi hs).mp hprefix).1
      have hjne : j ≠ i := by
        intro heq
        subst j
        have heqaddr : u.take h = u := Option.some.inj (hj.symm.trans hi)
        have hlen := congrArg List.length heqaddr
        rw [List.length_take_of_le hh'.le] at hlen
        omega
      have hjlt : j < i := by omega
      have hjS : j ∈ S := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_range.mpr hjlt,
          (isPrefix_iff_lukasiewicz_recordMin hj hi hjle).mp hprefix⟩
      refine ⟨j, hjS, ?_⟩
      change (t.vertices[j]'(hbound j hjS)).length = h
      have hvj : t.vertices[j]'(hbound j hjS) = u.take h :=
        (List.getElem?_eq_some_iff.mp hj).2
      rw [hvj, List.length_take_of_le hh'.le]
  simpa only [S, Finset.card_range] using hcard.symm

open scoped Classical in
/-- The discrete height process is recovered from the Łukasiewicz path by counting ancestors. -/
theorem height_eq_card_recordMin (t : PlaneTree) (i : Fin t.size) :
    t.height i = ((Finset.range i.val).filter
      (fun j => ∀ k, j ≤ k → k ≤ i.val → t.lukasiewicz j ≤ t.lukasiewicz k)).card := by
  exact length_eq_card_recordMin_of_getElem?_vertices
    (List.getElem?_eq_getElem (by simpa only [length_vertices] using i.isLt))

end BGW.PlaneTree
