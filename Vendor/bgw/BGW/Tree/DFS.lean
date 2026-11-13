/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.Vertices

/-!
# Depth-first degree sequences

The degree sequence visits the root first, then each child subtree in its child
order. Subtracting one in `ℤ` gives the Łukasiewicz increments: their sum is
`-1`, and each strict prefix has nonnegative sum.

This is the forward coding direction used in Section 2 of Kortchemski–Vetter,
*Rare subtree patterns in size-conditioned Bienaymé trees*. Reconstruction and
the identification of fringe segments are separate results.
-/

@[expose] public section

namespace BGW.PlaneTree

/-- Outdegrees in root-first depth-first order, counting every vertex occurrence. -/
def degrees : PlaneTree → List ℕ := fold fun ds => ds.length :: ds.flatten

@[simp] theorem degrees_node (ts : List PlaneTree) :
    (node ts).degrees = ts.length :: (ts.map degrees).flatten := by
  simp only [degrees, fold_node, List.length_map]

@[simp] theorem length_degrees (t : PlaneTree) : t.degrees.length = t.size := by
  induction t with
  | node ts ih =>
    have hmap : ts.map (fun s => s.degrees.length) = ts.map size :=
      List.map_congr_left ih
    rw [degrees_node, List.length_cons, List.length_flatten, List.map_map, size_node]
    change (ts.map (fun s => s.degrees.length)).sum + 1 = 1 + (ts.map size).sum
    rw [hmap]
    omega

/-- The sum of all outdegrees is one less than the number of vertices. -/
theorem sum_degrees_add_one (t : PlaneTree) : t.degrees.sum + 1 = t.size := by
  induction t with
  | node ts ih =>
    have hmap : ts.map (fun s => s.degrees.sum + 1) = ts.map size :=
      List.map_congr_left ih
    have hsum := congrArg List.sum hmap
    simp only [List.sum_map_add, List.map_const', List.sum_const_nat, Nat.mul_one] at hsum
    rw [degrees_node, List.sum_cons, List.sum_flatten, List.map_map, size_node]
    change ts.length + (ts.map (fun s => s.degrees.sum)).sum + 1 =
      1 + (ts.map size).sum
    omega

/-- Integer Łukasiewicz increments; subtraction is not truncated at zero. -/
def increments (t : PlaneTree) : List ℤ :=
  t.degrees.map (fun (d : ℕ) => (d : ℤ) - 1)

@[simp] theorem increments_node (ts : List PlaneTree) :
    (node ts).increments = ((ts.length : ℤ) - 1) :: (ts.map increments).flatten := by
  simp only [increments, degrees_node, List.map_cons, List.map_flatten, List.map_map,
    Function.comp_def]
  rfl

@[simp] theorem length_increments (t : PlaneTree) : t.increments.length = t.size := by
  simp [increments]

private theorem sum_degree_increments (ds : List ℕ) :
    (ds.map (fun (d : ℕ) => (d : ℤ) - 1)).sum = (ds.sum : ℤ) - (ds.length : ℤ) := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Int.natCast_add,
      Int.natCast_one, ih]
    omega

/-- The Łukasiewicz path ends at `-1`. -/
theorem sum_increments (t : PlaneTree) : t.increments.sum = -1 := by
  rw [increments, sum_degree_increments, length_degrees]
  have h := sum_degrees_add_one t
  omega

theorem neg_one_le_increment (t : PlaneTree) {x : ℤ} (hx : x ∈ t.increments) :
    -1 ≤ x := by
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
  omega

private theorem sum_take_flatten_lower_bound (blocks : List (List ℤ)) :
    (∀ b ∈ blocks, b.sum = -1 ∧ ∀ i < b.length, 0 ≤ (b.take i).sum) →
    ∀ i, i < blocks.flatten.length →
      1 - (blocks.length : ℤ) ≤ (blocks.flatten.take i).sum := by
  induction blocks with
  | nil =>
    intro _ i hi
    simp at hi
  | cons b blocks ih =>
    intro h i hi
    have hb := h b (by simp)
    have htail : ∀ c ∈ blocks, c.sum = -1 ∧ ∀ j < c.length, 0 ≤ (c.take j).sum := by
      intro c hc
      exact h c (by simp [hc])
    simp only [List.flatten_cons, List.length_append] at hi
    by_cases hib : i < b.length
    · rw [List.flatten_cons, List.take_append_of_le_length (Nat.le_of_lt hib)]
      have hp := hb.2 i hib
      simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
      omega
    · have hbi : b.length ≤ i := by omega
      have hit : i - b.length < blocks.flatten.length := by omega
      have ht := ih htail (i - b.length) hit
      rw [List.flatten_cons, List.take_append, List.take_of_length_le hbi,
        List.sum_append, hb.1]
      simp only [List.length_cons, Int.natCast_add, Int.natCast_one]
      omega

/-- Before its final increment, the Łukasiewicz path stays nonnegative. -/
theorem sum_take_increments_nonneg (t : PlaneTree) {i : ℕ}
    (hi : i < t.increments.length) : 0 ≤ (t.increments.take i).sum := by
  induction t generalizing i with
  | node ts ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hblocks : ∀ b ∈ ts.map increments,
          b.sum = -1 ∧ ∀ j < b.length, 0 ≤ (b.take j).sum := by
        intro b hb
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hb
        exact ⟨sum_increments s, fun j hj => ih s hs hj⟩
      simp only [increments_node, List.length_cons] at hi
      have hi' : i < (ts.map increments).flatten.length := by omega
      have hp := sum_take_flatten_lower_bound (ts.map increments) hblocks i hi'
      simp only [List.length_map] at hp
      rw [increments_node, List.take_succ_cons, List.sum_cons]
      omega

/-- The recursive degree sequence agrees with fringe lookup at the actual DFS addresses.
The `Option` codomain avoids assigning an artificial degree to an invalid address. -/
theorem map_fringe?_vertices_rootDegree (t : PlaneTree) :
    t.vertices.map (fun u => (t.fringe? u).map rootDegree) = t.degrees.map some := by
  induction t with
  | node ts ih =>
    simp only [vertices_node, degrees_node, List.map_cons, fringe?_nil, Option.map_some,
      rootDegree_node, List.map_flatten]
    congr 2
    apply List.ext_getElem (by simp)
    intro j hj _
    have hj' : j < ts.length := by simpa using hj
    simp only [List.getElem_map, List.getElem_mapIdx, List.map_map, Function.comp_apply]
    rw [← ih _ (List.getElem_mem hj')]
    apply List.map_congr_left
    intro u _
    simp [hj']

end BGW.PlaneTree

namespace BGW.PlaneForest

/-- Total number of vertices in a finite ordered forest. -/
def size (ts : PlaneForest) : ℕ := (ts.map PlaneTree.size).sum

/-- Concatenate the depth-first increment sequences in component order. -/
def increments (ts : PlaneForest) : List ℤ := (ts.map PlaneTree.increments).flatten

@[simp] theorem length_increments (ts : PlaneForest) :
    (increments ts).length = size ts := by
  simp [increments, size, List.map_map, Function.comp_def]

/-- Each component contributes one net downward step, including the empty forest. -/
theorem sum_increments (ts : PlaneForest) :
    (increments ts).sum = -(ts.length : ℤ) := by
  induction ts with
  | nil => simp [increments]
  | cons t ts ih =>
    change (PlaneTree.increments t ++ increments ts).sum = -((ts.length + 1 : ℕ) : ℤ)
    rw [List.sum_append, PlaneTree.sum_increments, ih]
    simp only [Int.natCast_add, Int.natCast_one]
    omega

end BGW.PlaneForest
