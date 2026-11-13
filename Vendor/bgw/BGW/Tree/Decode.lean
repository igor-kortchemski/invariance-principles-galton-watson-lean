/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.DFS

/-!
# Reconstruction from depth-first outdegrees

Read a natural degree word from right to left. At a vertex of degree `d`,
the first `d` trees already reconstructed become its ordered children.
The decoder fails if fewer than `d` trees are available. A tree word must
leave exactly one tree; an empty word represents the empty forest only.
-/

@[expose] public section

namespace BGW.PlaneForest

/-- Concatenate the degree words in component order. -/
def degrees (ts : PlaneForest) : List ℕ := (ts.map PlaneTree.degrees).flatten

@[simp] theorem degrees_nil : degrees [] = [] := rfl

@[simp] theorem degrees_cons (t : PlaneTree) (ts : PlaneForest) :
    degrees (t :: ts) = t.degrees ++ degrees ts := rfl

theorem degrees_append (ts ss : PlaneForest) :
    degrees (ts ++ ss) = degrees ts ++ degrees ss := by
  simp [degrees]

/-- Reconstruct an ordered forest from its depth-first outdegrees. -/
def ofDegrees? : List ℕ → Option PlaneForest
  | [] => some []
  | d :: ds => (ofDegrees? ds).bind fun ts =>
      if d ≤ ts.length then some (PlaneTree.node (ts.take d) :: ts.drop d) else none

@[simp] theorem ofDegrees?_nil : ofDegrees? [] = some [] := rfl

theorem ofDegrees?_cons (d : ℕ) (ds : List ℕ) :
    ofDegrees? (d :: ds) = (ofDegrees? ds).bind (fun ts =>
      if d ≤ ts.length then some (PlaneTree.node (ts.take d) :: ts.drop d) else none) := rfl

private theorem ofDegrees?_forest_prefix (ts : PlaneForest) :
    (∀ t ∈ ts, ∀ ds, ofDegrees? (t.degrees ++ ds) =
      (ofDegrees? ds).map (fun ss => t :: ss)) →
    ∀ ds, ofDegrees? (degrees ts ++ ds) = (ofDegrees? ds).map (fun ss => ts ++ ss) := by
  induction ts with
  | nil => intro _ ds; simp
  | cons t ts ih =>
    intro h ds
    rw [degrees_cons, List.append_assoc, h t (by simp)]
    rw [ih (fun s hs => h s (by simp [hs])) ds]
    simp [Option.map_map, Function.comp_def]

/-- Prepending one complete tree word adds that tree to any decoded suffix. -/
theorem ofDegrees?_tree_degrees_append (t : PlaneTree) (ds : List ℕ) :
    ofDegrees? (t.degrees ++ ds) = (ofDegrees? ds).map (fun ts => t :: ts) := by
  induction t generalizing ds with
  | node ts ih =>
    rw [PlaneTree.degrees_node, List.cons_append, ofDegrees?_cons]
    change (ofDegrees? (degrees ts ++ ds)).bind _ = _
    rw [ofDegrees?_forest_prefix ts ih ds]
    cases hd : ofDegrees? ds with
    | none => simp
    | some ss => simp

/-- The parser respects concatenation with any suffix word, valid or invalid. -/
theorem ofDegrees?_degrees_append (ts : PlaneForest) (ds : List ℕ) :
    ofDegrees? (degrees ts ++ ds) = (ofDegrees? ds).map (fun ss => ts ++ ss) :=
  ofDegrees?_forest_prefix ts (fun t _ => ofDegrees?_tree_degrees_append t) ds

@[simp] theorem ofDegrees?_degrees (ts : PlaneForest) :
    ofDegrees? (degrees ts) = some ts := by
  simpa using ofDegrees?_degrees_append ts []

/-- A successful parse reproduces exactly the input degree word. -/
theorem degrees_of_ofDegrees?_eq_some {ds : List ℕ} {ts : PlaneForest}
    (h : ofDegrees? ds = some ts) : degrees ts = ds := by
  induction ds generalizing ts with
  | nil =>
    have ht : ts = [] := by simpa using h.symm
    simp [ht]
  | cons d ds ih =>
    rw [ofDegrees?_cons, Option.bind_eq_some_iff] at h
    obtain ⟨ss, hs, h⟩ := h
    split at h
    next hd =>
      have ht : PlaneTree.node (ss.take d) :: ss.drop d = ts := by simpa using h
      rw [← ht, degrees_cons, PlaneTree.degrees_node, List.length_take_of_le hd]
      change d :: (degrees (ss.take d) ++ degrees (ss.drop d)) = d :: ds
      rw [← degrees_append, List.take_append_drop, ih hs]
    next => simp at h

/-- Successful parsing is exactly membership in the range of the forest encoder. -/
theorem ofDegrees?_eq_some_iff {ds : List ℕ} {ts : PlaneForest} :
    ofDegrees? ds = some ts ↔ degrees ts = ds := by
  constructor
  · exact degrees_of_ofDegrees?_eq_some
  · intro h
    rw [← h, ofDegrees?_degrees]

theorem degrees_injective : Function.Injective degrees := by
  intro ts ss h
  have he := congrArg ofDegrees? h
  simpa using he

/-- The number of roots is the deficit between word length and total degree. -/
theorem length_add_sum_degrees (ts : PlaneForest) :
    ts.length + (degrees ts).sum = (degrees ts).length := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [degrees_cons, List.length_cons, List.sum_append, List.length_append]
    have ht := t.sum_degrees_add_one
    have hl := t.length_degrees
    omega

theorem length_add_sum_of_ofDegrees?_eq_some {ds : List ℕ} {ts : PlaneForest}
    (h : ofDegrees? ds = some ts) : ts.length + ds.sum = ds.length := by
  rw [← degrees_of_ofDegrees?_eq_some h]
  exact length_add_sum_degrees ts

end BGW.PlaneForest

namespace BGW.PlaneTree

/-- Reconstruct a single tree, rejecting failed parses and nonsingleton forests. -/
def ofDegrees? (ds : List ℕ) : Option PlaneTree :=
  match PlaneForest.ofDegrees? ds with
  | some [t] => some t
  | _ => none

/-- A single-tree parse is precisely a forest parse with one component. -/
theorem ofDegrees?_eq_some_iff_forest {ds : List ℕ} {t : PlaneTree} :
    ofDegrees? ds = some t ↔ PlaneForest.ofDegrees? ds = some [t] := by
  cases h : PlaneForest.ofDegrees? ds with
  | none => simp [ofDegrees?, h]
  | some ts =>
    cases ts with
    | nil => simp [ofDegrees?, h]
    | cons s ts => cases ts <;> simp [ofDegrees?, h]

/-- Both reconstruction identities, with failure explicit for other words. -/
theorem ofDegrees?_eq_some_iff {ds : List ℕ} {t : PlaneTree} :
    ofDegrees? ds = some t ↔ t.degrees = ds := by
  rw [ofDegrees?_eq_some_iff_forest, PlaneForest.ofDegrees?_eq_some_iff]
  simp

@[simp] theorem ofDegrees?_degrees (t : PlaneTree) : ofDegrees? t.degrees = some t :=
  ofDegrees?_eq_some_iff.mpr rfl

theorem degrees_injective : Function.Injective degrees := by
  intro s t h
  have he := congrArg ofDegrees? h
  simpa using he

end BGW.PlaneTree
