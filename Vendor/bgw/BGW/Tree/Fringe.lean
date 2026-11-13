/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree

/-!
# Fringe subtrees and replacement

Lookup uses zero-based addresses. Replacing the subtree at a valid address
identifies the old and new roots; replacement at a leaf is leaf grafting.
Replacement at an invalid address leaves the tree unchanged.
-/

@[expose] public section

namespace BGW.PlaneTree

/-- Taking a fringe subtree re-roots all its descendant addresses. -/
theorem fringe?_append (t : PlaneTree) (u v : List ℕ) :
    t.fringe? (u ++ v) = (t.fringe? u).bind (fun s => s.fringe? v) := by
  induction u generalizing t with
  | nil => simp
  | cons i u ih =>
    simp only [List.cons_append, fringe?_cons]
    cases h : t.children[i]? with
    | none => simp
    | some s => simpa using ih s

@[simp] theorem isVertex_nil (t : PlaneTree) : t.IsVertex [] := ⟨t, rfl⟩

theorem isVertex_append_iff (t : PlaneTree) (u v : List ℕ) :
    t.IsVertex (u ++ v) ↔ ∃ s, t.fringe? u = some s ∧ s.IsVertex v := by
  simp only [IsVertex, fringe?_append]
  cases h : t.fringe? u <;> simp

/-- Every prefix of a vertex address is a vertex address. -/
theorem IsVertex.prefix {t : PlaneTree} {u v : List ℕ}
    (h : t.IsVertex (u ++ v)) : t.IsVertex u := by
  obtain ⟨s, hs, _⟩ := (isVertex_append_iff t u v).mp h
  exact ⟨s, hs⟩

/-- Children form an initial segment, with no gaps. -/
@[simp] theorem isVertex_singleton_iff (t : PlaneTree) (i : ℕ) :
    t.IsVertex [i] ↔ i < t.rootDegree := by
  simp [IsVertex, rootDegree, List.getElem?_eq_some_iff]

/-- The children of any vertex are precisely an initial segment. -/
theorem isVertex_append_singleton_iff {t s : PlaneTree} {u : List ℕ}
    (h : t.fringe? u = some s) (i : ℕ) :
    t.IsVertex (u ++ [i]) ↔ i < s.rootDegree := by
  rw [isVertex_append_iff]
  simp [h]

theorem IsLeaf.isVertex {t : PlaneTree} {u : List ℕ} (h : t.IsLeaf u) :
    t.IsVertex u := ⟨leaf, h⟩

@[simp] theorem isLeaf_nil_iff (t : PlaneTree) : t.IsLeaf [] ↔ t = leaf := by
  simp [IsLeaf]

/-- Replace the fringe subtree at an address, preserving the ordered context.
At a leaf this is the grafting operation used in cut-and-graft arguments. -/
def graft : PlaneTree → List ℕ → PlaneTree → PlaneTree
  | _, [], s => s
  | t, i :: u, s => node (t.children.modify i (fun r => r.graft u s))

/-- Remove strict descendants of an address, retaining that vertex as a leaf. -/
def cut (t : PlaneTree) (u : List ℕ) : PlaneTree := t.graft u leaf

@[simp] theorem graft_nil (t s : PlaneTree) : t.graft [] s = s := rfl

@[simp] theorem graft_cons (t s : PlaneTree) (i : ℕ) (u : List ℕ) :
    t.graft (i :: u) s = node (t.children.modify i (fun r => r.graft u s)) := rfl

/-- The inserted tree is exactly the fringe subtree at the graft address. -/
theorem fringe?_graft {t : PlaneTree} {u : List ℕ} (h : t.IsVertex u)
    (s : PlaneTree) : (t.graft u s).fringe? u = some s := by
  induction u generalizing t with
  | nil => simp
  | cons i u ih =>
    obtain ⟨r, hr⟩ := h
    simp only [fringe?_cons] at hr
    cases hc : t.children[i]? with
    | none => simp [hc] at hr
    | some a =>
      have ha : a.IsVertex u := ⟨r, by simpa [hc] using hr⟩
      simpa [List.getElem?_modify_eq, hc] using ih ha

/-- Replacing a fringe subtree by itself recovers the original tree. -/
theorem graft_fringe {t r : PlaneTree} {u : List ℕ} (h : t.fringe? u = some r) :
    t.graft u r = t := by
  induction u generalizing t with
  | nil => simpa using h.symm
  | cons i u ih =>
    rw [graft_cons, ← node_children t]
    congr 1
    apply List.ext_getElem?
    intro j
    by_cases hij : i = j
    · subst j
      simp only [List.getElem?_modify_eq]
      cases hc : t.children[i]? with
      | none => simp [hc]
      | some a =>
        have ha : a.fringe? u = some r := by simpa [hc] using h
        simp [hc, ih ha]
    · simp [List.getElem?_modify_ne _ _ hij]

/-- Repeated replacements at one address keep only the last replacement. -/
theorem graft_graft (t s r : PlaneTree) (u : List ℕ) :
    (t.graft u s).graft u r = t.graft u r := by
  induction u generalizing t with
  | nil => simp
  | cons i u ih =>
    simp only [graft_cons, children_node, List.modify_modify_eq]
    congr 1
    congr 1
    funext a
    exact ih a

theorem isLeaf_cut {t : PlaneTree} {u : List ℕ} (h : t.IsVertex u) :
    (t.cut u).IsLeaf u := fringe?_graft h leaf

/-- Cutting and restoring the removed fringe reconstructs the original tree. -/
theorem graft_cut {t r : PlaneTree} {u : List ℕ} (h : t.fringe? u = some r) :
    (t.cut u).graft u r = t := by
  rw [cut, graft_graft, graft_fringe h]

private theorem sum_sizes_modify {ts : List PlaneTree} {i : ℕ} {a : PlaneTree}
    (hi : ts[i]? = some a) (f : PlaneTree → PlaneTree) (b c : ℕ)
    (h : (f a).size + b = a.size + c) :
    ((ts.modify i f).map size).sum + b = (ts.map size).sum + c := by
  induction ts generalizing i with
  | nil => simp at hi
  | cons t ts ih =>
    cases i with
    | zero =>
      have ha : t = a := by simpa using hi
      subst a
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        congrArg (fun n => n + (ts.map size).sum) h
    | succ i =>
      have he := ih (by simpa using hi)
      simpa [Nat.add_assoc] using congrArg (fun n => t.size + n) he

/-- Subtree replacement removes exactly the old fringe and inserts the new one. -/
theorem size_graft_add {t r : PlaneTree} {u : List ℕ} (h : t.fringe? u = some r)
    (s : PlaneTree) : (t.graft u s).size + r.size = t.size + s.size := by
  induction u generalizing t with
  | nil =>
    have ht : t = r := by simpa using h
    simp [ht, Nat.add_comm]
  | cons i u ih =>
    cases hc : t.children[i]? with
    | none => simp [hc] at h
    | some a =>
      have ha : a.fringe? u = some r := by simpa [hc] using h
      have he := sum_sizes_modify hc (fun a => a.graft u s) r.size s.size (ih ha)
      have ht := size_node t.children
      rw [node_children] at ht
      simp only [graft_cons, size_node]
      omega

/-- Leaf grafting identifies the leaf with the inserted root. -/
theorem size_graft_of_isLeaf {t : PlaneTree} {u : List ℕ} (h : t.IsLeaf u)
    (s : PlaneTree) : (t.graft u s).size + 1 = t.size + s.size := by
  simpa using size_graft_add h s

/-- A failed lookup cannot create a new branch by grafting. -/
theorem graft_of_fringe?_eq_none {t : PlaneTree} {u : List ℕ}
    (h : t.fringe? u = none) (s : PlaneTree) : t.graft u s = t := by
  induction u generalizing t with
  | nil => simp at h
  | cons i u ih =>
    rw [graft_cons, ← node_children t]
    congr 1
    apply List.ext_getElem?
    intro j
    by_cases hij : i = j
    · subst j
      simp only [List.getElem?_modify_eq]
      cases hc : t.children[i]? with
      | none => simp [hc]
      | some a =>
        have ha : a.fringe? u = none := by simpa [hc] using h
        simp [hc, ih ha]
    · simp [List.getElem?_modify_ne _ _ hij]

end BGW.PlaneTree
