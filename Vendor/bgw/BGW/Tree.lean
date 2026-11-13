/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Data.W.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Finite plane trees

A plane tree is a finite rooted tree whose children are ordered. We use Mathlib's
`WType`, with `Fin n` indexing the children of a vertex of outdegree `n`.
`PlaneTree.node` and `PlaneTree.children` provide the list interface. The `induction`
and `cases` tactics produce a single `node ts` case, and `PlaneTree.fold` defines
functions by bottom-up recursion, so the `WType` encoding is not used outside this file.

Addresses are zero-based lists of child indices; the root has address `[]`.
These are implementation coordinates, independent of the paper's one-based
numbering of vertices in depth-first order. Size counts vertices, including the root.
-/

@[expose] public section

namespace BGW

/-- Finite rooted ordered trees, with no vertex labels. -/
def PlaneTree : Type := WType (fun n : ℕ => Fin n)

instance : Encodable PlaneTree := inferInstanceAs (Encodable (WType _))

/-- Finite ordered forests. The empty forest is allowed. -/
abbrev PlaneForest := List PlaneTree

namespace PlaneTree

/-- A tree is determined by the ordered list of subtrees attached to its root. -/
def equivChildren : PlaneTree ≃ List PlaneTree :=
  (WType.equivSigma (fun n : ℕ => Fin n)).trans List.equivSigmaTuple.symm

/-- Attach an ordered list of trees to a new root. -/
def node (ts : List PlaneTree) : PlaneTree := equivChildren.symm ts

/-- The ordered subtrees attached to the root. -/
def children (t : PlaneTree) : List PlaneTree := equivChildren t

/-- Two plane trees are equal when their ordered lists of root subtrees agree. -/
@[ext] theorem ext {s t : PlaneTree} (h : s.children = t.children) : s = t :=
  equivChildren.injective h

@[simp] theorem children_node (ts : List PlaneTree) : (node ts).children = ts :=
  equivChildren.apply_symm_apply ts

@[simp] theorem node_children (t : PlaneTree) : node t.children = t :=
  equivChildren.symm_apply_apply t

@[simp] theorem node_inj {ts ss : List PlaneTree} : node ts = node ss ↔ ts = ss :=
  equivChildren.symm.injective.eq_iff

/-- Induction over all the children of a root. This is the default `induction` principle. -/
@[elab_as_elim, induction_eliminator] theorem induction_on {motive : PlaneTree → Prop}
    (t : PlaneTree) (node : ∀ ts, (∀ s ∈ ts, motive s) → motive (PlaneTree.node ts)) :
    motive t := by
  induction t with
  | mk n f ih =>
    rw [← node_children (WType.mk n f)]
    apply node
    intro s hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
    exact ih i

/-- Case analysis on the children of the root. This is the default `cases` principle. -/
@[elab_as_elim, cases_eliminator] def casesOn {motive : PlaneTree → Sort*} (t : PlaneTree)
    (node : ∀ ts, motive (PlaneTree.node ts)) : motive t :=
  cast (congrArg motive (node_children t)) (node t.children)

@[simp] theorem casesOn_node {motive : PlaneTree → Sort*} (ts : List PlaneTree)
    (node : ∀ ts, motive (PlaneTree.node ts)) : casesOn (PlaneTree.node ts) node = node ts := by
  apply eq_of_heq
  refine (cast_heq _ _).trans ?_
  have h := children_node ts
  generalize (PlaneTree.node ts).children = cs at h ⊢
  subst h
  rfl

/-- Bottom-up recursion: `fold g` applies `g` to the values already computed at the
children of the root, in child order. -/
def fold {β : Type*} (g : List β → β) : PlaneTree → β :=
  WType.elim β fun ⟨_, f⟩ => g (List.ofFn f)

@[simp] theorem fold_node {β : Type*} (g : List β → β) (ts : List PlaneTree) :
    fold g (node ts) = g (ts.map (fold g)) := by
  change g (List.ofFn (fold g ∘ ts.get)) = _
  rw [← List.map_ofFn, List.ofFn_get]

/-- The tree consisting only of its root. -/
def leaf : PlaneTree := node []

/-- The number of children of the root. -/
def rootDegree (t : PlaneTree) : ℕ := t.children.length

/-- The number of vertices, including the root. -/
def size : PlaneTree → ℕ := fold fun ns => 1 + ns.sum

@[simp] theorem size_node (ts : List PlaneTree) :
    (node ts).size = 1 + (ts.map size).sum :=
  fold_node _ ts

@[simp] theorem children_leaf : leaf.children = [] := children_node []

@[simp] theorem size_leaf : leaf.size = 1 := by simp [leaf]

@[simp] theorem rootDegree_node (ts : List PlaneTree) :
    (node ts).rootDegree = ts.length := by simp [rootDegree]

theorem size_pos (t : PlaneTree) : 0 < t.size := by
  cases t with
  | node ts =>
    rw [size_node]
    omega

/-- Lookup of a fringe subtree. `none` means that the address is not a vertex.
The returned tree is re-rooted: its addresses start at `[]` again. -/
def fringe? : PlaneTree → List ℕ → Option PlaneTree
  | t, [] => some t
  | t, i :: u => t.children[i]?.bind (fun s => s.fringe? u)

/-- An address belongs to the tree exactly when fringe lookup succeeds. -/
def IsVertex (t : PlaneTree) (u : List ℕ) : Prop := ∃ s, t.fringe? u = some s

/-- A leaf is a vertex whose fringe subtree consists only of its root. -/
def IsLeaf (t : PlaneTree) (u : List ℕ) : Prop := t.fringe? u = some leaf

@[simp] theorem fringe?_nil (t : PlaneTree) : t.fringe? [] = some t := rfl

@[simp] theorem fringe?_cons (t : PlaneTree) (i : ℕ) (u : List ℕ) :
    t.fringe? (i :: u) = t.children[i]?.bind (fun s => s.fringe? u) := rfl

theorem fringe?_node_cons (ts : List PlaneTree) (i : ℕ) (u : List ℕ) :
    (node ts).fringe? (i :: u) = ts[i]?.bind (fun s => s.fringe? u) := by simp

end PlaneTree
end BGW
