/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Finite.Basic
import Lean.Elab.Tactic.Omega

/-!
# Canonical locally finite plane trees

This is the deterministic carrier used by the iid offspring construction in
`freezing1/Freezing1/PlaneTree.lean` and `PlaneTreeGeometry.lean`, adapted into
`BGW.LocallyFinite`. Unlike `BGW.PlaneTree`, its trees may have infinite height.

Addresses use positive child indices, with `[]` for the root. Offspring counts
are zero at absent addresses, but also at leaves: vertex membership is `Present`,
not positivity of the coordinate. The finite-tree bridge explicitly shifts the
existing zero-based addresses. No topology or probability law is installed here.
-/

@[expose] public section

namespace BGW.LocallyFinite

/-- A vertex address, with positive child indices and `[]` for the root. -/
abbrev Address := List ℕ

/-- A field assigning a finite offspring count to each address. -/
abbrev Offspring := Address → ℕ

/-- Invalid children have zero offspring; the condition propagates to descendants. -/
def Canonical (f : Offspring) : Prop :=
  ∀ (u : Address) (j : ℕ), ¬(1 ≤ j ∧ j ≤ f u) → f (u ++ [j]) = 0

/-- Canonical offspring fields describe possibly infinite, locally finite plane trees. -/
abbrev Tree := {f : Offspring // Canonical f}

/-- The number of children of the root. -/
def degree (T : Tree) : ℕ := T.val []

/-- The tree consisting only of its root, with zero offspring at every address. -/
def leaf : Tree := ⟨fun _ => 0, fun _ _ _ => rfl⟩

@[simp] theorem leaf_offspring (u : Address) : leaf.val u = 0 := rfl

@[simp] theorem degree_leaf : degree leaf = 0 := rfl

theorem Canonical.zero_descendants {f : Offspring} (hf : Canonical f)
    {u : Address} (hu : f u = 0) (v : Address) : f (u ++ v) = 0 := by
  induction v using List.reverseRecOn with
  | nil => simpa using hu
  | append_singleton v j ih =>
    rw [← List.append_assoc]
    exact hf (u ++ v) j (by rw [ih]; omega)

theorem Canonical.zero_of_absent_child {f : Offspring} (hf : Canonical f)
    (u : Address) (j : ℕ) (hj : ¬(1 ≤ j ∧ j ≤ f u)) (v : Address) :
    f (u ++ j :: v) = 0 := by
  simpa only [List.append_assoc, List.singleton_append] using
    hf.zero_descendants (hf u j hj) v

theorem eq_leaf_of_degree_zero {T : Tree} (hT : degree T = 0) : T = leaf := by
  apply Subtype.ext
  funext u
  simpa only [List.nil_append, leaf_offspring] using T.property.zero_descendants hT u

theorem degree_zero_iff (T : Tree) : degree T = 0 ↔ T = leaf :=
  ⟨eq_leaf_of_degree_zero, fun h => by rw [h]; rfl⟩

/-- Re-root at child `j`. An absent child is represented by `leaf`; use `Present`
to test whether that child actually exists. -/
def child (T : Tree) (j : ℕ) : Tree :=
  ⟨fun u => T.val (j :: u), fun u k hk => T.property (j :: u) k hk⟩

@[simp] theorem child_offspring (T : Tree) (j : ℕ) (u : Address) :
    (child T j).val u = T.val (j :: u) := rfl

theorem child_eq_leaf_of_absent (T : Tree) (j : ℕ)
    (hj : ¬(1 ≤ j ∧ j ≤ degree T)) : child T j = leaf := by
  apply Subtype.ext
  funext u
  exact T.property.zero_of_absent_child [] j hj u

/-- The root degree and its existing ordered children determine a tree. -/
theorem eq_of_degree_child_eq {T S : Tree} (hd : degree T = degree S)
    (hc : ∀ j, 1 ≤ j → j ≤ degree T → child T j = child S j) : T = S := by
  apply Subtype.ext
  funext u
  cases u with
  | nil => exact hd
  | cons j u =>
    by_cases hj : 1 ≤ j ∧ j ≤ degree T
    · exact congrArg (fun A : Tree => A.val u) (hc j hj.1 hj.2)
    · have hs : ¬(1 ≤ j ∧ j ≤ degree S) := by simpa only [hd] using hj
      exact (T.property.zero_of_absent_child [] j hj u).trans
        (S.property.zero_of_absent_child [] j hs u).symm

/-- Membership of an address, including leaves and the root. -/
def Present (T : Tree) : Address → Prop
  | [] => True
  | j :: u => 1 ≤ j ∧ j ≤ degree T ∧ Present (child T j) u

@[simp] theorem present_nil (T : Tree) : Present T [] := trivial

@[simp] theorem present_cons (T : Tree) (j : ℕ) (u : Address) :
    Present T (j :: u) ↔ 1 ≤ j ∧ j ≤ degree T ∧ Present (child T j) u := Iff.rfl

theorem not_present_offspring_zero (T : Tree) (u : Address) (hu : ¬Present T u) :
    T.val u = 0 := by
  induction u generalizing T with
  | nil => exact (hu trivial).elim
  | cons j u ih =>
    by_cases hj : 1 ≤ j ∧ j ≤ degree T
    · exact ih (child T j) (fun h => hu ⟨hj.1, hj.2, h⟩)
    · exact T.property.zero_of_absent_child [] j hj u

/-- Finiteness refers to the vertices, not to the support of the offspring field. -/
def FiniteVertices (T : Tree) : Prop := {u | Present T u}.Finite

end BGW.LocallyFinite
