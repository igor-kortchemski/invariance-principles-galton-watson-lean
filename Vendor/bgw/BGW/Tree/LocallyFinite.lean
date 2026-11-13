/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.Basic
public import BGW.Tree.Vertices
public import BGW.Tree.Fringe
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite trees in canonical offspring coordinates

The existing `PlaneTree` uses zero-based child indices. The locally finite
carrier uses positive indices to match the existing BGW-law construction.
`positiveAddress` is the explicit conversion; zero is always an invalid index
on the locally finite side. All finite-tree reasoning uses the public list API.
-/

@[expose] public section

namespace BGW.PlaneTree

/-- Convert a zero-based address to its positive-index counterpart. -/
def positiveAddress (u : List ℕ) : List ℕ := u.map Nat.succ

@[simp] theorem positiveAddress_nil : positiveAddress [] = [] := rfl

@[simp] theorem positiveAddress_cons (i : ℕ) (u : List ℕ) :
    positiveAddress (i :: u) = (i + 1) :: positiveAddress u := rfl

/-- Offspring count at a positive-index address; invalid addresses have count zero. -/
def offspringAt : PlaneTree → List ℕ → ℕ
  | t, [] => t.rootDegree
  | _, 0 :: _ => 0
  | t, (i + 1) :: u => ((t.children[i]?).map (fun s => offspringAt s u)).getD 0

@[simp] theorem offspringAt_nil (t : PlaneTree) : t.offspringAt [] = t.rootDegree := rfl

@[simp] theorem offspringAt_zero_cons (t : PlaneTree) (u : List ℕ) :
    t.offspringAt (0 :: u) = 0 := rfl

theorem canonical_offspringAt (t : PlaneTree) : LocallyFinite.Canonical t.offspringAt := by
  intro u j
  induction u generalizing t with
  | nil =>
    cases j with
    | zero => simp [offspringAt]
    | succ j =>
      intro hj
      have hn : ¬j < t.children.length := by
        simp only [offspringAt, rootDegree] at hj
        omega
      simp [offspringAt, List.getElem?_eq_none (Nat.le_of_not_gt hn)]
  | cons i u ih =>
    cases i with
    | zero => simp [offspringAt]
    | succ i =>
      cases h : t.children[i]? with
      | none => simp [offspringAt, h]
      | some s => simpa only [List.cons_append, offspringAt, h, Option.map_some,
          Option.getD_some] using ih s

/-- View a finite plane tree as a canonical, possibly-infinite-tree value. -/
def toLocallyFinite (t : PlaneTree) : LocallyFinite.Tree :=
  ⟨t.offspringAt, t.canonical_offspringAt⟩

@[simp] theorem degree_toLocallyFinite (t : PlaneTree) :
    LocallyFinite.degree t.toLocallyFinite = t.rootDegree := rfl

@[simp] theorem toLocallyFinite_leaf : leaf.toLocallyFinite = LocallyFinite.leaf :=
  LocallyFinite.eq_leaf_of_degree_zero (by simp [rootDegree])

/-- The positive-index coordinates agree with the original fringe lookup. -/
theorem offspringAt_positiveAddress (t : PlaneTree) (u : List ℕ) :
    t.offspringAt (positiveAddress u) = ((t.fringe? u).map rootDegree).getD 0 := by
  induction u generalizing t with
  | nil => rfl
  | cons i u ih =>
    simp only [positiveAddress_cons, offspringAt, fringe?_cons]
    cases h : t.children[i]? with
    | none => rfl
    | some s => simpa using ih s

/-- An existing zero-based child becomes child `i + 1` in the new carrier. -/
theorem child_toLocallyFinite {t s : PlaneTree} (i : ℕ) (h : t.children[i]? = some s) :
    LocallyFinite.child t.toLocallyFinite (i + 1) = s.toLocallyFinite := by
  apply Subtype.ext
  funext u
  simp [LocallyFinite.child, toLocallyFinite, offspringAt, h]

/-- Vertex membership is preserved, including the root and leaves. -/
theorem present_toLocallyFinite (t : PlaneTree) (u : List ℕ) :
    LocallyFinite.Present t.toLocallyFinite (positiveAddress u) ↔ t.IsVertex u := by
  induction u generalizing t with
  | nil => simp
  | cons i u ih =>
    by_cases hi : i < t.children.length
    · have hc : t.children[i]? = some t.children[i] := List.getElem?_eq_getElem hi
      rw [positiveAddress_cons, LocallyFinite.present_cons, degree_toLocallyFinite,
        child_toLocallyFinite i hc, ih]
      simp [IsVertex, fringe?_cons, hc, rootDegree, Nat.succ_le_iff.mpr hi]
    · simp [positiveAddress_cons, LocallyFinite.present_cons, rootDegree,
        Nat.succ_le_iff, hi, IsVertex]

/-- Distinct finite trees stay distinct in the canonical offspring representation. -/
theorem toLocallyFinite_injective : Function.Injective toLocallyFinite := by
  intro t
  induction t with
  | node ts ih =>
    intro s h
    cases s with
    | node ss =>
      apply node_inj.mpr
      have hlen : ts.length = ss.length := by
        simpa using congrArg LocallyFinite.degree h
      apply List.ext_getElem hlen
      intro i hi hj
      apply ih ts[i] (List.getElem_mem hi)
      have ht : (node ts).children[i]? = some ts[i] := by simp [hi]
      have hs : (node ss).children[i]? = some ss[i] := by simp [hj]
      simpa only [child_toLocallyFinite i ht, child_toLocallyFinite i hs] using
        congrArg (fun T => LocallyFinite.child T (i + 1)) h

/-- Every present positive-index address has a zero-based preimage. -/
theorem exists_positiveAddress_of_present {T : LocallyFinite.Tree} {u : List ℕ}
    (hu : LocallyFinite.Present T u) : ∃ v, positiveAddress v = u := by
  induction u generalizing T with
  | nil => exact ⟨[], rfl⟩
  | cons j u ih =>
    obtain ⟨hj, _, hu⟩ := hu
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
    obtain ⟨v, hv⟩ := ih hu
    exact ⟨i :: v, by simp [hv]⟩

theorem finiteVertices_toLocallyFinite (t : PlaneTree) :
    LocallyFinite.FiniteVertices t.toLocallyFinite := by
  apply ((t.vertices.finite_toSet).image positiveAddress).subset
  intro u hu
  obtain ⟨v, rfl⟩ := exists_positiveAddress_of_present hu
  exact ⟨v, (mem_vertices_iff t v).mpr ((present_toLocallyFinite t v).mp hu), rfl⟩

end BGW.PlaneTree

namespace BGW.LocallyFinite

/-- A finite tree has a uniform bound on the depth of its vertices.
Adapted from `Freezing1/PlaneFiniteExtinction.lean`, without its model imports. -/
theorem FiniteVertices.exists_height_bound {T : Tree} (hT : FiniteVertices T) :
    ∃ n : ℕ, ∀ u, Present T u → u.length ≤ n := by
  classical
  change {u | Present T u}.Finite at hT
  refine ⟨hT.toFinset.sup List.length, ?_⟩
  intro u hu
  exact Finset.le_sup (hT.mem_toFinset.mpr hu)

/-- Cut at a deterministic depth, keeping the root and the order of children. -/
def truncate : ℕ → Tree → PlaneTree
  | 0, _ => PlaneTree.leaf
  | n + 1, T => PlaneTree.node (List.ofFn fun i : Fin (degree T) =>
      truncate n (child T (i.val + 1)))

/-- Once the truncation depth bounds all vertices, no information is lost. -/
theorem toLocallyFinite_truncate_of_height_bound (n : ℕ) (T : Tree)
    (hT : ∀ u, Present T u → u.length ≤ n) :
    (truncate n T).toLocallyFinite = T := by
  induction n generalizing T with
  | zero =>
    have hd : degree T = 0 := by
      by_contra h
      have hp : Present T [1] := ⟨by omega, by omega, trivial⟩
      have := hT [1] hp
      simp at this
    simpa [truncate] using (eq_leaf_of_degree_zero hd).symm
  | succ n ih =>
    apply eq_of_degree_child_eq
    · simp [truncate, PlaneTree.rootDegree]
    · intro j hj hdeg
      have hjT : j ≤ degree T := by
        simpa [truncate, PlaneTree.rootDegree] using hdeg
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
      have hi : i < degree T := by omega
      have hchild : ∀ u, Present (child T (i + 1)) u → u.length ≤ n := by
        intro u hu
        have := hT ((i + 1) :: u) ⟨by omega, by omega, hu⟩
        simp only [List.length_cons] at this
        omega
      have hc : (truncate (n + 1) T).children[i]? =
          some (truncate n (child T (i + 1))) := by
        simp [truncate, hi]
      exact (PlaneTree.child_toLocallyFinite i hc).trans (ih _ hchild)

/-- The finite plane trees are exactly the locally finite trees with finitely many vertices. -/
theorem exists_toLocallyFinite_iff (T : Tree) :
    (∃ t : PlaneTree, t.toLocallyFinite = T) ↔ FiniteVertices T := by
  constructor
  · rintro ⟨t, rfl⟩
    exact t.finiteVertices_toLocallyFinite
  · intro hT
    obtain ⟨n, hn⟩ := hT.exists_height_bound
    exact ⟨truncate n T, toLocallyFinite_truncate_of_height_bound n T hn⟩

end BGW.LocallyFinite

namespace BGW.PlaneTree

/-- The existing finite-tree type is equivalent to the finite part of the canonical carrier. -/
noncomputable def equivFiniteVertices :
    PlaneTree ≃ {T : LocallyFinite.Tree // LocallyFinite.FiniteVertices T} :=
  Equiv.ofBijective (fun t => ⟨t.toLocallyFinite, t.finiteVertices_toLocallyFinite⟩)
    ⟨fun _ _ h => toLocallyFinite_injective (congrArg Subtype.val h), by
      rintro ⟨T, hT⟩
      obtain ⟨t, ht⟩ := (LocallyFinite.exists_toLocallyFinite_iff T).mpr hT
      exact ⟨t, Subtype.ext ht⟩⟩

@[simp] theorem equivFiniteVertices_apply (t : PlaneTree) :
    (equivFiniteVertices t).val = t.toLocallyFinite := rfl

end BGW.PlaneTree
