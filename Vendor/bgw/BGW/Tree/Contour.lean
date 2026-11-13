/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.Fringe
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.List.Chain

/-!
# The discrete contour of a finite plane tree

The contour records heights during the complete depth-first traversal, starting and ending
at the root. Each child contributes its own contour raised by one, followed by a return to
height zero. The root-only tree has contour `[0]`; a tree with `n` vertices has contour length
`2 * (n - 1) + 1`, hence traversal duration `2 * (n - 1)`. Vertex addresses and their lengths
identify exactly the heights encountered. This is a list of discrete heights, without any
continuous interpolation.
-/

@[expose] public section

namespace BGW.PlaneTree

/-- Heights along the complete depth-first contour, including both endpoint visits. -/
def contour : PlaneTree → List ℕ :=
  fold fun cs => 0 :: (cs.map (fun c => c.map Nat.succ ++ [0])).flatten

@[simp] theorem contour_node (ts : List PlaneTree) :
    (node ts).contour =
      0 :: (ts.map (fun t => t.contour.map Nat.succ ++ [0])).flatten := by
  simp only [contour, fold_node, List.map_map, Function.comp_def]

@[simp] theorem contour_leaf : leaf.contour = [0] := by simp [leaf]

theorem contour_ne_nil (t : PlaneTree) : t.contour ≠ [] := by
  cases t with
  | node ts => simp

@[simp] theorem head?_contour (t : PlaneTree) : t.contour.head? = some 0 := by
  cases t with
  | node ts => simp

@[simp] theorem getLast?_contour (t : PlaneTree) : t.contour.getLast? = some 0 := by
  cases t with
  | node ts =>
    rw [contour_node]
    induction ts with
    | nil => simp
    | cons s ts ih =>
      simp only [List.map_cons, List.flatten_cons, List.append_assoc]
      change ((0 :: s.contour.map Nat.succ) ++
        (0 :: (ts.map (fun t => t.contour.map Nat.succ ++ [0])).flatten)).getLast? = some 0
      rw [List.getLast?_append_cons]
      exact ih

private theorem isChain_contour_blocks (cs : List (List ℕ))
    (hcs : ∀ c ∈ cs, c.IsChain (fun a b : ℕ => a + 1 = b ∨ b + 1 = a) ∧
      c.head? = some 0 ∧ c.getLast? = some 0) :
    (0 :: (cs.map (fun c => c.map Nat.succ ++ [0])).flatten).IsChain
      (fun a b : ℕ => a + 1 = b ∨ b + 1 = a) := by
  revert hcs
  induction cs with
  | nil =>
    intro _
    exact List.IsChain.singleton 0
  | cons c cs ih =>
    intro hcs
    obtain ⟨hchain, hhead, hlast⟩ := hcs c List.mem_cons_self
    have htail := ih (fun d hd => hcs d (List.mem_cons_of_mem c hd))
    have hup : (c.map Nat.succ).IsChain (fun a b : ℕ => a + 1 = b ∨ b + 1 = a) := by
      apply List.isChain_map_of_isChain Nat.succ ?_ hchain
      intro a b hab
      omega
    have hprefix : (0 :: c.map Nat.succ).IsChain
        (fun a b : ℕ => a + 1 = b ∨ b + 1 = a) := by
      apply hup.cons
      intro y hy
      have hy' : 1 = y := by simpa [hhead] using hy
      subst y
      exact Or.inl rfl
    simp only [List.map_cons, List.flatten_cons, List.append_assoc]
    change ((0 :: c.map Nat.succ) ++
      (0 :: (cs.map (fun d => d.map Nat.succ ++ [0])).flatten)).IsChain _
    apply hprefix.append htail
    intro x hx y hy
    have hx' : 1 = x := by simpa [List.getLast?_cons, hlast] using hx
    have hy' : 0 = y := by simpa using hy
    subst x
    subst y
    exact Or.inr rfl

/-- Every contour step changes height by exactly one; for the root-only tree this is vacuous. -/
theorem isChain_contour (t : PlaneTree) :
    t.contour.IsChain (fun a b : ℕ => a + 1 = b ∨ b + 1 = a) := by
  induction t with
  | node ts ih =>
    rw [contour_node]
    have hcs : ∀ c ∈ ts.map contour,
        c.IsChain (fun a b : ℕ => a + 1 = b ∨ b + 1 = a) ∧
          c.head? = some 0 ∧ c.getLast? = some 0 := by
      intro c hc
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
      exact ⟨ih s hs, head?_contour s, getLast?_contour s⟩
    simpa only [List.map_map, Function.comp_def] using isChain_contour_blocks _ hcs

/-- An addition-only form of the contour length formula. -/
theorem length_contour_add_one (t : PlaneTree) : t.contour.length + 1 = 2 * t.size := by
  induction t with
  | node ts ih =>
    have hmap : ts.map (fun t => t.contour.length + 1) = ts.map (fun t => 2 * t.size) := by
      apply List.map_congr_left
      intro s hs
      exact ih s hs
    rw [contour_node, List.length_cons, List.length_flatten]
    simp only [List.map_map, List.length_append, List.length_map, List.length_singleton,
      Function.comp_def]
    rw [hmap, List.sum_map_mul_left (l := ts) (f := size) (r := (2 : ℕ)), size_node]
    omega

/-- The contour has one more entry than its traversal duration. -/
@[simp] theorem length_contour (t : PlaneTree) :
    t.contour.length = 2 * (t.size - 1) + 1 := by
  have := length_contour_add_one t
  have := size_pos t
  omega

/-- The contour visits exactly the depths of the tree's vertex addresses. -/
theorem mem_contour_iff (t : PlaneTree) (h : ℕ) :
    h ∈ t.contour ↔ ∃ u, t.IsVertex u ∧ u.length = h := by
  induction t generalizing h with
  | node ts ih =>
    constructor
    · intro hm
      rw [contour_node] at hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨[], isVertex_nil _, rfl⟩
      · obtain ⟨block, hblock, hm⟩ := List.mem_flatten.mp hm
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hblock
        rcases List.mem_append.mp hm with hm | hm
        · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
          obtain ⟨u, hu, hlen⟩ := (ih s hs k).mp hk
          obtain ⟨i, hi⟩ := List.getElem?_of_mem hs
          obtain ⟨r, hr⟩ := hu
          refine ⟨i :: u, ⟨r, ?_⟩, ?_⟩
          · simp [hi, hr]
          · simp [hlen]
        · have hh : h = 0 := by simpa using hm
          subst h
          exact ⟨[], isVertex_nil _, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      cases u with
      | nil => simp
      | cons i u =>
        obtain ⟨r, hr⟩ := hu
        rw [fringe?_node_cons] at hr
        cases hc : ts[i]? with
        | none => simp [hc] at hr
        | some s =>
          have hs : s ∈ ts := List.mem_of_getElem? hc
          have hu : s.IsVertex u := ⟨r, by simpa [hc] using hr⟩
          have hm : u.length ∈ s.contour := (ih s hs u.length).mpr ⟨u, hu, rfl⟩
          rw [contour_node]
          apply List.mem_cons_of_mem
          apply List.mem_flatten.mpr
          refine ⟨s.contour.map Nat.succ ++ [0], List.mem_map_of_mem hs, ?_⟩
          apply List.mem_append_left
          simpa using List.mem_map_of_mem (f := Nat.succ) hm

end BGW.PlaneTree
