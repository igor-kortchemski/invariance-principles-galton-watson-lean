/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.Contour
public import BGW.Tree.Geometry
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Indexes

/-!
# The contour as a walk on vertex addresses

The contour starts at the root, traverses the children in order, and returns to the
root after each child. Both endpoint visits are included. Projecting an address to
its length gives the existing discrete height contour. Consecutive addresses are
adjacent in the graph metric. The first occurrence of the vertex at DFS index `i`
is at contour index `2 * i - depth`; this refers to the address itself, not merely
to its height.
-/

@[expose] public section

namespace BGW.PlaneTree

/-- Vertex addresses along the complete contour, including both endpoint visits. -/
def vertexContour : PlaneTree → List (List ℕ) :=
  fold fun cs => [] :: (cs.mapIdx fun i c => c.map (List.cons i) ++ [[]]).flatten

@[simp] theorem vertexContour_node (ts : List PlaneTree) :
    (node ts).vertexContour =
      [] :: (ts.mapIdx fun i t => t.vertexContour.map (List.cons i) ++ [[]]).flatten := by
  simp only [vertexContour, fold_node, List.mapIdx_eq_ofFn, List.length_map,
    List.get_eq_getElem, List.getElem_map]
  rfl

@[simp] theorem vertexContour_leaf : leaf.vertexContour = [[]] := by simp [leaf]

theorem vertexContour_ne_nil (t : PlaneTree) : t.vertexContour ≠ [] := by
  cases t with
  | node ts => simp

@[simp] theorem head?_vertexContour (t : PlaneTree) :
    t.vertexContour.head? = some [] := by
  cases t with
  | node ts => simp

private theorem getLast?_vertexContour_blocks (cs : List (List (List ℕ)))
    (f : ℕ → ℕ) :
    ([] :: (cs.mapIdx fun i c => c.map (List.cons (f i)) ++ [[]]).flatten).getLast? =
      some [] := by
  induction cs generalizing f with
  | nil => simp
  | cons c cs ih =>
    simp only [List.mapIdx_cons, List.flatten_cons, List.append_assoc]
    change (([] :: c.map (List.cons (f 0))) ++
      ([] :: (cs.mapIdx fun i d => d.map (List.cons (f (i + 1))) ++ [[]]).flatten)).getLast? = _
    rw [List.getLast?_append_cons]
    exact ih _

@[simp] theorem getLast?_vertexContour (t : PlaneTree) :
    t.vertexContour.getLast? = some [] := by
  cases t with
  | node ts =>
    rw [vertexContour_node]
    have h := getLast?_vertexContour_blocks (ts.map vertexContour) id
    simpa only [List.mapIdx_eq_ofFn, List.length_map, List.get_eq_getElem,
      List.getElem_map, Fin.val_cast, id_eq] using h

/-- Address depth is exactly the height recorded by the discrete contour. -/
theorem map_length_vertexContour (t : PlaneTree) :
    t.vertexContour.map List.length = t.contour := by
  induction t with
  | node ts ih =>
    have hblock (s : PlaneTree) (hs : s ∈ ts) (i : ℕ) :
        (s.vertexContour.map (List.cons i) ++ [[]]).map List.length =
          s.contour.map Nat.succ ++ [0] := by
      have h := congrArg (fun c : List ℕ => c.map Nat.succ) (ih s hs)
      simpa only [List.map_append, List.map_map, List.map_singleton,
        List.length_nil, Function.comp_def, List.length_cons] using
          congrArg (fun c : List ℕ => c ++ [0]) h
    rw [vertexContour_node, contour_node, List.map_cons, List.length_nil,
      List.map_flatten]
    congr 1
    congr 1
    apply List.ext_getElem (by simp)
    intro i hi hi'
    have hiTs : i < ts.length := by simpa using hi'
    simpa only [List.getElem_map, List.getElem_mapIdx] using
      hblock (ts[i]'hiTs) (List.getElem_mem hiTs) i

/-- Each edge is traversed twice and the initial root visit is also listed. -/
@[simp] theorem length_vertexContour (t : PlaneTree) :
    t.vertexContour.length = 2 * (t.size - 1) + 1 := by
  have h := congrArg List.length (map_length_vertexContour t)
  simpa only [List.length_map, length_contour] using h

/-- An addition-only form of the contour length formula. -/
theorem length_vertexContour_add_one (t : PlaneTree) :
    t.vertexContour.length + 1 = 2 * t.size := by
  have h := length_vertexContour t
  have hp := size_pos t
  omega

/-- The contour visits precisely the present vertex addresses. -/
theorem mem_vertexContour_iff (t : PlaneTree) (u : List ℕ) :
    u ∈ t.vertexContour ↔ t.IsVertex u := by
  induction t generalizing u with
  | node ts ih =>
    cases u with
    | nil => simp [IsVertex]
    | cons i u =>
      simp only [vertexContour_node, List.mem_cons, reduceCtorEq, false_or,
        List.mem_flatten, List.mem_mapIdx, IsVertex, fringe?_node_cons]
      constructor
      · rintro ⟨_, ⟨j, hj, rfl⟩, hmem⟩
        rcases List.mem_append.mp hmem with hmem | hmem
        · obtain ⟨v, hv, heq⟩ := List.mem_map.mp hmem
          obtain ⟨rfl, rfl⟩ := List.cons.inj heq
          obtain ⟨s, hs⟩ := (ih _ (List.getElem_mem hj) v).mp hv
          exact ⟨s, by simpa [hj] using hs⟩
        · simp only [List.mem_singleton] at hmem
          cases hmem
      · rintro ⟨s, hs⟩
        by_cases hi : i < ts.length
        · have hsub : IsVertex ts[i] u := ⟨s, by simpa [hi] using hs⟩
          refine ⟨_, ⟨i, hi, rfl⟩, List.mem_append_left _ ?_⟩
          exact List.mem_map_of_mem ((ih _ (List.getElem_mem hi) u).mpr hsub)
        · simp [hi] at hs

private theorem graphDist_cons_same (i : ℕ) (u v : List ℕ) :
    graphDist (i :: u) (i :: v) = graphDist u v := by
  have h := graphDist_add_two_lca u v
  have h' := graphDist_add_two_lca (i :: u) (i :: v)
  have hlca : lca (i :: u) (i :: v) = i :: lca u v := by simp [lca]
  rw [hlca] at h'
  simp only [List.length_cons] at h'
  omega

private theorem isChain_vertexContour_blocks (cs : List (List (List ℕ)))
    (hcs : ∀ c ∈ cs, c.IsChain (fun u v => graphDist u v = 1) ∧
      c.head? = some [] ∧ c.getLast? = some []) (f : ℕ → ℕ) :
    ([] :: (cs.mapIdx fun i c => c.map (List.cons (f i)) ++ [[]]).flatten).IsChain
      (fun u v => graphDist u v = 1) := by
  revert hcs f
  induction cs with
  | nil =>
    intro _ _
    exact List.IsChain.singleton []
  | cons c cs ih =>
    intro hcs f
    obtain ⟨hchain, hhead, hlast⟩ := hcs c List.mem_cons_self
    have htail := ih (fun d hd => hcs d (List.mem_cons_of_mem c hd))
      (fun i => f (i + 1))
    have hup : (c.map (List.cons (f 0))).IsChain (fun u v => graphDist u v = 1) := by
      apply List.isChain_map_of_isChain (List.cons (f 0)) ?_ hchain
      intro u v huv
      simpa only [graphDist_cons_same] using huv
    have hprefix : ([] :: c.map (List.cons (f 0))).IsChain
        (fun u v => graphDist u v = 1) := by
      apply hup.cons
      intro v hv
      have hv' : [f 0] = v := by simpa [hhead] using hv
      subst v
      simp
    simp only [List.mapIdx_cons, List.flatten_cons, List.append_assoc]
    change (([] :: c.map (List.cons (f 0))) ++
      ([] :: (cs.mapIdx fun i d => d.map (List.cons (f (i + 1))) ++ [[]]).flatten)).IsChain _
    apply hprefix.append htail
    intro u hu v hv
    have hu' : [f 0] = u := by simpa [List.getLast?_cons, hlast] using hu
    have hv' : [] = v := by simpa using hv
    subst u
    subst v
    rw [graphDist_comm]
    simp

/-- Successive contour visits are joined by one parent-child edge. -/
theorem isChain_vertexContour (t : PlaneTree) :
    t.vertexContour.IsChain (fun u v => graphDist u v = 1) := by
  induction t with
  | node ts ih =>
    rw [vertexContour_node]
    have hcs : ∀ c ∈ ts.map vertexContour,
        c.IsChain (fun u v => graphDist u v = 1) ∧
          c.head? = some [] ∧ c.getLast? = some [] := by
      intro c hc
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
      exact ⟨ih s hs, head?_vertexContour s, getLast?_vertexContour s⟩
    have h := isChain_vertexContour_blocks _ hcs id
    simpa only [List.mapIdx_eq_ofFn, List.length_map, List.get_eq_getElem,
      List.getElem_map, Fin.val_cast, id_eq] using h

private theorem idxOf_map_cons (cs : List (List ℕ)) (j : ℕ) (u : List ℕ) :
    (cs.map (List.cons j)).idxOf (j :: u) = cs.idxOf u := by
  induction cs with
  | nil => rfl
  | cons v cs ih => simp [List.idxOf_cons, ih]

/-- Locate an element in a block when it is absent from all preceding blocks. -/
private theorem idxOf_flatten_mapIdx_of_mem {α : Type*} (ts : List α)
    (blocks : ℕ → α → List (List ℕ)) (j : ℕ) (hj : j < ts.length) (u : List ℕ)
    (hu : u ∈ blocks j ts[j])
    (hprev : ∀ k (hk : k < j), u ∉ blocks k (ts[k]'(Nat.lt_trans hk hj))) :
    (ts.mapIdx blocks).flatten.idxOf u =
      ((ts.take j).mapIdx blocks).flatten.length + (blocks j ts[j]).idxOf u := by
  induction ts generalizing blocks j with
  | nil => simp at hj
  | cons s ts ih =>
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero] at hu
      simp only [List.mapIdx_cons, List.flatten_cons, List.take_zero, List.mapIdx_nil,
        List.flatten_nil, List.length_nil, Nat.zero_add, List.getElem_cons_zero]
      exact List.idxOf_append_of_mem hu
    | succ j =>
      have hj' : j < ts.length := by simpa using hj
      have hzero : u ∉ blocks 0 s := by simpa using hprev 0 (Nat.succ_pos j)
      have hu' : u ∈ blocks (j + 1) ts[j] := by simpa using hu
      have hprev' : ∀ k (hk : k < j),
          u ∉ blocks (k + 1) (ts[k]'(Nat.lt_trans hk hj')) := by
        intro k hk
        simpa using hprev (k + 1) (Nat.succ_lt_succ hk)
      have htail := ih (fun k => blocks (k + 1)) j hj' hu' hprev'
      simp only [List.mapIdx_cons, List.flatten_cons, List.take_succ_cons,
        List.getElem_cons_succ, List.length_append]
      rw [List.idxOf_append_of_notMem hzero, htail]
      omega

private theorem length_vertexContour_blocks (ts : List PlaneTree) :
    (ts.mapIdx fun i t => t.vertexContour.map (List.cons i) ++ [[]]).flatten.length =
      2 * (ts.map size).sum := by
  have h := length_vertexContour_add_one (node ts)
  simp only [vertexContour_node, List.length_cons, size_node] at h
  omega

private theorem length_vertices_blocks (ts : List PlaneTree) :
    (ts.mapIdx fun i t => t.vertices.map (List.cons i)).flatten.length =
      (ts.map size).sum := by
  have h := length_vertices (node ts)
  simp only [vertices_node, List.length_cons, size_node] at h
  change (ts.mapIdx fun i t => t.vertices.map (List.cons i)).flatten.length + 1 =
    1 + (ts.map size).sum at h
  omega

/-- The first contour visit plus vertex depth is twice the DFS index.
This addition-only form certifies that the first-visit subtraction never truncates. -/
theorem idxOf_vertexContour_add_length (t : PlaneTree) (u : List ℕ)
    (hu : t.IsVertex u) :
    t.vertexContour.idxOf u + u.length = 2 * t.vertices.idxOf u := by
  induction t generalizing u with
  | node ts ih =>
    cases u with
    | nil => simp
    | cons j u =>
      obtain ⟨s, hs⟩ := hu
      by_cases hj : j < ts.length
      · have hsub : IsVertex ts[j] u := ⟨s, by simpa [hj] using hs⟩
        have hmC : u ∈ vertexContour ts[j] := (mem_vertexContour_iff _ _).mpr hsub
        have hmV : u ∈ vertices ts[j] := (mem_vertices_iff _ _).mpr hsub
        have hmC' : j :: u ∈ (vertexContour ts[j]).map (List.cons j) :=
          List.mem_map_of_mem hmC
        have hmV' : j :: u ∈ (vertices ts[j]).map (List.cons j) :=
          List.mem_map_of_mem hmV
        have hc := idxOf_flatten_mapIdx_of_mem ts
          (fun i t => t.vertexContour.map (List.cons i) ++ [[]]) j hj (j :: u)
          (List.mem_append_left _ hmC') (by
            intro k hk hmem
            rcases List.mem_append.mp hmem with hmem | hmem
            · obtain ⟨v, _, heq⟩ := List.mem_map.mp hmem
              have hkj := (List.cons.inj heq).1
              omega
            · simp only [List.mem_singleton] at hmem
              cases hmem)
        rw [List.idxOf_append_of_mem hmC', idxOf_map_cons] at hc
        have hv := idxOf_flatten_mapIdx_of_mem ts
          (fun i t => t.vertices.map (List.cons i)) j hj (j :: u) hmV' (by
            intro k hk hmem
            obtain ⟨v, _, heq⟩ := List.mem_map.mp hmem
            have hkj := (List.cons.inj heq).1
            omega)
        rw [idxOf_map_cons] at hv
        have hsubidx := ih _ (List.getElem_mem hj) u hsub
        rw [vertexContour_node, vertices_node,
          List.idxOf_cons_ne _ (by simp), List.idxOf_cons_ne _ (by simp), hc, hv,
          length_vertexContour_blocks, length_vertices_blocks]
        simp only [List.length_cons]
        omega
      · simp [hj] at hs

/-- The first visit to the address at DFS index `i` occurs at `2 * i - depth`.
`idxOf?` specifies both this occurrence and the absence of every earlier occurrence. -/
theorem idxOf?_vertexContour_of_getElem?_vertices {t : PlaneTree} {i : ℕ} {u : List ℕ}
    (hi : t.vertices[i]? = some u) :
    t.vertexContour.idxOf? u = some (2 * i - u.length) := by
  obtain ⟨hi', heq⟩ := List.getElem?_eq_some_iff.mp hi
  have hu : t.IsVertex u := (mem_vertices_iff t u).mp (List.mem_of_getElem? hi)
  have hidx : t.vertices.idxOf u = i := by
    rw [← heq]
    exact (nodup_vertices t).idxOf_getElem i hi'
  have hbalance := idxOf_vertexContour_add_length t u hu
  rw [hidx] at hbalance
  have hfirst : t.vertexContour.idxOf u = 2 * i - u.length := by omega
  have hlt := List.idxOf_lt_length_of_mem ((mem_vertexContour_iff t u).mpr hu)
  change t.vertexContour.findIdx? (fun v => v == u) = some (2 * i - u.length)
  apply List.findIdx?_eq_some_iff_findIdx_eq.mpr
  constructor
  · rw [← hfirst]
    exact hlt
  · exact hfirst

/-- At the first visit to a DFS vertex, the height contour records its depth. -/
theorem getElem?_contour_first_visit {t : PlaneTree} {i : ℕ} {u : List ℕ}
    (hi : t.vertices[i]? = some u) :
    t.contour[2 * i - u.length]? = some u.length := by
  obtain ⟨hb, heq, _⟩ := List.idxOf?_eq_some_iff.mp
    (idxOf?_vertexContour_of_getElem?_vertices hi)
  have hv : t.vertexContour[2 * i - u.length]? = some u :=
    List.getElem?_eq_some_iff.mpr ⟨hb, heq⟩
  rw [← map_length_vertexContour, List.getElem?_map, hv]
  rfl

end BGW.PlaneTree
