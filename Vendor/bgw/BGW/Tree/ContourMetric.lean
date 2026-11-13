/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.ContourVertices
import Mathlib.Data.List.Indexes

/-!
# Common ancestors along contour intervals

Between the first contour visits to two DFS vertices, the contour visits their
longest common prefix and stays among its descendants. Consequently the least
discrete height on that interval is the depth of their lowest common ancestor.

The proof works with the existing address lists. Each child contributes one
contiguous block and distinct child blocks are separated by a root visit. The
internal induction applies to arbitrary contour visits, including repeated visits
to the same address; the public statements use the established first-visit times.
-/

@[expose] public section

namespace BGW.PlaneTree

private def LcaIntervals (cs : List (List ℕ)) : Prop :=
  ∀ (a b : ℕ) (u v : List ℕ), cs[a]? = some u → cs[b]? = some v → a ≤ b →
    (∃ k, a ≤ k ∧ k ≤ b ∧ cs[k]? = some (lca u v)) ∧
      ∀ (k : ℕ) (w : List ℕ), a ≤ k → k ≤ b → cs[k]? = some w → lca u v <+: w

private theorem lcaIntervals_nil : LcaIntervals [] := by
  intro a b u v ha
  simp at ha

private theorem lcaIntervals_cons_root {cs : List (List ℕ)} (hcs : LcaIntervals cs) :
    LcaIntervals ([] :: cs) := by
  intro a b u v ha hb hab
  cases a with
  | zero =>
    have hu : [] = u := by simpa using ha
    subst u
    constructor
    · exact ⟨0, le_rfl, hab, by simp⟩
    · intro k w _ _ _
      simp
  | succ a =>
    cases b with
    | zero => omega
    | succ b =>
      simp only [List.getElem?_cons_succ] at ha hb
      obtain ⟨⟨k, hak, hkb, hk⟩, hp⟩ := hcs a b u v ha hb (by omega)
      constructor
      · exact ⟨k + 1, by omega, by omega, by simpa using hk⟩
      · intro k w hak hkb hkw
        cases k with
        | zero => omega
        | succ k =>
          exact hp k w (by omega) (by omega) (by simpa using hkw)

private theorem lcaIntervals_map_cons {cs : List (List ℕ)} (hcs : LcaIntervals cs)
    (j : ℕ) : LcaIntervals (cs.map (List.cons j)) := by
  intro a b u v ha hb hab
  rw [List.getElem?_map] at ha hb
  obtain ⟨u', hau', hueq⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨v', hbv', hveq⟩ := Option.map_eq_some_iff.mp hb
  subst u
  subst v
  have hlca : lca (j :: u') (j :: v') = j :: lca u' v' := by simp [lca]
  rw [hlca]
  obtain ⟨⟨k, hak, hkb, hk⟩, hp⟩ := hcs a b u' v' hau' hbv' hab
  constructor
  · refine ⟨k, hak, hkb, ?_⟩
    rw [List.getElem?_map, hk]
    rfl
  · intro k w hak hkb hkw
    rw [List.getElem?_map] at hkw
    obtain ⟨w', hkw', hweq⟩ := Option.map_eq_some_iff.mp hkw
    subst w
    exact List.cons_prefix_cons.mpr ⟨rfl, hp k w' hak hkb hkw'⟩

/-- Concatenate blocks whose common ancestors across the join are the root. -/
private theorem lcaIntervals_append {xs ys : List (List ℕ)}
    (hxs : LcaIntervals xs) (hys : LcaIntervals ys) (hy0 : ys[0]? = some [])
    (hsep : ∀ u ∈ xs, ∀ v ∈ ys, lca u v = []) : LcaIntervals (xs ++ ys) := by
  intro a b u v ha hb hab
  by_cases hbL : b < xs.length
  · have haL : a < xs.length := by omega
    rw [List.getElem?_append_left haL] at ha
    rw [List.getElem?_append_left hbL] at hb
    obtain ⟨⟨k, hak, hkb, hk⟩, hp⟩ := hxs a b u v ha hb hab
    constructor
    · refine ⟨k, hak, hkb, ?_⟩
      rw [List.getElem?_append_left (by omega)]
      exact hk
    · intro k w hak hkb hkw
      rw [List.getElem?_append_left (by omega)] at hkw
      exact hp k w hak hkb hkw
  · have hbR : xs.length ≤ b := by omega
    rw [List.getElem?_append_right hbR] at hb
    by_cases haL : a < xs.length
    · rw [List.getElem?_append_left haL] at ha
      have huv : lca u v = [] :=
        hsep u (List.mem_of_getElem? ha) v (List.mem_of_getElem? hb)
      rw [huv]
      constructor
      · refine ⟨xs.length, by omega, hbR, ?_⟩
        rw [List.getElem?_append_right le_rfl, Nat.sub_self]
        exact hy0
      · intro k w _ _ _
        exact List.nil_prefix
    · have haR : xs.length ≤ a := by omega
      rw [List.getElem?_append_right haR] at ha
      obtain ⟨⟨k, hak, hkb, hk⟩, hp⟩ :=
        hys (a - xs.length) (b - xs.length) u v ha hb (by omega)
      constructor
      · refine ⟨xs.length + k, by omega, by omega, ?_⟩
        rw [List.getElem?_append_right (by omega)]
        simpa using hk
      · intro k w hak hkb hkw
        rw [List.getElem?_append_right (by omega)] at hkw
        exact hp (k - xs.length) w (by omega) (by omega) hkw

private theorem lcaIntervals_blocks (cs : List (List (List ℕ)))
    (hcs : ∀ c ∈ cs, LcaIntervals c) (f : ℕ → ℕ) (hf : Function.Injective f) :
    LcaIntervals
      ([] :: (cs.mapIdx fun i c => c.map (List.cons (f i)) ++ [[]]).flatten) := by
  revert hcs f
  induction cs with
  | nil =>
    intro _ f _
    exact lcaIntervals_cons_root lcaIntervals_nil
  | cons c cs ih =>
    intro hcs f hf
    have hf' : Function.Injective (fun i => f (i + 1)) := by
      intro i j hij
      have h := hf hij
      omega
    have htail := ih (fun d hd => hcs d (List.mem_cons_of_mem c hd))
      (fun i => f (i + 1)) hf'
    have hprefix := lcaIntervals_cons_root
      (lcaIntervals_map_cons (hcs c List.mem_cons_self) (f 0))
    simp only [List.mapIdx_cons, List.flatten_cons, List.append_assoc]
    change LcaIntervals (([] :: c.map (List.cons (f 0))) ++
      ([] :: (cs.mapIdx fun i d => d.map (List.cons (f (i + 1))) ++ [[]]).flatten))
    apply lcaIntervals_append hprefix htail rfl
    intro u hu v hv
    rcases List.mem_cons.mp hu with rfl | hu
    · exact lca_nil_left v
    · obtain ⟨u, _, rfl⟩ := List.mem_map.mp hu
      rcases List.mem_cons.mp hv with rfl | hv
      · exact lca_nil_right _
      · obtain ⟨block, hblock, hv⟩ := List.mem_flatten.mp hv
        obtain ⟨i, _, rfl⟩ := List.mem_mapIdx.mp hblock
        rcases List.mem_append.mp hv with hv | hv
        · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
          have hne : f 0 ≠ f (i + 1) := by
            intro heq
            have h := hf heq
            omega
          simp [lca, hne]
        · have hv' : v = [] := by simpa using hv
          subst v
          exact lca_nil_right _

private theorem lcaIntervals_vertexContour (t : PlaneTree) :
    LcaIntervals t.vertexContour := by
  induction t with
  | node ts ih =>
    rw [vertexContour_node]
    have hcs : ∀ c ∈ ts.map vertexContour, LcaIntervals c := by
      intro c hc
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
      exact ih s hs
    have h := lcaIntervals_blocks _ hcs id Function.injective_id
    simpa only [List.mapIdx_eq_ofFn, List.length_map, List.get_eq_getElem,
      List.getElem_map, Fin.val_cast, id_eq] using h

private theorem getElem?_vertexContour_first_visit {t : PlaneTree} {i : ℕ} {u : List ℕ}
    (hi : t.vertices[i]? = some u) :
    t.vertexContour[2 * i - u.length]? = some u := by
  obtain ⟨hb, heq, _⟩ := List.idxOf?_eq_some_iff.mp
    (idxOf?_vertexContour_of_getElem?_vertices hi)
  exact List.getElem?_eq_some_iff.mpr ⟨hb, heq⟩

/-- Between any two actual contour visits, the contour reaches their LCA. -/
theorem lca_visit_between_contour_visits {t : PlaneTree} {a b : ℕ} {u v : List ℕ}
    (ha : t.vertexContour[a]? = some u) (hb : t.vertexContour[b]? = some v) :
    ∃ k, min a b ≤ k ∧ k ≤ max a b ∧ t.vertexContour[k]? = some (lca u v) := by
  rcases le_total a b with hab | hba
  · have h := (lcaIntervals_vertexContour t) a b u v ha hb hab
    simpa only [min_eq_left hab, max_eq_right hab] using h.1
  · have h := (lcaIntervals_vertexContour t) b a v u hb ha hba
    simpa only [min_eq_right hba, max_eq_left hba, lca_comm v u] using h.1

/-- Between any two actual visits, every address remains below their common ancestor. -/
theorem lca_prefix_vertexContour_between_visits {t : PlaneTree} {a b k : ℕ}
    {u v w : List ℕ} (ha : t.vertexContour[a]? = some u)
    (hb : t.vertexContour[b]? = some v) (hlo : min a b ≤ k) (hhi : k ≤ max a b)
    (hkw : t.vertexContour[k]? = some w) : lca u v <+: w := by
  rcases le_total a b with hab | hba
  · have h := (lcaIntervals_vertexContour t) a b u v ha hb hab
    exact h.2 k w (by simpa only [min_eq_left hab] using hlo)
      (by simpa only [max_eq_right hab] using hhi) hkw
  · have h := (lcaIntervals_vertexContour t) b a v u hb ha hba
    rw [lca_comm u v]
    exact h.2 k w (by simpa only [min_eq_right hba] using hlo)
      (by simpa only [max_eq_left hba] using hhi) hkw

/-- The contour reaches the LCA between the first visits to two DFS vertices. -/
theorem lca_visit_between_first_visits {t : PlaneTree} {i j : ℕ} {u v : List ℕ}
    (hi : t.vertices[i]? = some u) (hj : t.vertices[j]? = some v) :
    ∃ k, min (2 * i - u.length) (2 * j - v.length) ≤ k ∧
      k ≤ max (2 * i - u.length) (2 * j - v.length) ∧
      t.vertexContour[k]? = some (lca u v) := by
  have ha := getElem?_vertexContour_first_visit hi
  have hb := getElem?_vertexContour_first_visit hj
  rcases le_total (2 * i - u.length) (2 * j - v.length) with hab | hba
  · have h := (lcaIntervals_vertexContour t) _ _ u v ha hb hab
    simpa only [min_eq_left hab, max_eq_right hab] using h.1
  · have h := (lcaIntervals_vertexContour t) _ _ v u hb ha hba
    simpa only [min_eq_right hba, max_eq_left hba, lca_comm v u] using h.1

/-- Every visit between these first visits remains in the subtree of their LCA. -/
theorem lca_prefix_vertexContour_between_first_visits {t : PlaneTree} {i j k : ℕ}
    {u v w : List ℕ} (hi : t.vertices[i]? = some u) (hj : t.vertices[j]? = some v)
    (hlo : min (2 * i - u.length) (2 * j - v.length) ≤ k)
    (hhi : k ≤ max (2 * i - u.length) (2 * j - v.length))
    (hkw : t.vertexContour[k]? = some w) : lca u v <+: w := by
  have ha := getElem?_vertexContour_first_visit hi
  have hb := getElem?_vertexContour_first_visit hj
  rcases le_total (2 * i - u.length) (2 * j - v.length) with hab | hba
  · have h := (lcaIntervals_vertexContour t) _ _ u v ha hb hab
    exact h.2 k w (by simpa only [min_eq_left hab] using hlo)
      (by simpa only [max_eq_right hab] using hhi) hkw
  · have h := (lcaIntervals_vertexContour t) _ _ v u hb ha hba
    rw [lca_comm u v]
    exact h.2 k w (by simpa only [min_eq_right hba] using hlo)
      (by simpa only [max_eq_left hba] using hhi) hkw

end BGW.PlaneTree
