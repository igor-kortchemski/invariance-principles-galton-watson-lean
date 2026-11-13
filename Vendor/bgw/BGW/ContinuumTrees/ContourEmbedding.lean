/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.ContourCoding
public import BGW.ContinuumTrees.FiniteTree
public import BGW.ContinuumTrees.CodingMeasure
public import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Isometric embedding of vertices in their contour-coded tree

A vertex is represented by its first contour visit. The minimum between two
such visits is their common ancestor's depth, so the coding distance agrees
with the graph metric. The embedding preserves the root. Its mass comparison
with the contour's Lebesgue pushforward is a separate result.
-/

@[expose] public section

open BGW.PlaneTree

namespace BGW.ContinuumTrees.FiniteTree

private theorem dfs_lookup (t : PlaneTree) (u : Vertex t) :
    t.vertices[t.vertices.idxOf u.val]? = some u.val :=
  List.getElem?_idxOf ((mem_vertices_iff t u.val).mpr u.property)

/-- Time of the first visit to a present vertex, in the normalized contour traversal. -/
noncomputable def vertexTime (t : PlaneTree) (u : Vertex t) : unitInterval :=
  t.contourTime ⟨2 * t.vertices.idxOf u.val - u.val.length, by
    have h := getElem?_contour_first_visit
      (List.getElem?_idxOf ((mem_vertices_iff t u.val).mpr u.property))
    exact (List.getElem?_eq_some_iff.mp h).1⟩

/-- The continuous contour at a vertex's first visit records its depth. -/
theorem contourFunction_vertexTime (t : PlaneTree) (u : Vertex t) :
    t.contourFunction (vertexTime t u) = (u.val.length : ℝ) := by
  rw [vertexTime, contourFunction_contourTime]
  obtain ⟨_, hval⟩ := List.getElem?_eq_some_iff.mp (getElem?_contour_first_visit (dfs_lookup t u))
  exact congrArg (fun k : ℕ => (k : ℝ)) hval

/-- The image of a vertex in the real tree coded by the interpolated contour. -/
noncomputable def vertexEmbedding (t : PlaneTree) (u : Vertex t) :
    Coding.Space t.contourFunction :=
  Coding.projection t.contourFunction (vertexTime t u)

/-- The contour-coded distance between vertices is exactly their existing graph metric. -/
theorem isometry_vertexEmbedding (t : PlaneTree) : Isometry (vertexEmbedding t) := by
  apply Isometry.of_dist_eq
  intro u v
  let a : Fin t.contour.length := ⟨2 * t.vertices.idxOf u.val - u.val.length,
    (List.getElem?_eq_some_iff.mp (getElem?_contour_first_visit (dfs_lookup t u))).1⟩
  let b : Fin t.contour.length := ⟨2 * t.vertices.idxOf v.val - v.val.length,
    (List.getElem?_eq_some_iff.mp (getElem?_contour_first_visit (dfs_lookup t v))).1⟩
  change Coding.codingDist t.contourFunction (t.contourTime a) (t.contourTime b) =
    (graphDist u.val v.val : ℝ)
  exact ContourCoding.codingDist_first_visits (dfs_lookup t u) (dfs_lookup t v) a b rfl rfl

@[simp] theorem vertexTime_root (t : PlaneTree) : vertexTime t (root t) = 0 := by
  have hidx : t.vertices.idxOf ([] : List ℕ) = 0 := by
    cases t with
    | node ts => simp
  apply Subtype.ext
  simp [vertexTime, root, contourTime, hidx]

/-- The embedding sends the finite tree's root to the coding root. -/
@[simp] theorem vertexEmbedding_root (t : PlaneTree) :
    vertexEmbedding t (root t) = Coding.root t.contourFunction := by
  rw [vertexEmbedding, vertexTime_root, Coding.root]

/-- The addition-only relation between first-visit time, depth and DFS index. -/
theorem duration_mul_vertexTime_add_depth (t : PlaneTree) (u : Vertex t) :
    ((t.contour.length - 1 : ℕ) : ℝ) * (vertexTime t u : ℝ) + (u.val.length : ℝ) =
      2 * (t.vertices.idxOf u.val : ℝ) := by
  have hb := idxOf_vertexContour_add_length t u.val u.property
  have hnat : 2 * t.vertices.idxOf u.val - u.val.length + u.val.length =
      2 * t.vertices.idxOf u.val := by omega
  rw [vertexTime, duration_mul_contourTime]
  exact_mod_cast hnat

/-- First-visit time is close to normalized DFS rank when depth is small relative to size. -/
theorem abs_vertexTime_sub_dfsTime_le (t : PlaneTree) (hn : 2 ≤ t.size) (u : Vertex t) :
    |(vertexTime t u : ℝ) - (t.vertices.idxOf u.val : ℝ) / (t.size : ℝ)| ≤
      (u.val.length : ℝ) / (2 * ((t.size - 1 : ℕ) : ℝ)) + 1 / (t.size : ℝ) := by
  have hnR : (0 : ℝ) < t.size := by exact_mod_cast (show 0 < t.size by omega)
  have hmR : (0 : ℝ) < ((t.size - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < t.size - 1 by omega)
  have hmn : ((t.size - 1 : ℕ) : ℝ) + 1 = (t.size : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (show 1 ≤ t.size by omega)
  have hi : t.vertices.idxOf u.val < t.size := by
    simpa only [length_vertices] using
      List.idxOf_lt_length_of_mem ((mem_vertices_iff t u.val).mpr u.property)
  have hiR : (t.vertices.idxOf u.val : ℝ) ≤ ((t.size - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show t.vertices.idxOf u.val ≤ t.size - 1 by omega)
  have hduration : ((t.contour.length - 1 : ℕ) : ℝ) =
      2 * ((t.size - 1 : ℕ) : ℝ) := by
    rw [length_contour]
    simp only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_ofNat]
  have hb := duration_mul_vertexTime_add_depth t u
  rw [hduration] at hb
  have htau : (vertexTime t u : ℝ) =
      (t.vertices.idxOf u.val : ℝ) / ((t.size - 1 : ℕ) : ℝ) -
        (u.val.length : ℝ) / (2 * ((t.size - 1 : ℕ) : ℝ)) := by
    field_simp
    nlinarith only [hb]
  have heq : (vertexTime t u : ℝ) - (t.vertices.idxOf u.val : ℝ) / (t.size : ℝ) =
      (t.vertices.idxOf u.val : ℝ) / ((t.size : ℝ) * ((t.size - 1 : ℕ) : ℝ)) -
        (u.val.length : ℝ) / (2 * ((t.size - 1 : ℕ) : ℝ)) := by
    rw [htau]
    field_simp
    nlinarith only [congrArg (fun x : ℝ => (t.vertices.idxOf u.val : ℝ) * x) hmn]
  have hfrac : (t.vertices.idxOf u.val : ℝ) /
      ((t.size : ℝ) * ((t.size - 1 : ℕ) : ℝ)) ≤ 1 / (t.size : ℝ) := by
    rw [div_le_div_iff₀ (mul_pos hnR hmR) hnR]
    nlinarith only [mul_le_mul_of_nonneg_left hiR hnR.le]
  have hzero : 0 ≤ (t.vertices.idxOf u.val : ℝ) /
      ((t.size : ℝ) * ((t.size - 1 : ℕ) : ℝ)) := by positivity
  have hdepth : 0 ≤ (u.val.length : ℝ) / (2 * ((t.size - 1 : ℕ) : ℝ)) := by positivity
  have hone : 0 ≤ 1 / (t.size : ℝ) := by positivity
  rw [heq]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end BGW.ContinuumTrees.FiniteTree
