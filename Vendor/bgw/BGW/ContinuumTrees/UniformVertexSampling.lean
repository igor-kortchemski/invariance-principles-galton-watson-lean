/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.ContourEmbedding
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform sampling of vertices by DFS rank

A time in the unit interval selects DFS rank `min (floor (size * time)) (size - 1)`.
The final time therefore selects the last vertex. All earlier rank cells are
half-open intervals of length `1 / size`; the final cell is closed at one and
has the same volume. The pushforward of the actual interval volume is exactly
the uniform measure on all vertices, including roots and leaves.
-/

@[expose] public section

open MeasureTheory
open BGW.PlaneTree
open scoped ENNReal

namespace BGW.ContinuumTrees.FiniteTree

private noncomputable def sampleRank (t : PlaneTree) (s : unitInterval) : ℕ :=
  min (Nat.floor ((t.size : ℝ) * (s : ℝ))) (t.size - 1)

private theorem sampleRank_lt (t : PlaneTree) (s : unitInterval) :
    sampleRank t s < t.vertices.length := by
  rw [length_vertices]
  have hp := size_pos t
  have h := min_le_right (Nat.floor ((t.size : ℝ) * (s : ℝ))) (t.size - 1)
  change min (Nat.floor ((t.size : ℝ) * (s : ℝ))) (t.size - 1) < t.size
  omega

/-- Select a DFS vertex by an interval time, with the final time clamped to the last rank. -/
noncomputable def sampleVertex (t : PlaneTree) (s : unitInterval) : Vertex t := by
  let r := min (Nat.floor ((t.size : ℝ) * (s : ℝ))) (t.size - 1)
  have hr : r < t.vertices.length := by
    rw [length_vertices]
    have hp := size_pos t
    have h := min_le_right (Nat.floor ((t.size : ℝ) * (s : ℝ))) (t.size - 1)
    dsimp only [r]
    omega
  exact ⟨t.vertices[r]'hr, (mem_vertices_iff t _).mp (List.getElem_mem hr)⟩

private theorem idxOf_sampleVertex (t : PlaneTree) (s : unitInterval) :
    t.vertices.idxOf (sampleVertex t s).val = sampleRank t s := by
  change t.vertices.idxOf (t.vertices[sampleRank t s]'(sampleRank_lt t s)) = sampleRank t s
  exact (nodup_vertices t).idxOf_getElem _ _

private theorem sampleVertex_eq_iff (t : PlaneTree) (s : unitInterval) (u : Vertex t) :
    sampleVertex t s = u ↔ sampleRank t s = t.vertices.idxOf u.val := by
  constructor
  · intro h
    have h' := congrArg (fun v : Vertex t => t.vertices.idxOf v.val) h
    simpa only [idxOf_sampleVertex] using h'
  · intro h
    apply Subtype.ext
    change t.vertices[sampleRank t s]'(sampleRank_lt t s) = u.val
    have hu := List.idxOf_lt_length_of_mem ((mem_vertices_iff t u.val).mpr u.property)
    simpa only [h] using (List.getElem_idxOf hu)

private theorem preimage_sampleVertex_singleton (t : PlaneTree) (u : Vertex t) :
    sampleVertex t ⁻¹' {u} = {s | sampleRank t s = t.vertices.idxOf u.val} := by
  ext s
  exact sampleVertex_eq_iff t s u

private theorem measurable_sampleRank (t : PlaneTree) : Measurable (sampleRank t) := by
  have h : Measurable (fun s : unitInterval => (t.size : ℝ) * (s : ℝ)) :=
    (continuous_const.mul continuous_subtype_val).measurable
  exact h.nat_floor.min measurable_const

/-- The sampler is measurable into the existing Borel space of vertices. -/
theorem measurable_sampleVertex (t : PlaneTree) : Measurable (sampleVertex t) := by
  apply measurable_to_countable'
  intro u
  rw [preimage_sampleVertex_singleton]
  exact (measurable_sampleRank t) (measurableSet_singleton _)

private noncomputable def rankTime (t : PlaneTree) (i : ℕ) (hi : i ≤ t.size) : unitInterval :=
  ⟨(i : ℝ) / (t.size : ℝ), by
    have hn : (0 : ℝ) < t.size := by exact_mod_cast size_pos t
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hn.le
    · apply (div_le_one₀ hn).mpr
      exact_mod_cast hi⟩

private theorem sampleRank_fiber_Ico (t : PlaneTree) (i : ℕ) (hi : i < t.size - 1) :
    {s : unitInterval | sampleRank t s = i} =
      Set.Ico (rankTime t i (by omega)) (rankTime t (i + 1) (by omega)) := by
  ext s
  have hn : (0 : ℝ) < t.size := by exact_mod_cast size_pos t
  have hx0 : 0 ≤ (t.size : ℝ) * (s : ℝ) := mul_nonneg hn.le s.property.1
  have hm : sampleRank t s = i ↔ Nat.floor ((t.size : ℝ) * (s : ℝ)) = i := by
    dsimp only [sampleRank]
    omega
  change sampleRank t s = i ↔
    (i : ℝ) / (t.size : ℝ) ≤ (s : ℝ) ∧
      (s : ℝ) < ((i + 1 : ℕ) : ℝ) / (t.size : ℝ)
  rw [hm, Nat.floor_eq_iff hx0, div_le_iff₀ hn, lt_div_iff₀ hn]
  simp only [Nat.cast_add, Nat.cast_one, mul_comm]

private theorem sampleRank_fiber_last (t : PlaneTree) :
    {s : unitInterval | sampleRank t s = t.size - 1} =
      Set.Icc (rankTime t (t.size - 1) (Nat.sub_le _ _)) 1 := by
  ext s
  have hn : (0 : ℝ) < t.size := by exact_mod_cast size_pos t
  have hx0 : 0 ≤ (t.size : ℝ) * (s : ℝ) := mul_nonneg hn.le s.property.1
  have hm : sampleRank t s = t.size - 1 ↔
      t.size - 1 ≤ Nat.floor ((t.size : ℝ) * (s : ℝ)) := by
    exact min_eq_right_iff
  change sampleRank t s = t.size - 1 ↔
    ((t.size - 1 : ℕ) : ℝ) / (t.size : ℝ) ≤ (s : ℝ) ∧ (s : ℝ) ≤ 1
  rw [hm, Nat.le_floor_iff hx0, div_le_iff₀ hn]
  constructor
  · intro h
    exact ⟨by simpa only [mul_comm] using h, s.property.2⟩
  · intro h
    simpa only [mul_comm] using h.1

private theorem volume_sampleRank_fiber (t : PlaneTree) (i : ℕ) (hi : i < t.size) :
    volume {s : unitInterval | sampleRank t s = i} = (t.size : ℝ≥0∞)⁻¹ := by
  have hn : (0 : ℝ) < t.size := by exact_mod_cast size_pos t
  by_cases hlast : i = t.size - 1
  · subst i
    rw [sampleRank_fiber_last, unitInterval.volume_Icc]
    change ENNReal.ofReal (1 - ((t.size - 1 : ℕ) : ℝ) / (t.size : ℝ)) = _
    have hm : ((t.size - 1 : ℕ) : ℝ) + 1 = (t.size : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel (show 1 ≤ t.size from size_pos t)
    have hlen : (1 : ℝ) - ((t.size - 1 : ℕ) : ℝ) / (t.size : ℝ) = 1 / (t.size : ℝ) := by
      field_simp
      linarith
    rw [hlen, ENNReal.ofReal_div_of_pos hn, ENNReal.ofReal_one,
      ENNReal.ofReal_natCast, one_div]
  · have hi' : i < t.size - 1 := by omega
    rw [sampleRank_fiber_Ico t i hi', unitInterval.volume_Ico]
    change ENNReal.ofReal (((i + 1 : ℕ) : ℝ) / (t.size : ℝ) -
      (i : ℝ) / (t.size : ℝ)) = _
    have hlen : ((i + 1 : ℕ) : ℝ) / (t.size : ℝ) -
        (i : ℝ) / (t.size : ℝ) = 1 / (t.size : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]
      ring
    rw [hlen, ENNReal.ofReal_div_of_pos hn, ENNReal.ofReal_one,
      ENNReal.ofReal_natCast, one_div]

/-- Interval volume pushes forward to exactly the uniform probability on all vertices. -/
theorem map_sampleVertex_volume (t : PlaneTree) :
    Measure.map (sampleVertex t) (volume : Measure unitInterval) =
      (mass t : Measure (Vertex t)) := by
  apply Measure.ext_of_singleton
  intro u
  rw [Measure.map_apply (measurable_sampleVertex t) (measurableSet_singleton u),
    preimage_sampleVertex_singleton, mass_singleton]
  apply volume_sampleRank_fiber
  simpa only [length_vertices] using
    List.idxOf_lt_length_of_mem ((mem_vertices_iff t u.val).mpr u.property)

/-- The first sampling time selects the root. -/
@[simp] theorem sampleVertex_zero (t : PlaneTree) : sampleVertex t 0 = root t := by
  apply (sampleVertex_eq_iff t 0 (root t)).mpr
  cases t with
  | node ts => simp [sampleRank, root]

/-- Every vertex is selected, at the time given by its DFS rank divided by tree size. -/
theorem sampleVertex_surjective (t : PlaneTree) : Function.Surjective (sampleVertex t) := by
  intro u
  let i := t.vertices.idxOf u.val
  have hi : i < t.size := by
    simpa only [length_vertices] using
      List.idxOf_lt_length_of_mem ((mem_vertices_iff t u.val).mpr u.property)
  refine ⟨rankTime t i hi.le, (sampleVertex_eq_iff t _ u).mpr ?_⟩
  change min (Nat.floor ((t.size : ℝ) * ((i : ℝ) / (t.size : ℝ)))) (t.size - 1) = i
  have hn : (t.size : ℝ) ≠ 0 := by exact_mod_cast (size_pos t).ne'
  rw [mul_div_cancel₀ _ hn, Nat.floor_natCast, min_eq_left (by omega)]

private theorem sampleRank_cell_bounds (t : PlaneTree) (s : unitInterval) :
    (sampleRank t s : ℝ) ≤ (t.size : ℝ) * (s : ℝ) ∧
      (t.size : ℝ) * (s : ℝ) ≤ (sampleRank t s : ℝ) + 1 := by
  have hn : (0 : ℝ) < t.size := by exact_mod_cast size_pos t
  have hx0 : 0 ≤ (t.size : ℝ) * (s : ℝ) := mul_nonneg hn.le s.property.1
  have hfloor : sampleRank t s ≤ Nat.floor ((t.size : ℝ) * (s : ℝ)) := min_le_left _ _
  constructor
  · exact (Nat.cast_le.mpr hfloor).trans (Nat.floor_le hx0)
  · by_cases hcap : Nat.floor ((t.size : ℝ) * (s : ℝ)) ≤ t.size - 1
    · have hr : sampleRank t s = Nat.floor ((t.size : ℝ) * (s : ℝ)) := min_eq_left hcap
      rw [hr]
      exact (Nat.lt_floor_add_one _).le
    · have hr : sampleRank t s = t.size - 1 := min_eq_right (by omega)
      rw [hr]
      have hm : ((t.size - 1 : ℕ) : ℝ) + 1 = (t.size : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel (show 1 ≤ t.size from size_pos t)
      rw [hm]
      have h := mul_le_mul_of_nonneg_left s.property.2 hn.le
      simpa only [mul_one] using h

private theorem abs_sampleRank_div_sub_time_le (t : PlaneTree) (s : unitInterval) :
    |(sampleRank t s : ℝ) / (t.size : ℝ) - (s : ℝ)| ≤ 1 / (t.size : ℝ) := by
  have hn : (0 : ℝ) < t.size := by exact_mod_cast size_pos t
  obtain ⟨hlo, hhi⟩ := sampleRank_cell_bounds t s
  have hleft : (sampleRank t s : ℝ) / (t.size : ℝ) ≤ (s : ℝ) := by
    apply (div_le_iff₀ hn).mpr
    simpa only [mul_comm] using hlo
  have hright : (s : ℝ) ≤ (sampleRank t s : ℝ) / (t.size : ℝ) +
      1 / (t.size : ℝ) := by
    rw [← add_div]
    apply (le_div_iff₀ hn).mpr
    simpa only [mul_comm] using hhi
  rw [abs_of_nonpos (sub_nonpos.mpr hleft)]
  linarith

/-- The sampled vertex's first-visit time stays uniformly close to its sampling time. -/
theorem abs_vertexTime_sampleVertex_sub_le (t : PlaneTree) (hn : 2 ≤ t.size)
    (s : unitInterval) :
    |(vertexTime t (sampleVertex t s) : ℝ) - (s : ℝ)| ≤
      ‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ)) + 2 / (t.size : ℝ) := by
  have hfirst := abs_vertexTime_sub_dfsTime_le t hn (sampleVertex t s)
  rw [idxOf_sampleVertex] at hfirst
  have hcell := abs_sampleRank_div_sub_time_le t s
  have hdepth := t.contourFunction.apply_le_norm (vertexTime t (sampleVertex t s))
  rw [contourFunction_vertexTime] at hdepth
  have hden : (0 : ℝ) ≤ 2 * ((t.size - 1 : ℕ) : ℝ) :=
    mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hdepthBound := div_le_div_of_nonneg_right hdepth hden
  calc
    |(vertexTime t (sampleVertex t s) : ℝ) - (s : ℝ)| ≤
        |(vertexTime t (sampleVertex t s) : ℝ) - (sampleRank t s : ℝ) / (t.size : ℝ)| +
          |(sampleRank t s : ℝ) / (t.size : ℝ) - (s : ℝ)| := abs_sub_le _ _ _
    _ ≤ ((sampleVertex t s).val.length : ℝ) / (2 * ((t.size - 1 : ℕ) : ℝ)) +
        1 / (t.size : ℝ) + 1 / (t.size : ℝ) := add_le_add hfirst hcell
    _ ≤ ‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ)) +
        1 / (t.size : ℝ) + 1 / (t.size : ℝ) := by linarith
    _ = ‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ)) + 2 / (t.size : ℝ) := by ring

end BGW.ContinuumTrees.FiniteTree
