/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.Geometry
public import BGW.MetricMeasure.RootedCompactMeasuredSpace
public import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Card

/-!
# Finite plane trees as rooted compact metric probability spaces

The carrier is the existing subtype `PlaneTree.Vertex t` of present addresses,
with its graph metric. Its Borel probability measure gives mass `1 / t.size`
to every vertex, including the root and all leaves. No measurable structure on
the type of plane trees or on all addresses is introduced.

This module only bundles the finite tree. Metric scaling and comparison with a
continuously coded tree are separate constructions.
-/

@[expose] public section

open MeasureTheory
open BGW.PlaneTree
open scoped ENNReal

namespace BGW.ContinuumTrees.FiniteTree

/-- Enumerate the existing vertex subtype using the DFS address list. -/
noncomputable instance vertexFintype (t : PlaneTree) : Fintype (Vertex t) :=
  Fintype.ofFinset t.vertices.toFinset (fun u => by
    change u ∈ t.vertices.toFinset ↔ t.IsVertex u
    simpa only [List.mem_toFinset] using mem_vertices_iff t u)

/-- Cardinality counts all vertex occurrences, including the root. -/
@[simp] theorem card_vertex (t : PlaneTree) : Fintype.card (Vertex t) = t.size := by
  let e : Vertex t ≃ t.vertices.toFinset :=
    { toFun := fun u => ⟨u.val, by
        simpa only [List.mem_toFinset] using (mem_vertices_iff t u.val).mpr u.property⟩
      invFun := fun u => ⟨u.val, (mem_vertices_iff t u.val).mp (by
        simpa only [List.mem_toFinset] using u.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    Fintype.card (Vertex t) = Fintype.card t.vertices.toFinset := Fintype.card_congr e
    _ = t.vertices.toFinset.card := Fintype.card_coe _
    _ = t.vertices.length := List.toFinset_card_of_nodup (nodup_vertices t)
    _ = t.size := length_vertices t

/-- The distinguished root address. -/
def root (t : PlaneTree) : Vertex t := ⟨[], isVertex_nil t⟩

instance vertexNonempty (t : PlaneTree) : Nonempty (Vertex t) := ⟨root t⟩

/-- Use the Borel structure of the existing graph metric. -/
noncomputable instance vertexMeasurableSpace (t : PlaneTree) : MeasurableSpace (Vertex t) :=
  borel (Vertex t)

instance vertexBorelSpace (t : PlaneTree) : BorelSpace (Vertex t) := ⟨rfl⟩

/-- Uniform probability on every vertex of the finite tree. -/
noncomputable def mass (t : PlaneTree) : ProbabilityMeasure (Vertex t) := by
  classical
  refine ⟨Measure.uniformOfFinset Finset.univ, ⟨?_⟩⟩
  rw [Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true, Finset.card_univ, card_vertex]
  exact ENNReal.div_self
    (by exact_mod_cast (size_pos t).ne') (ENNReal.natCast_ne_top t.size)

@[simp] theorem coe_mass (t : PlaneTree) :
    (mass t : Measure (Vertex t)) = Measure.uniformOfFinset Finset.univ := rfl

/-- Each present vertex has the same positive mass, regardless of its degree. -/
theorem mass_singleton (t : PlaneTree) (u : Vertex t) :
    (mass t : Measure (Vertex t)) {u} = (t.size : ℝ≥0∞)⁻¹ := by
  rw [coe_mass, Measure.uniformOfFinset_apply_singleton]
  simp only [Finset.mem_univ, ite_true, Finset.card_univ, card_vertex]

/-- The whole finite vertex space with its graph metric and uniform probability. -/
noncomputable def compactMeasuredSpace (t : PlaneTree) :
    BGW.MetricMeasure.CompactMeasuredSpace :=
  BGW.MetricMeasure.CompactMeasuredSpace.of (Vertex t) (mass t)

/-- The same measured vertex space, rooted at the empty address. -/
noncomputable def rootedCompactMeasuredSpace (t : PlaneTree) :
    BGW.MetricMeasure.RootedCompactMeasuredSpace where
  space := compactMeasuredSpace t
  root := root t

end BGW.ContinuumTrees.FiniteTree
