/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

import BGW.Probability.WeakConvergence
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Order.Disjointed

/-!
# Continuity partitions for Skorokhod representation

A separable metric space admits countable Borel partitions of arbitrarily small mesh whose
cells have null frontier for a prescribed finite measure. These are the spatial partitions
in Billingsley's proof of the representation theorem.
-/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology

namespace BGW.Probability

private theorem exists_null_frontier_ball {S : Type*} [PseudoMetricSpace S]
    [MeasurableSpace S] [OpensMeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    (x : S) {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Ioo a b, μ (frontier (Metric.ball x r)) = 0 := by
  have hdisj : Pairwise (Function.onFun Disjoint fun r : ℝ =>
      frontier (Metric.ball x r)) := by
    intro r s hrs
    apply disjoint_left.mpr
    intro y hyr hys
    have hr := Metric.frontier_ball_subset_sphere hyr
    have hs := Metric.frontier_ball_subset_sphere hys
    exact hrs ((Metric.mem_sphere.mp hr).symm.trans (Metric.mem_sphere.mp hs))
  have hc := countable_setOf_measure_frontier_ne_zero μ hdisj
  by_contra! h
  have hsub : Ioo a b ⊆ {r | μ (frontier (Metric.ball x r)) ≠ 0} := by
    intro r hr
    exact h r hr
  exact (not_le.mpr hab) (Cardinal.Real.Ioo_countable_iff.mp (hc.mono hsub))

private theorem null_frontier_sdiff {S : Type*} [TopologicalSpace S]
    [MeasurableSpace S] {μ : Measure S} {A B : Set S}
    (hA : μ (frontier A) = 0) (hB : μ (frontier B) = 0) :
    μ (frontier (A \ B)) = 0 := by
  rw [sdiff_eq]
  exact null_frontier_inter hA (by simpa only [frontier_compl] using hB)

/-- A finite Borel measure on a nonempty separable metric space admits a countable Borel
partition of arbitrarily small mesh, all of whose cells have null frontier. Empty cells are
permitted; the covering and disjointness statements are exact, rather than almost everywhere. -/
theorem exists_continuity_partition {S : Type*} [PseudoMetricSpace S]
    [SeparableSpace S] [Nonempty S] [MeasurableSpace S] [OpensMeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℕ → Set S,
      (∀ j, MeasurableSet (A j)) ∧ Pairwise (Function.onFun Disjoint A) ∧
      (⋃ j, A j) = univ ∧ (∀ j, μ (frontier (A j)) = 0) ∧
      ∀ j, ∀ x ∈ A j, ∀ y ∈ A j, dist x y < ε := by
  classical
  let d := TopologicalSpace.denseSeq S
  obtain ⟨r, hr, hnull⟩ : ∃ r : ℕ → ℝ,
      (∀ j, r j ∈ Ioo (ε / 4) (ε / 2)) ∧
      ∀ j, μ (frontier (Metric.ball (d j) (r j))) = 0 := by
    have h (j : ℕ) := exists_null_frontier_ball μ (d j)
      (show ε / 4 < ε / 2 by linarith)
    choose r hr hnull using h
    exact ⟨r, hr, hnull⟩
  let B : ℕ → Set S := fun j => Metric.ball (d j) (r j)
  have hB : ∀ j, MeasurableSet (B j) := fun _ => Metric.isOpen_ball.measurableSet
  have hcover : (⋃ j, B j) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨j, hj⟩ := (TopologicalSpace.denseRange_denseSeq S).exists_dist_lt x
      (show 0 < ε / 4 by positivity)
    exact mem_iUnion.mpr ⟨j, hj.trans (hr j).1⟩
  refine ⟨disjointed B, ?_, disjoint_disjointed B, ?_, ?_, ?_⟩
  · intro j
    exact disjointedRec (fun {t i} ht => ht.diff (hB i)) (hB j)
  · rw [iUnion_disjointed, hcover]
  · intro j
    exact disjointedRec (f := B) (p := fun t => μ (frontier t) = 0)
      (fun {t i} ht => null_frontier_sdiff ht (hnull i)) (hnull j)
  · intro j x hx y hy
    have hxB : dist x (d j) < r j := disjointed_subset B j hx
    have hyB : dist y (d j) < r j := disjointed_subset B j hy
    calc
      dist x y ≤ dist x (d j) + dist y (d j) := dist_triangle_right _ _ _
      _ < ε := by linarith [(hr j).2]

end BGW.Probability
