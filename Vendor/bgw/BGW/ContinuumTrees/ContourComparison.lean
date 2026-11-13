/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.UniformVertexSampling
public import BGW.ContinuumTrees.CodingScaling
public import BGW.MetricMeasure.RootedCommonSource
import Mathlib.Tactic.Linarith

/-!
# Comparing uniform vertex mass with contour mass

The uniform DFS sampler and the contour projection have the same probability
source: Lebesgue measure on the unit interval. A sampled vertex is represented
by its first contour visit. The time discrepancy is bounded by the contour
height divided by twice the number of edges, plus twice the inverse number
of vertices.

An oscillation bound on the spatially scaled contour controls the coding
distance between these paired times. The resulting common-source
correspondence has distortion at most four oscillation errors, so its rooted
GHP distance is at most six errors. The finite measure is uniform on all
vertices, including the root and leaves; the contour measure is the actual
Lebesgue pushforward. This is a deterministic comparison, not an invariance
principle or a convergence assertion.
-/

@[expose] public section

open MeasureTheory
open BGW.MetricMeasure
open BGW.PlaneTree

namespace BGW.ContinuumTrees

namespace Coding

/-- A modulus of oscillation controls coding distance between nearby times. -/
theorem codingDist_le_of_oscillation (g : C(unitInterval, ℝ))
    {s t : unitInterval} {δ ε : ℝ}
    (hst : |(s : ℝ) - (t : ℝ)| ≤ δ)
    (hosc : ∀ a b : unitInterval,
      |(a : ℝ) - (b : ℝ)| ≤ δ → |g a - g b| ≤ ε) :
    codingDist g s t ≤ 2 * ε := by
  obtain ⟨r, hr, hmin⟩ := exists_intervalMin g s t
  have hnear : |(s : ℝ) - (r : ℝ)| ≤ δ ∧ |(t : ℝ) - (r : ℝ)| ≤ δ := by
    obtain ⟨hst₁, hst₂⟩ := abs_le.mp hst
    rcases Set.mem_uIcc.mp hr with h | h
    · have hsr : (s : ℝ) ≤ (r : ℝ) := h.1
      have hrt : (r : ℝ) ≤ (t : ℝ) := h.2
      constructor <;> apply abs_le.mpr <;> constructor <;> linarith
    · have htr : (t : ℝ) ≤ (r : ℝ) := h.1
      have hrs : (r : ℝ) ≤ (s : ℝ) := h.2
      constructor <;> apply abs_le.mpr <;> constructor <;> linarith
  have hs := (abs_le.mp (hosc s r hnear.1)).2
  have ht := (abs_le.mp (hosc t r hnear.2)).2
  rw [codingDist, hmin]
  linarith

end Coding

namespace FiniteTree

/-- Uniform vertex mass and contour mass are close when the scaled contour has small
oscillation on the deterministic first-visit time discrepancy. -/
theorem rooted_distance_scale_contour_le (t : PlaneTree) (hn : 2 ≤ t.size)
    (factor : ℝ) (hfactor : 0 < factor) {ε : ℝ} (hε : 0 < ε)
    (hosc : ∀ s r : unitInterval,
      |(s : ℝ) - (r : ℝ)| ≤
        ‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ)) + 2 / (t.size : ℝ) →
      |(factor • t.contourFunction) s - (factor • t.contourFunction) r| ≤ ε) :
    RootedCompactMeasuredSpace.distance
      (RootedCompactMeasuredSpace.scale factor hfactor (rootedCompactMeasuredSpace t))
      (Coding.rootedCompactMeasuredSpace (factor • t.contourFunction)) ≤ 6 * ε := by
  let c : Set.Ioi (0 : ℝ) := ⟨factor, hfactor⟩
  let g : C(unitInterval, ℝ) := factor • t.contourFunction
  let p : unitInterval → ScaledMetric c (Vertex t) :=
    ScaledMetric.toScaled c ∘ sampleVertex t
  let q : unitInterval → Coding.Space g := Coding.projection g
  have hp : Measurable p := (ScaledMetric.measurable_toScaled c).comp (measurable_sampleVertex t)
  have hq : Measurable q := Coding.measurable_projection g
  have hps : Function.Surjective p :=
    (ScaledMetric.equiv c (Vertex t)).surjective.comp (sampleVertex_surjective t)
  have hqs : Function.Surjective q := Coding.projection_surjective g
  have hnear (s : unitInterval) :
      dist (q (vertexTime t (sampleVertex t s))) (q s) ≤ 2 * ε := by
    rw [Coding.dist_projection]
    exact Coding.codingDist_le_of_oscillation g
      (abs_vertexTime_sampleVertex_sub_le t hn s) hosc
  have hvertices (u v : Vertex t) :
      dist (ScaledMetric.toScaled c u) (ScaledMetric.toScaled c v) =
        dist (q (vertexTime t u)) (q (vertexTime t v)) := by
    rw [ScaledMetric.dist_toScaled, Coding.dist_projection,
      Coding.codingDist_smul t.contourFunction factor hfactor.le]
    have he := (isometry_vertexEmbedding t).dist_eq u v
    change Coding.codingDist t.contourFunction (vertexTime t u) (vertexTime t v) =
      dist u v at he
    rw [he]
  have hdis (s r : unitInterval) :
      |dist (p s) (p r) - dist (q s) (q r)| ≤ 2 * (2 * ε) := by
    change |dist (ScaledMetric.toScaled c (sampleVertex t s))
      (ScaledMetric.toScaled c (sampleVertex t r)) - dist (q s) (q r)| ≤ _
    rw [hvertices]
    have hd := dist_dist_dist_le
      (q (vertexTime t (sampleVertex t s))) (q (vertexTime t (sampleVertex t r))) (q s) (q r)
    rw [Real.dist_eq] at hd
    have hs := hnear s
    have hr := hnear r
    linarith
  have hb := rootedGHPDistance_map_le_of_distortion
    (X := ScaledMetric c (Vertex t)) (Y := Coding.Space g)
    (volume : Measure unitInterval) p q hp hq hps hqs (by linarith : 0 < 2 * ε) hdis 0
  have hmass : (volume : Measure unitInterval).map p =
      (mass t : Measure (Vertex t)).map (ScaledMetric.toScaled c) := by
    change (volume : Measure unitInterval).map (ScaledMetric.toScaled c ∘ sampleVertex t) = _
    rw [← Measure.map_map (ScaledMetric.measurable_toScaled c) (measurable_sampleVertex t),
      map_sampleVertex_volume]
  have hroot : p 0 = ScaledMetric.toScaled c (root t) := by
    change ScaledMetric.toScaled c (sampleVertex t 0) = _
    rw [sampleVertex_zero]
  rw [hmass, hroot] at hb
  change rootedGHPDistance
    ((mass t : Measure (Vertex t)).map (ScaledMetric.toScaled c))
    (Coding.mass g : Measure (Coding.Space g))
    (ScaledMetric.toScaled c (root t)) (Coding.root g) ≤ 3 * (2 * ε) at hb
  change rootedGHPDistance
    ((mass t : Measure (Vertex t)).map (ScaledMetric.toScaled c))
    (Coding.mass g : Measure (Coding.Space g))
    (ScaledMetric.toScaled c (root t)) (Coding.root g) ≤ 6 * ε
  linarith

end FiniteTree

end BGW.ContinuumTrees
