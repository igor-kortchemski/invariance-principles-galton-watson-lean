/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.ContinuumTrees.LeafMeasure
import BGW.ContinuumTrees.ContourLawConvergence
import Mathlib.Data.List.Flatten
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Deterministic leaf-measure transfer

Uniform vertex and leaf measures on a finite plane tree are coupled by quantile sampling.
The resulting graph-distance bound scales with the metric and gives a rooted measured
Gromov--Hausdorff--Prokhorov estimate. A uniform modulus on a compact set of contours makes
this estimate quantitative in the divisor-to-size ratio and the leaf-index discrepancy.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BGW.MetricMeasure

/-! ### Measure change on one rooted carrier -/

namespace BGW.MetricMeasure

universe u

/-- **Measure change on one carrier.**  Two probability measures on the same compact metric
space with the same root give rooted measured GHP classes at distance at most the
Lévy–Prokhorov distance of the measures. -/
theorem dist_toRootedMeasuredGHSpace_le_levyProkhorovDist {X : Type u} [MetricSpace X]
    [Nonempty X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ ν : ProbabilityMeasure X) (x : X) :
    dist (toRootedMeasuredGHSpace ⟨CompactMeasuredSpace.of X μ, x⟩)
        (toRootedMeasuredGHSpace ⟨CompactMeasuredSpace.of X ν, x⟩) ≤
      levyProkhorovDist (μ : Measure X) (ν : Measure X) := by
  rw [RootedMeasuredGHSpace.dist_toRootedMeasuredGHSpace]
  change rootedGHPDistance (μ : Measure X) (ν : Measure X) x x ≤ _
  have h := rootedGHPDistance_le_of_isometries μ ν x x X id id isometry_id isometry_id
  simp only [dist_self, Metric.hausdorffDist_self_zero, add_zero, zero_add] at h
  have hb : borel X = ‹MeasurableSpace X› := BorelSpace.measurable_eq.symm
  convert h using 1
  rw [hb, Measure.map_id, Measure.map_id]

end BGW.MetricMeasure

namespace BGW.ContinuumTrees.LeafMeasure

open BGW.PlaneTree BGW.ContinuumTrees.FiniteTree BGW.ContinuumTrees.Coding

/-! ### The leaf-measured rooted tree -/

/-- The uniform probability on the leaves of a plane tree, bundled. -/
noncomputable def leafLaw (t : PlaneTree) : ProbabilityMeasure (Vertex t) :=
  ⟨leafMass t, inferInstance⟩

@[simp] theorem coe_leafLaw (t : PlaneTree) :
    (leafLaw t : Measure (Vertex t)) = leafMass t := rfl

/-- The vertex set with its graph metric and the uniform probability on leaves. -/
noncomputable def leafCompactMeasuredSpace (t : PlaneTree) : CompactMeasuredSpace :=
  CompactMeasuredSpace.of (Vertex t) (leafLaw t)

/-- The same leaf-measured space, rooted at the empty address (as
`FiniteTree.rootedCompactMeasuredSpace`). -/
noncomputable def leafRootedCompactMeasuredSpace (t : PlaneTree) :
    RootedCompactMeasuredSpace where
  space := leafCompactMeasuredSpace t
  root := FiniteTree.root t

/-! ### The last depth-first leaf -/

private theorem isLeafAddr_getLast_vertices (t : PlaneTree) :
    ∀ h : t.vertices ≠ [], IsLeafAddr t (t.vertices.getLast h) := by
  induction t with
  | node ts ih =>
    intro h
    cases ts with
    | nil => simp [IsLeafAddr]
    | cons s ss =>
      let L := (s :: ss).mapIdx (fun i u => u.vertices.map (fun v => i :: v))
      have hts : (s :: ss) ≠ [] := List.cons_ne_nil _ _
      have hL : L ≠ [] := by simp [L]
      have hv : (s :: ss).getLast hts ∈ (s :: ss) := List.getLast_mem hts
      have hvne : ((s :: ss).getLast hts).vertices ≠ [] := by
        intro hvnil
        have hp := size_pos ((s :: ss).getLast hts)
        simp [← length_vertices, hvnil] at hp
      have hlast : L.getLast hL ≠ [] := by
        rw [List.getLast_mapIdx]
        simpa using hvne
      have hflat : L.flatten ≠ [] :=
        List.flatten_ne_nil_iff.mpr ⟨L.getLast hL, List.getLast_mem hL, hlast⟩
      simp only [vertices_node]
      change IsLeafAddr (node (s :: ss)) (([] :: L.flatten).getLast _)
      rw [List.getLast_cons hflat, List.getLast_flatten_eq_getLast_getLast _ hlast]
      intro hbad
      apply ih ((s :: ss).getLast hts) hv hvne
      obtain ⟨r, hr⟩ := hbad
      refine ⟨r, ?_⟩
      simp only [L, List.getElem_mapIdx, List.getElem_map, List.length_mapIdx,
        List.length_map, List.getLast_eq_getElem, length_vertices, List.cons_append] at hr
      rw [fringe?_node_cons] at hr
      have hlt : (s :: ss).length - 1 < (s :: ss).length := by simp
      rw [List.getElem?_eq_getElem hlt] at hr
      simpa [List.getLast_eq_getElem] using hr

/-- The last leaf in DFS order is the last vertex in DFS order. -/
theorem leafIndex_numLeaves_sub_one (t : PlaneTree) :
    leafIndex t (numLeaves t - 1) = t.size - 1 := by
  classical
  have hN : 0 < numLeaves t := numLeaves_pos t
  have hk : numLeaves t - 1 < numLeaves t := by omega
  have hvne : t.vertices ≠ [] := by
    intro hvnil
    have hp := size_pos t
    simp [← length_vertices, hvnil] at hp
  have hlast : IsLeafAddr t (t.vertices.getLast hvne) :=
    isLeafAddr_getLast_vertices t hvne
  have hleafne : leafAddrs t ≠ [] := List.ne_nil_of_length_pos hN
  have hget : (leafAddrs t).getLast hleafne = t.vertices.getLast hvne := by
    obtain ⟨l, a, ha⟩ := (List.eq_nil_or_concat t.vertices).resolve_left hvne
    have hla : IsLeafAddr t a := by simpa [ha] using hlast
    simp [leafAddrs, ha, hla]
  rw [leafIndex, leafVertex_val t hk]
  have hvalid : (leafAddrs t)[numLeaves t - 1]'hk = t.vertices.getLast hvne := by
    rw [← hget]
    symm
    apply List.getLast_eq_getElem
  rw [hvalid, List.getLast_eq_getElem, (nodup_vertices t).idxOf_getElem, length_vertices]

/-- A leaf-index discrepancy bound forces many leaves: `1 / N ≤ D + 1 / n`. -/
theorem one_div_numLeaves_le (t : PlaneTree) {D : ℝ}
    (hD : ∀ k < numLeaves t,
      |(leafIndex t k : ℝ) / (t.size : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| ≤ D) :
    1 / (numLeaves t : ℝ) ≤ D + 1 / (t.size : ℝ) := by
  have hn : 0 < t.size := size_pos t
  have hN : 0 < numLeaves t := numLeaves_pos t
  have hnR : (0 : ℝ) < t.size := by exact_mod_cast hn
  have hNR : (0 : ℝ) < numLeaves t := by exact_mod_cast hN
  have hk : numLeaves t - 1 < numLeaves t := by omega
  have habs := hD (numLeaves t - 1) hk
  rw [leafIndex_numLeaves_sub_one] at habs
  have hncast : ((t.size - 1 : ℕ) : ℝ) + 1 = (t.size : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hn
  have hNcast : ((numLeaves t - 1 : ℕ) : ℝ) + 1 = (numLeaves t : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hN
  have ha : ((t.size - 1 : ℕ) : ℝ) / (t.size : ℝ) + 1 / (t.size : ℝ) = 1 := by
    rw [← add_div, hncast]
    exact div_self hnR.ne'
  have hb : ((numLeaves t - 1 : ℕ) : ℝ) / (numLeaves t : ℝ) +
      1 / (numLeaves t : ℝ) = 1 := by
    rw [← add_div, hNcast]
    exact div_self hNR.ne'
  have hlow := (abs_le.mp habs).2
  linarith

/-! ### Quantile coupling -/

/-- The leaf quantile map sends Lebesgue measure on `[0,1]` to the uniform leaf measure. -/
theorem map_leafVertex_rank_volume (t : PlaneTree) :
    (volume : Measure unitInterval).map (fun s => leafVertex t (rank (numLeaves t) s)) =
      leafMass t := map_leafVertex_rank t

/-- **Quantile coupling bound** (C39(a), unscaled).  The vertex and the leaf selected by the same
uniform time `s` are within graph distance `2 ω`, where `ω` bounds the oscillation of the contour
at the time scale `D + 1/N + 2 ‖c‖/(2(n-1)) + 3/n`. -/
theorem dist_sampleVertex_leafVertex_le (t : PlaneTree) (hn : 2 ≤ t.size) {D ω : ℝ}
    (hD : ∀ k < numLeaves t,
      |(leafIndex t k : ℝ) / (t.size : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| ≤ D)
    (hω : ∀ u v : unitInterval, |(u : ℝ) - (v : ℝ)| ≤ D + 1 / (numLeaves t : ℝ)
        + 2 * (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ))) + 3 / (t.size : ℝ) →
        |t.contourFunction u - t.contourFunction v| ≤ ω)
    (s : unitInterval) :
    dist (sampleVertex t s) (leafVertex t (rank (numLeaves t) s)) ≤ 2 * ω := by
  have hN : 0 < numLeaves t := numLeaves_pos t
  let k := rank (numLeaves t) s
  have hk : k < numLeaves t := rank_lt (numLeaves t) hN s
  have hsample := abs_vertexTime_sampleVertex_sub_le t hn s
  have hcell : |(s : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| ≤ 1 / (numLeaves t : ℝ) := by
    simpa only [abs_sub_comm] using abs_rank_div_sub_time_le (numLeaves t) hN s
  have hdepth := t.contourFunction.apply_le_norm (vertexTime t (leafVertex t k))
  rw [contourFunction_vertexTime] at hdepth
  have hden : (0 : ℝ) ≤ 2 * ((t.size - 1 : ℕ) : ℝ) :=
    mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hdepthBound := div_le_div_of_nonneg_right hdepth hden
  have hleaf := abs_vertexTime_sub_dfsTime_le t hn (leafVertex t k)
  change |(vertexTime t (leafVertex t k) : ℝ) -
    (leafIndex t k : ℝ) / (t.size : ℝ)| ≤ _ at hleaf
  have hleafBound : |(leafIndex t k : ℝ) / (t.size : ℝ) -
      (vertexTime t (leafVertex t k) : ℝ)| ≤
      ‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ)) + 1 / (t.size : ℝ) := by
    rw [abs_sub_comm]
    exact hleaf.trans (add_le_add_left hdepthBound _)
  have htri : |(vertexTime t (sampleVertex t s) : ℝ) -
      (vertexTime t (leafVertex t k) : ℝ)| ≤
      |(vertexTime t (sampleVertex t s) : ℝ) - (s : ℝ)| +
        |(s : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| +
        |(k : ℝ) / (numLeaves t : ℝ) - (leafIndex t k : ℝ) / (t.size : ℝ)| +
        |(leafIndex t k : ℝ) / (t.size : ℝ) - (vertexTime t (leafVertex t k) : ℝ)| := by
    calc
      |(vertexTime t (sampleVertex t s) : ℝ) - (vertexTime t (leafVertex t k) : ℝ)| ≤
          |(vertexTime t (sampleVertex t s) : ℝ) - (s : ℝ)| +
            |(s : ℝ) - (vertexTime t (leafVertex t k) : ℝ)| := abs_sub_le _ _ _
      _ ≤ |(vertexTime t (sampleVertex t s) : ℝ) - (s : ℝ)| +
          (|(s : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| +
            |(k : ℝ) / (numLeaves t : ℝ) - (vertexTime t (leafVertex t k) : ℝ)|) :=
        add_le_add_right (abs_sub_le _ _ _) _
      _ ≤ |(vertexTime t (sampleVertex t s) : ℝ) - (s : ℝ)| +
          (|(s : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| +
            (|(k : ℝ) / (numLeaves t : ℝ) - (leafIndex t k : ℝ) / (t.size : ℝ)| +
              |(leafIndex t k : ℝ) / (t.size : ℝ) -
                (vertexTime t (leafVertex t k) : ℝ)|)) := by
        apply add_le_add_right
        apply add_le_add_right
        exact abs_sub_le _ _ _
      _ = _ := by ring
  have hdiscrep : |(k : ℝ) / (numLeaves t : ℝ) -
      (leafIndex t k : ℝ) / (t.size : ℝ)| ≤ D := by
    simpa only [abs_sub_comm] using hD k hk
  have htime : |(vertexTime t (sampleVertex t s) : ℝ) -
      (vertexTime t (leafVertex t k) : ℝ)| ≤ D + 1 / (numLeaves t : ℝ)
      + 2 * (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ))) + 3 / t.size := by
    calc
      _ ≤ |(vertexTime t (sampleVertex t s) : ℝ) - (s : ℝ)| +
          |(s : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| +
          |(k : ℝ) / (numLeaves t : ℝ) - (leafIndex t k : ℝ) / (t.size : ℝ)| +
          |(leafIndex t k : ℝ) / (t.size : ℝ) - (vertexTime t (leafVertex t k) : ℝ)| := htri
      _ ≤ (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ)) + 2 / (t.size : ℝ)) +
          1 / (numLeaves t : ℝ) + D +
          (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ)) + 1 / (t.size : ℝ)) :=
        add_le_add (add_le_add (add_le_add hsample hcell) hdiscrep) hleafBound
      _ = _ := by ring
  have he := (isometry_vertexEmbedding t).dist_eq (sampleVertex t s) (leafVertex t k)
  change codingDist t.contourFunction (vertexTime t (sampleVertex t s))
    (vertexTime t (leafVertex t k)) = dist (sampleVertex t s) (leafVertex t k) at he
  rw [← he]
  exact codingDist_le_of_oscillation t.contourFunction htime hω

/-- **Scaled vertex/leaf comparison.**  After multiplying the graph distance by `c > 0`, the
leaf-measured and vertex-measured rooted trees are within rooted GHP distance `2 ω`, where `ω`
bounds the oscillation of the SCALED contour `c • c_t` at the time scale
`D + 1/N + 2 ‖c_t‖/(2(n-1)) + 3/n`. -/
theorem dist_scale_leaf_vertex_le (t : PlaneTree) (hn : 2 ≤ t.size) (c : ℝ) (hc : 0 < c)
    {D ω : ℝ}
    (hD : ∀ k < numLeaves t,
      |(leafIndex t k : ℝ) / (t.size : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| ≤ D)
    (hω : ∀ u v : unitInterval, |(u : ℝ) - (v : ℝ)| ≤ D + 1 / (numLeaves t : ℝ)
        + 2 * (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ))) + 3 / (t.size : ℝ) →
        |(c • t.contourFunction) u - (c • t.contourFunction) v| ≤ ω) :
    dist (RootedMeasuredGHSpace.scale c hc
        (toRootedMeasuredGHSpace (leafRootedCompactMeasuredSpace t)))
      (RootedMeasuredGHSpace.scale c hc
        (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace t))) ≤ 2 * ω := by
  have hN : 0 < numLeaves t := numLeaves_pos t
  have hD0 : 0 ≤ D := by
    have h := hD 0 hN
    exact (abs_nonneg _).trans h
  have hscale : 0 ≤ D + 1 / (numLeaves t : ℝ)
      + 2 * (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ))) + 3 / t.size := by
    positivity
  have hω0 : 0 ≤ ω := by
    have h := hω 0 0 (by simpa using hscale)
    simpa using h
  have hω' : ∀ u v : unitInterval, |(u : ℝ) - (v : ℝ)| ≤ D + 1 / (numLeaves t : ℝ)
      + 2 * (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ))) + 3 / (t.size : ℝ) →
      |t.contourFunction u - t.contourFunction v| ≤ ω / c := by
    intro u v huv
    have h := hω u v huv
    simp only [ContinuousMap.smul_apply, smul_eq_mul, ← mul_sub, abs_mul, abs_of_pos hc] at h
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using h
  let c' : Set.Ioi (0 : ℝ) := ⟨c, hc⟩
  refine (dist_toRootedMeasuredGHSpace_le_levyProkhorovDist
    ((leafLaw t).map (ScaledMetric.toScaled c')) ((mass t).map (ScaledMetric.toScaled c'))
    (ScaledMetric.toScaled c' (root t))).trans ?_
  have hleaf : Measurable (fun s => ScaledMetric.toScaled c'
      (leafVertex t (rank (numLeaves t) s))) := by
    exact (ScaledMetric.measurable_toScaled c').comp
      ((measurable_of_countable (leafVertex t)).comp (measurable_rank (numLeaves t)))
  have hvertex : Measurable (fun s => ScaledMetric.toScaled c' (sampleVertex t s)) :=
    (ScaledMetric.measurable_toScaled c').comp (measurable_sampleVertex t)
  have hleafmap : (((leafLaw t).map (ScaledMetric.toScaled c')) :
      Measure (ScaledMetric c' (Vertex t))) = (volume : Measure unitInterval).map
        (fun s => ScaledMetric.toScaled c' (leafVertex t (rank (numLeaves t) s))) := by
    change (leafMass t).map (ScaledMetric.toScaled c') = _
    rw [← map_leafVertex_rank_volume t]
    change ((volume : Measure unitInterval).map
      (leafVertex t ∘ rank (numLeaves t))).map (ScaledMetric.toScaled c') = _
    rw [Measure.map_map (ScaledMetric.measurable_toScaled c')
      ((measurable_of_countable (leafVertex t)).comp (measurable_rank (numLeaves t)))]
    rfl
  have hvertexmap : (((mass t).map (ScaledMetric.toScaled c')) :
      Measure (ScaledMetric c' (Vertex t))) = (volume : Measure unitInterval).map
        (fun s => ScaledMetric.toScaled c' (sampleVertex t s)) := by
    change (mass t : Measure (Vertex t)).map (ScaledMetric.toScaled c') = _
    rw [← map_sampleVertex_volume t, Measure.map_map (ScaledMetric.measurable_toScaled c')
      (measurable_sampleVertex t)]
    rfl
  rw [hleafmap, hvertexmap]
  apply levyProkhorovDist_map_le_of_dist_le volume hleaf hvertex
    (mul_nonneg (by norm_num) hω0)
  intro s
  calc
    dist (ScaledMetric.toScaled c' (leafVertex t (rank (numLeaves t) s)))
        (ScaledMetric.toScaled c' (sampleVertex t s)) =
        c * dist (leafVertex t (rank (numLeaves t) s)) (sampleVertex t s) :=
      ScaledMetric.dist_toScaled c' _ _
    _ = c * dist (sampleVertex t s) (leafVertex t (rank (numLeaves t) s)) := by rw [dist_comm]
    _ ≤ c * (2 * (ω / c)) := mul_le_mul_of_nonneg_left
      (dist_sampleVertex_leafVertex_le t hn hD hω' s) hc.le
    _ = 2 * ω := by field_simp

/-! ### Uniform compact estimate -/

/-- **Uniform deterministic bound on a compact set of rescaled contours.**  For a compact `K`
and `ε > 0` there is `r > 0` such that a tree whose rescaled contour lies in `K`, with
divisor-to-size ratio `≤ r` and all leaf-index discrepancies `≤ r`, has rescaled leaf- and
vertex-measured rooted trees within `ε`. -/
theorem exists_leaf_ratio_bound_on_compact
    (K : Set C(unitInterval, ℝ)) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ (t : PlaneTree) (b : ℝ) (hb : 0 < b), 1 ≤ b →
      b⁻¹ • t.contourFunction ∈ K → b / (t.size : ℝ) ≤ r →
      (∀ k < numLeaves t,
        |(leafIndex t k : ℝ) / (t.size : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| ≤ r) →
      dist (RootedMeasuredGHSpace.scale b⁻¹ (inv_pos.mpr hb)
          (toRootedMeasuredGHSpace (leafRootedCompactMeasuredSpace t)))
        (RootedMeasuredGHSpace.scale b⁻¹ (inv_pos.mpr hb)
          (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace t))) ≤ ε := by
  obtain ⟨M, hM, hnorm⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨δ, hδ, hosc⟩ := exists_uniform_oscillation_of_isCompact K hK
    (show 0 < ε / 2 by linarith)
  have hden : 0 < 2 * M + 7 := by linarith
  let r : ℝ := min (1 / 2) (δ / (2 * M + 7))
  have hr : 0 < r := lt_min (by norm_num) (div_pos hδ hden)
  refine ⟨r, hr, ?_⟩
  intro t b hb hb1 hg hratio hD
  have hhalf : b / (t.size : ℝ) ≤ 1 / 2 := hratio.trans (min_le_left _ _)
  have hn : 2 ≤ t.size := by
    by_contra h
    have hsingle : t.size = 1 := by have := size_pos t; omega
    rw [hsingle, Nat.cast_one, div_one] at hhalf
    linarith
  have hratio0 : 0 ≤ b / (t.size : ℝ) := div_nonneg hb.le (Nat.cast_nonneg _)
  have hnorm' := hnorm (b⁻¹ • t.contourFunction) hg
  have hsmall : (2 * M + 7) * r ≤ δ := by
    have h := (le_div_iff₀ hden).mp (min_le_right (1 / 2 : ℝ) (δ / (2 * M + 7)))
    simpa only [r, mul_comm] using h
  have hinvsize : 1 / (t.size : ℝ) ≤ b / (t.size : ℝ) :=
    div_le_div_of_nonneg_right hb1 (Nat.cast_nonneg _)
  have hinvsize0 : 0 ≤ 1 / (t.size : ℝ) := by positivity
  have hinvN : 1 / (numLeaves t : ℝ) ≤ 2 * r := by
    calc
      1 / (numLeaves t : ℝ) ≤ r + 1 / (t.size : ℝ) := one_div_numLeaves_le t hD
      _ ≤ r + b / (t.size : ℝ) := add_le_add (le_refl r) hinvsize
      _ ≤ 2 * r := by linarith
  have herr : ‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ)) +
      2 / (t.size : ℝ) ≤ (M + 2) * r := by
    calc
      _ ≤ (‖b⁻¹ • t.contourFunction‖ + 2) * (b / (t.size : ℝ)) :=
        contour_time_error_le t hn b hb1
      _ ≤ (M + 2) * (b / (t.size : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) hratio0
      _ ≤ (M + 2) * r := mul_le_mul_of_nonneg_left hratio (by linarith)
  have herr' : 2 * (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ))) +
      3 / (t.size : ℝ) ≤ 2 * ((M + 2) * r) := by
    have htwo := mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 2)
    calc
      _ = 2 * (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ)) +
          2 / (t.size : ℝ)) - 1 / (t.size : ℝ) := by ring
      _ ≤ 2 * (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ)) +
          2 / (t.size : ℝ)) := by linarith
      _ ≤ 2 * ((M + 2) * r) := htwo
  have htime : r + 1 / (numLeaves t : ℝ) +
      2 * (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ))) + 3 / (t.size : ℝ) ≤ δ := by
    calc
      _ ≤ r + 2 * r + 2 * ((M + 2) * r) := by linarith
      _ = (2 * M + 7) * r := by ring
      _ ≤ δ := hsmall
  have h := dist_scale_leaf_vertex_le t hn b⁻¹ (inv_pos.mpr hb) hD
    (fun u v huv => hosc _ hg u v (huv.trans htime))
  linarith

end BGW.ContinuumTrees.LeafMeasure
