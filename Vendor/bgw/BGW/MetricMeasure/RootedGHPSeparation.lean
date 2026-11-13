/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.RootedGHPTransport

/-!
# Separation for rooted measured GHP distance

Vanishing actual rooted costs give approximate maps of the whole compact
carriers. Their uniform isometric limit preserves the probability measure
by the ambient Prokhorov bounds. The additional root-distance bounds show
that this same limit sends the first root to the second root.

The proof extends `BGW.MetricMeasure.GHPSeparation`, adapted from
`Freezing2/Geometry/GHPSeparation.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
There is no full-support assumption and no assumed root-preserving isometry.
-/

@[expose] public section

open Filter MeasureTheory Metric Set
open scoped Topology Classical

universe u

namespace BGW.MetricMeasure

variable {X Y : Type u}
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]

/-- Zero rooted distance supplies actual ambient realizations of arbitrarily small rooted cost. -/
theorem exists_rootedGHPCoupling_cost_lt_of_eq_zero (μ : Measure X) (ν : Measure Y)
    (x : X) (y : Y) (hz : rootedGHPDistance μ ν x y = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : GHPCoupling X Y, C.rootedCost μ ν x y < ε := by
  obtain ⟨r, hr, hlt⟩ := exists_lt_of_csInf_lt (rootedGHPCosts_nonempty μ ν x y)
    (show sInf (rootedGHPCosts μ ν x y) < ε by
      change rootedGHPDistance μ ν x y < ε; rwa [hz])
  obtain ⟨C, rfl⟩ := hr
  exact ⟨C, hlt⟩

/-- A single surjective isometry preserves both the measure and the distinguished point. -/
theorem exists_measured_rooted_isometry_of_rootedGHPDistance_eq_zero
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : X) (y : Y) (hz : rootedGHPDistance μ ν x y = 0) :
    ∃ e : X ≃ᵢ Y, μ.map e = ν ∧ e x = y := by
  let : Nonempty X := ⟨x⟩
  let : Nonempty Y := ⟨y⟩
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have heps : Tendsto ε atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  choose C hCr using fun n ↦ exists_rootedGHPCoupling_cost_lt_of_eq_zero μ ν x y hz (hε n)
  have hC (n : ℕ) : (C n).cost μ ν < ε n :=
    (le_add_of_nonneg_left dist_nonneg).trans_lt (hCr n)
  have hrootdist (n : ℕ) : dist ((C n).left x) ((C n).right y) < ε n :=
    (le_add_of_nonneg_right
      (show 0 ≤ (C n).cost μ ν from
        add_nonneg ENNReal.toReal_nonneg hausdorffDist_nonneg)).trans_lt (hCr n)
  choose f hf hd hden using fun n ↦ (C n).exists_approximation μ ν (hC n)
  have heps2 : Tendsto (fun n ↦ 2 * ε n) atTop (𝓝 0) := by
    simpa using heps.const_mul 2
  have hrootapprox (n : ℕ) : dist (f n x) y ≤ 2 * ε n := by
    have ht := dist_triangle ((C n).right (f n x)) ((C n).left x) ((C n).right y)
    rw [(C n).right_isometry.dist_eq,
      dist_comm ((C n).right (f n x)) ((C n).left x)] at ht
    have h1 := hf n x
    have h2 := hrootdist n
    linarith
  obtain ⟨U, hU, e, huni⟩ := exists_isometryEquiv_uniform_limit_of_distortion heps2
    (Eventually.of_forall hd) (Eventually.of_forall hden)
  have hroot : e x = y := by
    have hlim : Tendsto (fun n ↦ dist (f n x) y) U (𝓝 (dist (e x) y)) :=
      (huni.tendsto_at x).dist tendsto_const_nhds
    have hzero : Tendsto (fun n ↦ dist (f n x) y) U (𝓝 0) :=
      squeeze_zero (fun _ ↦ dist_nonneg) hrootapprox (heps2.mono_left hU)
    exact dist_eq_zero.mp (tendsto_nhds_unique hlim hzero)
  refine ⟨e, ?_, hroot⟩
  have hzero : levyProkhorovDist (μ.map e) ν = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    by_contra! hpos
    change 0 < levyProkhorovDist (μ.map e) ν at hpos
    let δ : ℝ := levyProkhorovDist (μ.map e) ν / 4
    have hδ : 0 < δ := div_pos hpos (by norm_num)
    obtain ⟨n, hn, hun⟩ := (((heps.mono_left hU).eventually_lt_const hδ).and
      (Metric.tendstoUniformly_iff.mp huni δ hδ)).exists
    have hclose (t : X) : dist ((C n).left t) ((C n).right (e t)) ≤ 2 * δ := by
      have htri := dist_triangle ((C n).left t) ((C n).right (f n t)) ((C n).right (e t))
      rw [(C n).right_isometry.dist_eq] at htri
      have hft := hf n t
      have het := hun t
      rw [dist_comm (e t) (f n t)] at het
      linarith
    have hnear := levyProkhorovDist_map_le_of_dist_le μ (C n).left_isometry.continuous.measurable
      ((C n).right_isometry.continuous.measurable.comp e.continuous.measurable)
      (show 0 ≤ 2 * δ by positivity) hclose
    have hnear' : levyProkhorovDist ((μ.map e).map (C n).right) (μ.map (C n).left) ≤ 2 * δ := by
      rw [Measure.map_map (C n).right_isometry.continuous.measurable e.continuous.measurable,
        levyProkhorovDist_comm]
      exact hnear
    have hsmall : levyProkhorovDist (μ.map (C n).left) (ν.map (C n).right) < ε n :=
      (le_add_of_nonneg_right hausdorffDist_nonneg).trans_lt (hC n)
    have htri := levyProkhorovDist_triangle ((μ.map e).map (C n).right)
      (μ.map (C n).left) (ν.map (C n).right)
    rw [levyProkhorovDist_map_isometry (μ.map e) ν (C n).right_isometry] at htri
    dsimp [δ] at hn hnear'
    linarith
  have hzeroE : levyProkhorovEDist (μ.map e) ν = 0 := by
    exact ((ENNReal.toReal_eq_zero_iff _).mp hzero).resolve_right (levyProkhorovEDist_ne_top _ _)
  refine ext_of_generate_finite _ ?_ isPiSystem_isClosed (fun A hA ↦ ?_) (by simp)
  · rw [BorelSpace.measurable_eq (α := Y), borel_eq_generateFrom_isClosed]
  · exact measure_eq_measure_of_levyProkhorovEDist_eq_zero_of_isClosed hzeroE hA
      ⟨1, Real.zero_lt_one, measure_ne_top _ _⟩ ⟨1, Real.zero_lt_one, measure_ne_top _ _⟩

/-- Zero rooted GHP distance is exactly whole-carrier, root- and measure-preserving isometry. -/
theorem rootedGHPDistance_eq_zero_iff_measured_isometry
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x : X) (y : Y) :
    rootedGHPDistance μ ν x y = 0 ↔ ∃ e : X ≃ᵢ Y, μ.map e = ν ∧ e x = y :=
  ⟨exists_measured_rooted_isometry_of_rootedGHPDistance_eq_zero μ ν x y,
    fun ⟨e, hμ, hroot⟩ ↦ rootedGHPDistance_eq_zero_of_measured_isometry μ ν x y e hμ hroot⟩

end BGW.MetricMeasure
