/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.GHPUnderlyingGH
public import BGW.MetricMeasure.ApproximateIsometryLimit
public import BGW.MetricMeasure.ProkhorovIsometry

/-!
# Separation for the exact measured GHP distance

Near-zero actual ambient costs give approximate maps between the entire
compact carriers. A compact uniform limit is a surjective isometry. Uniform
closeness in the original ambient realizations, together with their vanishing
Prokhorov costs, proves that this isometry preserves the probability measures.
Thus no points outside the measure supports are discarded.

Adapted from `Freezing2/Geometry/GHPSeparation.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open Filter MeasureTheory Metric Set
open scoped Topology Classical

universe u

namespace BGW.MetricMeasure

/-- An actual common ambient metric realization of two spaces. -/
structure GHPCoupling (X Y : Type u) [MetricSpace X] [MetricSpace Y] where
  /-- The common ambient carrier realizing both spaces. -/
  ambient : Type u
  /-- The metric on the common ambient carrier. -/
  metric : MetricSpace ambient
  /-- The isometric embedding of the whole left-hand space. -/
  left : X → ambient
  /-- The isometric embedding of the whole right-hand space. -/
  right : Y → ambient
  left_isometry : @Isometry X ambient inferInstance
    (@PseudoMetricSpace.toPseudoEMetricSpace _ metric.toPseudoMetricSpace) left
  right_isometry : @Isometry Y ambient inferInstance
    (@PseudoMetricSpace.toPseudoEMetricSpace _ metric.toPseudoMetricSpace) right

namespace GHPCoupling

variable {X Y : Type u} [MetricSpace X] [MetricSpace Y]

instance (C : GHPCoupling X Y) : MetricSpace C.ambient := C.metric
noncomputable instance (C : GHPCoupling X Y) : MeasurableSpace C.ambient := borel _
instance (C : GHPCoupling X Y) : BorelSpace C.ambient := ⟨rfl⟩

/-- The sum of the Lévy–Prokhorov cost of the pushed measures and the Hausdorff cost
of the embedded whole spaces. -/
noncomputable def cost [MeasurableSpace X] [MeasurableSpace Y]
    (C : GHPCoupling X Y) (μ : Measure X) (ν : Measure Y) : ℝ :=
  levyProkhorovDist (μ.map C.left) (ν.map C.right) +
    hausdorffDist (range C.left) (range C.right)

/-- A small actual ambient cost supplies approximate isometries on all
points. The chosen maps themselves need no measurability assumption. -/
theorem exists_approximation [MeasurableSpace X] [MeasurableSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    (C : GHPCoupling X Y) (μ : Measure X) (ν : Measure Y) {ε : ℝ}
    (hC : C.cost μ ν < ε) :
    ∃ f : X → Y,
      (∀ x, dist (C.left x) (C.right (f x)) < ε) ∧
      (∀ x y, |dist (f x) (f y) - dist x y| ≤ 2 * ε) ∧
      (∀ y, ∃ x, dist y (f x) ≤ 2 * ε) := by
  have hH : hausdorffDist (range C.left) (range C.right) < ε :=
    (le_add_of_nonneg_left ENNReal.toReal_nonneg).trans_lt hC
  have hfinite : hausdorffEDist (range C.left) (range C.right) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _)
      (isCompact_range C.left_isometry.continuous).isBounded
      (isCompact_range C.right_isometry.continuous).isBounded
  have hex (x : X) : ∃ y : Y, dist (C.left x) (C.right y) < ε := by
    obtain ⟨z, ⟨y, rfl⟩, hy⟩ := exists_dist_lt_of_hausdorffDist_lt (mem_range_self x) hH hfinite
    exact ⟨y, hy⟩
  choose f hf using hex
  refine ⟨f, hf, ?_, ?_⟩
  · intro x y
    have h := dist_dist_dist_le (C.right (f x)) (C.right (f y)) (C.left x) (C.left y)
    rw [C.right_isometry.dist_eq, C.left_isometry.dist_eq, Real.dist_eq,
      dist_comm (C.right (f x)), dist_comm (C.right (f y))] at h
    have hx := hf x
    have hy := hf y
    linarith
  · intro y
    obtain ⟨z, ⟨x, rfl⟩, hx⟩ := exists_dist_lt_of_hausdorffDist_lt' (mem_range_self y) hH hfinite
    refine ⟨x, ?_⟩
    have h := dist_triangle (C.right y) (C.left x) (C.right (f x))
    rw [C.right_isometry.dist_eq, dist_comm (C.right y) (C.left x)] at h
    have hfx := hf x
    linarith

end GHPCoupling

variable {X Y : Type u}
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [Nonempty Y]

omit [Nonempty X] [Nonempty Y] in
/-- The GHP infimum supplies actual ambient realizations with arbitrarily
small summed costs when the distance is zero. -/
theorem exists_ghpCoupling_cost_lt_of_eq_zero (μ : Measure X) (ν : Measure Y)
    (hz : ghpDistance μ ν = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : GHPCoupling X Y, C.cost μ ν < ε := by
  obtain ⟨r, hr, hlt⟩ := exists_lt_of_csInf_lt (ghpCosts_nonempty μ ν)
    (show sInf (ghpCosts μ ν) < ε by change ghpDistance μ ν < ε; rwa [hz])
  obtain ⟨A, m, i, j, hi, hj, rfl⟩ := hr
  let := m
  let : TopologicalSpace A := m.toUniformSpace.toTopologicalSpace
  let : MeasurableSpace A := borel A
  exact ⟨⟨A, m, i, j, hi, hj⟩, hlt⟩

/-- Zero GHP distance forces a measure-preserving isometry of the entire
compact spaces. Compactness controls geometry and the ambient Prokhorov
bounds determine the measure of the resulting isometry. -/
theorem exists_measured_isometry_of_ghpDistance_eq_zero
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hz : ghpDistance μ ν = 0) : ∃ e : X ≃ᵢ Y, μ.map e = ν := by
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have heps : Tendsto ε atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  choose C hC using fun n ↦ exists_ghpCoupling_cost_lt_of_eq_zero μ ν hz (hε n)
  choose f hf hd hden using fun n ↦ (C n).exists_approximation μ ν (hC n)
  have heps2 : Tendsto (fun n ↦ 2 * ε n) atTop (𝓝 0) := by simpa using heps.const_mul 2
  obtain ⟨U, hU, e, huni⟩ := exists_isometryEquiv_uniform_limit_of_distortion heps2
    (Eventually.of_forall hd) (Eventually.of_forall hden)
  refine ⟨e, ?_⟩
  have hzero : levyProkhorovDist (μ.map e) ν = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    by_contra! hpos
    change 0 < levyProkhorovDist (μ.map e) ν at hpos
    let δ : ℝ := levyProkhorovDist (μ.map e) ν / 4
    have hδ : 0 < δ := div_pos hpos (by norm_num)
    obtain ⟨n, hn, hun⟩ := (((heps.mono_left hU).eventually_lt_const hδ).and
      (Metric.tendstoUniformly_iff.mp huni δ hδ)).exists
    have hclose (x : X) : dist ((C n).left x) ((C n).right (e x)) ≤ 2 * δ := by
      have htri := dist_triangle ((C n).left x) ((C n).right (f n x)) ((C n).right (e x))
      rw [(C n).right_isometry.dist_eq] at htri
      have hfx := hf n x
      have hex := hun x
      rw [dist_comm (e x) (f n x)] at hex
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

/-- Separation is with respect to whole-space measured isometry, exactly as
for whole-space measured isometry. -/
theorem ghpDistance_eq_zero_iff_measured_isometry
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ghpDistance μ ν = 0 ↔ ∃ e : X ≃ᵢ Y, μ.map e = ν :=
  ⟨exists_measured_isometry_of_ghpDistance_eq_zero μ ν,
    fun ⟨e, he⟩ ↦ ghpDistance_eq_zero_of_measured_isometry μ ν e he⟩

end BGW.MetricMeasure
