/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.Ultrafilter
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Compact limits of approximate isometries

Maps with uniformly vanishing distance distortion and asymptotically dense
images have a uniformly convergent refining ultrafilter whose limit is a
surjective isometry. The approximating maps need not be continuous or
measurable. Compactness and the vanishing distortion prove the uniform limit;
no exact-isometry or measure-preservation conclusion is assumed.

Adapted from `Freezing2/Geometry/ApproximateIsometryLimit.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open Filter Metric Set
open scoped Topology Classical

namespace BGW.MetricMeasure

variable {ι X Y : Type*} [MetricSpace X] [MetricSpace Y]
  {l : Filter ι} [NeBot l] {f : ι → X → Y} {g : X → Y} {err : ι → ℝ}

/-- Pointwise limits of maps with vanishing uniform distortion preserve distances. -/
theorem isometry_of_tendsto_of_distortion
    (herr : Tendsto err l (𝓝 0))
    (hd : ∀ᶠ i in l, ∀ x y, |dist (f i x) (f i y) - dist x y| ≤ err i)
    (hpt : ∀ x, Tendsto (fun i ↦ f i x) l (𝓝 (g x))) : Isometry g := by
  apply Isometry.of_dist_eq
  intro x y
  have ht := (((hpt x).dist (hpt y)).sub_const (dist x y)).abs
  have hz : Tendsto (fun i ↦ |dist (f i x) (f i y) - dist x y|) l (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) (hd.mono fun _ h ↦ h x y) herr
  exact sub_eq_zero.mp (abs_eq_zero.mp (tendsto_nhds_unique ht hz))

/-- On a compact domain the same vanishing distortion upgrades pointwise
convergence to uniform convergence, even for discontinuous approximants. -/
theorem tendstoUniformly_of_tendsto_of_distortion [CompactSpace X]
    (herr : Tendsto err l (𝓝 0))
    (hd : ∀ᶠ i in l, ∀ x y, |dist (f i x) (f i y) - dist x y| ≤ err i)
    (hpt : ∀ x, Tendsto (fun i ↦ f i x) l (𝓝 (g x))) : TendstoUniformly f g l := by
  have hg := isometry_of_tendsto_of_distortion herr hd hpt
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hδ : 0 < ε / 4 := by positivity
  obtain ⟨t, _, ht, hcover⟩ := finite_cover_balls_of_compact (s := (univ : Set X))
    isCompact_univ hδ
  have hpts : ∀ᶠ i in l, ∀ z ∈ t, dist (g z) (f i z) < ε / 4 := by
    apply ht.eventually_all.mpr
    intro z _
    simpa only [dist_comm] using Metric.tendsto_nhds.mp (hpt z) (ε / 4) hδ
  filter_upwards [hd, hpts, herr.eventually_lt_const hδ] with i hdi hpi hei
  intro x
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
  have hdist : dist x z < ε / 4 := hxz
  have hnear := hpi z hz
  have hdist' := (abs_le.mp (hdi z x)).2
  have ht1 := dist_triangle (g x) (g z) (f i x)
  have ht2 := dist_triangle (g z) (f i z) (f i x)
  rw [hg.dist_eq] at ht1
  rw [dist_comm z x] at hdist'
  linarith

/-- A uniform isometric limit of asymptotically dense maps is surjective. -/
theorem surjective_of_tendstoUniformly_of_dense [CompactSpace X]
    (hg : Isometry g) (herr : Tendsto err l (𝓝 0))
    (hdense : ∀ᶠ i in l, ∀ y, ∃ x, dist y (f i x) ≤ err i)
    (huni : TendstoUniformly f g l) : Function.Surjective g := by
  intro y
  have hc : IsClosed (range g) := (isCompact_range hg.continuous).isClosed
  apply mem_range.mp
  rw [← hc.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨i, hi, he, hd⟩ :=
    ((Metric.tendstoUniformly_iff.mp huni (ε / 2) hhalf).and
      ((herr.eventually_lt_const hhalf).and hdense)).exists
  obtain ⟨x, hx⟩ := hd y
  refine ⟨g x, mem_range_self _, ?_⟩
  have ht := dist_triangle y (f i x) (g x)
  have hix := hi x
  rw [dist_comm (g x) (f i x)] at hix
  linarith

/-- Compactness supplies a refining ultrafilter and a genuine surjective
isometry as its uniform limit. No continuity of the approximants is required. -/
theorem exists_isometryEquiv_uniform_limit_of_distortion
    [CompactSpace X] [CompactSpace Y]
    (herr : Tendsto err l (𝓝 0))
    (hd : ∀ᶠ i in l, ∀ x y, |dist (f i x) (f i y) - dist x y| ≤ err i)
    (hdense : ∀ᶠ i in l, ∀ y, ∃ x, dist y (f i x) ≤ err i) :
    ∃ U : Ultrafilter ι, (U : Filter ι) ≤ l ∧ ∃ e : X ≃ᵢ Y,
      TendstoUniformly f e U := by
  obtain ⟨g, _, hg⟩ := (isCompact_univ : IsCompact (univ : Set (X → Y))).exists_mapClusterPt
    (u := f) (f := l) (by simp)
  obtain ⟨U, hU, hlim⟩ := mapClusterPt_iff_ultrafilter.mp hg
  have he := herr.mono_left hU
  have hd' := hd.filter_mono hU
  have hden := hdense.filter_mono hU
  have hpt := tendsto_pi_nhds.mp hlim
  have hiso := isometry_of_tendsto_of_distortion he hd' hpt
  have huni := tendstoUniformly_of_tendsto_of_distortion he hd' hpt
  have hsurj := surjective_of_tendstoUniformly_of_dense hiso he hden huni
  refine ⟨U, hU, ⟨Equiv.ofBijective g ⟨hiso.injective, hsurj⟩, hiso⟩, ?_⟩
  exact huni

end BGW.MetricMeasure
