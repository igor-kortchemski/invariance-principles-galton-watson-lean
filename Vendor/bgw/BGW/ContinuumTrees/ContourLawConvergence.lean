/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.ContourConvergence
public import BGW.MetricMeasure.WeakPerturbation
public import BGW.MetricMeasure.RootedGHPSeparability
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Transferring contour laws to rooted measured tree laws

The probability space and the finite tree may vary with the index. Weak
convergence of the contours divided by a deterministic distance divisor,
together with vanishing divisor-to-size tails, controls the discrepancy
between uniform vertex mass and contour mass in probability.

Measurability is specified for the contour and rooted-space observables.
No global measurable structure is installed on finite trees or addresses.
The size-ratio hypothesis uses strict tails of the real outer measure, so
the proof does not require a separate measurable size map. For measurable
tree-valued inputs these are the usual strict probability tails.
-/

@[expose] public section

open Filter MeasureTheory Metric Set
open scoped Topology ENNReal
open BGW.MetricMeasure

namespace BGW.ContinuumTrees

/-- A compact family of continuous contours is uniformly equicontinuous. -/
theorem exists_uniform_oscillation_of_isCompact
    (K : Set C(unitInterval, ℝ)) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g ∈ K, ∀ s t : unitInterval,
      |(s : ℝ) - (t : ℝ)| ≤ δ → |g s - g t| ≤ ε := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have heval : Continuous (fun p : K × unitInterval => p.1.val p.2) := by fun_prop
  obtain ⟨η, hη, hbound⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous heval) ε hε
  refine ⟨η / 2, half_pos hη, ?_⟩
  intro g hg s t hst
  have hd : dist ((⟨g, hg⟩ : K), s) ((⟨g, hg⟩ : K), t) < η := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, Subtype.dist_eq, Real.dist_eq]
    exact hst.trans_lt (half_lt_self hη)
  have h := hbound hd
  exact (show |g s - g t| < ε by simpa only [Real.dist_eq] using h).le

namespace FiniteTree

/-- On a compact set of rescaled contours, a small divisor-to-size ratio controls the
distance between a vertex-measured finite tree and its continuum contour coding. -/
theorem exists_vertex_ratio_bound_on_compact
    (K : Set C(unitInterval, ℝ)) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ (t : PlaneTree) (b : ℝ) (hb : 0 < b),
      1 ≤ b → b⁻¹ • t.contourFunction ∈ K → b / (t.size : ℝ) ≤ r →
      dist
        (RootedMeasuredGHSpace.scale b⁻¹ (inv_pos.mpr hb)
          (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace t)))
        (Coding.rootedMeasuredGHSpace (b⁻¹ • t.contourFunction)) ≤ ε := by
  obtain ⟨M, hM, hnorm⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨δ, hδ, hosc⟩ := exists_uniform_oscillation_of_isCompact K hK
    (show 0 < ε / 6 by linarith)
  have hM2 : 0 < M + 2 := by linarith
  let r : ℝ := min (1 / 2) (δ / (M + 2))
  have hr : 0 < r := lt_min (by norm_num) (div_pos hδ hM2)
  refine ⟨r, hr, ?_⟩
  intro t b hb hb1 hg hratio
  have hhalf : b / (t.size : ℝ) ≤ 1 / 2 := hratio.trans (min_le_left _ _)
  have hn : 2 ≤ t.size := by
    by_contra h
    have hsingle : t.size = 1 := by have := BGW.PlaneTree.size_pos t; omega
    rw [hsingle, Nat.cast_one, div_one] at hhalf
    linarith
  have hratio0 : 0 ≤ b / (t.size : ℝ) := div_nonneg hb.le (Nat.cast_nonneg _)
  have hnorm' := hnorm (b⁻¹ • t.contourFunction) hg
  have hsmall : (M + 2) * r ≤ δ := by
    have h := (le_div_iff₀ hM2).mp (min_le_right (1 / 2 : ℝ) (δ / (M + 2)))
    simpa only [mul_comm] using h
  have htime : ‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ)) +
      2 / (t.size : ℝ) ≤ δ := by
    calc
      _ ≤ (‖b⁻¹ • t.contourFunction‖ + 2) * (b / (t.size : ℝ)) :=
        contour_time_error_le t hn b hb1
      _ ≤ (M + 2) * (b / (t.size : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (by linarith : ‖b⁻¹ • t.contourFunction‖ + 2 ≤ M + 2) hratio0
      _ ≤ (M + 2) * r := mul_le_mul_of_nonneg_left hratio hM2.le
      _ ≤ δ := hsmall
  have h := rooted_distance_scale_contour_le t hn b⁻¹ (inv_pos.mpr hb)
    (show 0 < ε / 6 by linarith)
    (fun s t hst => hosc _ hg s t (hst.trans htime))
  change dist
    (RootedMeasuredGHSpace.scale b⁻¹ (inv_pos.mpr hb)
      (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace t)))
    (Coding.rootedMeasuredGHSpace (b⁻¹ • t.contourFunction)) ≤ 6 * (ε / 6) at h
  linarith

/-- Weak contour convergence transfers to rooted GHP laws on varying probability spaces.
The only probabilistic error input is the strict divisor-to-size tail condition; the
rooted GHP discrepancy is proved to vanish in probability. -/
theorem tendsto_rooted_laws_of_contour
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree) (b : ℕ → ℝ)
    (hb : ∀ n, 0 < b n) (hbinfty : Tendsto b atTop atTop)
    (hF : ∀ n, Measurable (fun ω : Ω n =>
      RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
        (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace (t n ω)))))
    (hG : ∀ n, Measurable (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction))
    (hratio : ∀ r > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | r < b n / ((t n ω).size : ℝ)}) atTop (𝓝 0))
    {ν : ProbabilityMeasure C(unitInterval, ℝ)}
    (hlim : Tendsto (fun n => (μ n).map
      (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction)) atTop (𝓝 ν)) :
    Tendsto (fun n => (μ n).map (fun ω : Ω n =>
      RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
        (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace (t n ω)))))
      atTop (𝓝 (ν.map Coding.rootedMeasuredGHSpace)) := by
  let G : (n : ℕ) → Ω n → C(unitInterval, ℝ) :=
    fun n ω => (b n)⁻¹ • (t n ω).contourFunction
  let F : (n : ℕ) → Ω n → RootedMeasuredGHSpace := fun n ω =>
    RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
      (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace (t n ω)))
  let P : ℕ → ProbabilityMeasure C(unitInterval, ℝ) := fun n => (μ n).map (G n)
  have hcompact : IsCompact (insert ν (range P)) := hlim.isCompact_insert_range
  have htight := isTightMeasureSet_of_isCompact_closure
    (S := insert ν (range P)) (by
      rw [hcompact.isClosed.closure_eq]
      exact hcompact)
  have herr : ∀ ε > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ε < dist (F n ω) (Coding.rootedMeasuredGHSpace (G n ω))}) atTop (𝓝 0) := by
    intro ε hε
    rw [Metric.tendsto_nhds]
    intro η hη
    obtain ⟨K, hK, hprob⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
        (ENNReal.ofReal (η / 2)) (ENNReal.ofReal_pos.mpr (half_pos hη))
    have hKprob (n : ℕ) : (μ n : Measure (Ω n)).real {ω | G n ω ∉ K} ≤ η / 2 := by
      have hmem : (P n : Measure C(unitInterval, ℝ)) ∈
          {((γ : ProbabilityMeasure C(unitInterval, ℝ)) : Measure C(unitInterval, ℝ)) |
            γ ∈ insert ν (range P)} :=
        ⟨P n, mem_insert_of_mem _ (mem_range_self n), rfl⟩
      have hp := hprob (P n : Measure C(unitInterval, ℝ)) hmem
      change ((μ n : Measure (Ω n)).map (G n)) Kᶜ ≤ ENNReal.ofReal (η / 2) at hp
      rw [Measure.map_apply (hG n) hK.isClosed.measurableSet.compl] at hp
      have hp' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
      change ((μ n : Measure (Ω n)) ((G n) ⁻¹' Kᶜ)).toReal ≤ η / 2
      simpa only [ENNReal.toReal_ofReal (half_pos hη).le] using hp'
    obtain ⟨r, hr, hgood⟩ := exists_vertex_ratio_bound_on_compact K hK hε
    have htail : ∀ᶠ n in atTop, (μ n : Measure (Ω n)).real
        {ω | r < b n / ((t n ω).size : ℝ)} < η / 2 :=
      (hratio r hr).eventually_lt_const (half_pos hη)
    have hb1 : ∀ᶠ n in atTop, 1 ≤ b n := hbinfty.eventually (eventually_ge_atTop 1)
    filter_upwards [hb1, htail] with n hbn htailn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    have hsubset : {ω | ε < dist (F n ω) (Coding.rootedMeasuredGHSpace (G n ω))} ⊆
        {ω | G n ω ∉ K} ∪ {ω | r < b n / ((t n ω).size : ℝ)} := by
      intro ω hω
      by_cases hg : G n ω ∈ K
      · right
        by_contra hratio'
        have he := hgood (t n ω) (b n) (hb n) hbn hg (le_of_not_gt hratio')
        exact (not_le_of_gt hω) he
      · exact Or.inl hg
    calc
      _ ≤ (μ n : Measure (Ω n)).real
          ({ω | G n ω ∉ K} ∪ {ω | r < b n / ((t n ω).size : ℝ)}) :=
        measureReal_mono hsubset
      _ ≤ (μ n : Measure (Ω n)).real {ω | G n ω ∉ K} +
          (μ n : Measure (Ω n)).real {ω | r < b n / ((t n ω).size : ℝ)} :=
        measureReal_union_le _ _
      _ < η := by have := hKprob n; linarith
  have hCG : ∀ n, Measurable (fun ω : Ω n => Coding.rootedMeasuredGHSpace (G n ω)) :=
    fun n => Coding.measurable_rootedMeasuredGHSpace.comp (hG n)
  have hmap (n : ℕ) : (P n).map Coding.rootedMeasuredGHSpace =
      (μ n).map (fun ω : Ω n => Coding.rootedMeasuredGHSpace (G n ω)) := by
    apply ProbabilityMeasure.toMeasure_injective
    change ((μ n : Measure (Ω n)).map (G n)).map Coding.rootedMeasuredGHSpace =
      (μ n : Measure (Ω n)).map (fun ω => Coding.rootedMeasuredGHSpace (G n ω))
    exact Measure.map_map Coding.measurable_rootedMeasuredGHSpace (hG n)
  have hcode : Tendsto (fun n => (μ n).map
      (fun ω : Ω n => Coding.rootedMeasuredGHSpace (G n ω)))
      atTop (𝓝 (ν.map Coding.rootedMeasuredGHSpace)) := by
    have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous P ν hlim
      Coding.continuous_rootedMeasuredGHSpace
    simpa only [hmap] using h
  exact tendsto_probabilityMap_of_error_probability μ hF hCG herr hcode

end FiniteTree

end BGW.ContinuumTrees
