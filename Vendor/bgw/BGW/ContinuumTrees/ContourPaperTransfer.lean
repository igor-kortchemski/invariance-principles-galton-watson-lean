/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.ContourAdapters
public import BGW.ContinuumTrees.ContourLawConvergence

/-!
# Paper contour transfer for rooted measured convergence

Composition of the contour law convergence with the paper time convention and the divisor of
Remark 5.10: convergence of the rescaled paper contour of random plane trees gives convergence of
the laws of the rooted measured trees.

Reference: J.-F. Le Gall, *Random trees and applications*, Probab. Surveys 2 (2005).
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology
open BGW.MetricMeasure BGW.ContinuumTrees BGW.ContinuumTrees.FiniteTree

namespace BGW.ContinuumTrees.FiniteTree

/-- Rooted measured law convergence from the paper contour time convention, with the
deterministic divisor of Remark 5.10. -/
theorem tendsto_rooted_laws_of_paperContour_remarkDivisor
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree)
    (ht : ∀ n, @Measurable (Ω n) PlaneTree _ ⊤ (t n))
    {μ₀ θ : ℝ} (hμ₀ : 0 < μ₀) {N : ℕ → ℕ} {B : ℕ → ℝ}
    (hN : ∀ n, 0 < N n) (hB : ∀ n, 0 < B n) (hBinfty : Tendsto B atTop atTop)
    (hNB : Tendsto (fun n => B n / (N n : ℝ)) atTop (𝓝 0))
    (hsize : ∀ c : ℝ, 0 < c → c < 1 / μ₀ → Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ((t n ω).size : ℝ) < c * (N n : ℝ)}) atTop (𝓝 0))
    {ν : ProbabilityMeasure C(unitInterval, ℝ)}
    (hlim : Tendsto (fun n => (μ n).map
      (fun ω : Ω n => (remarkDivisor μ₀ θ N B n)⁻¹ • (t n ω).paperContourFunction))
      atTop (𝓝 ν)) :
    Tendsto (fun n => (μ n).map (fun ω : Ω n =>
      RootedMeasuredGHSpace.scale (remarkDivisor μ₀ θ N B n)⁻¹
        (inv_pos.mpr (remarkDivisor_pos hμ₀ hN hB n))
        (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace (t n ω)))))
      atTop (𝓝 (ν.map Coding.rootedMeasuredGHSpace)) := by
  have hb := remarkDivisor_pos (θ := θ) hμ₀ hN hB
  have hbinfty := tendsto_remarkDivisor_atTop (θ := θ) hμ₀ hN hB hNB
  have hratio := tendsto_ratio_remarkDivisor (θ := θ) hμ₀ hN hB hBinfty μ t hsize
  have hsize' := tendsto_real_size_lt_of_ratio μ t _ hb hbinfty hratio
  have hG := fun n => measurable_contour_of_top (t n) (remarkDivisor μ₀ θ N B n) (ht n)
  have hP := fun n => measurable_paperContour_of_top (t n) (remarkDivisor μ₀ θ N B n) (ht n)
  have hF := fun n => measurable_rootedMeasuredGHSpace_of_top (t n) (hb n) (ht n)
  exact tendsto_rooted_laws_of_contour μ t _ hb hbinfty hF hG hratio
    (tendsto_map_contour_of_tendsto_map_paperContour μ t _ hb hP hG hsize' hlim)

end BGW.ContinuumTrees.FiniteTree
