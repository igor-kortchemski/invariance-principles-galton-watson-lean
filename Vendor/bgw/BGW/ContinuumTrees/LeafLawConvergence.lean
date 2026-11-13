/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.ContinuumTrees.LeafLawConvergenceDeterministic
public import BGW.ContinuumTrees.ContourAdapters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Law-level leaf-measure transfer

Tight rescaled contour laws, a vanishing divisor-to-size ratio and a vanishing leaf-index
discrepancy make the vertex and leaf measures asymptotically indistinguishable in rooted
measured Gromov--Hausdorff--Prokhorov distance. Weak convergence of the contours therefore
determines the law of the leaf-measured trees, with the same limit as for vertex measures.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BGW.MetricMeasure

namespace BGW.ContinuumTrees.LeafMeasure

open BGW.PlaneTree BGW.ContinuumTrees.FiniteTree

/-! ### In probability -/

/-- **Leaf versus vertex measure in probability** (the C10(1) perturbation input of C39).
If the rescaled contour laws are tight, the divisor-to-size ratio and the leaf-index
discrepancy vanish in probability, then the rescaled leaf- and vertex-measured rooted trees are
within `o_P(1)` in rooted GHP distance. -/
theorem tendsto_dist_leaf_vertex_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree) (b : ℕ → ℝ)
    (hb : ∀ n, 0 < b n) (hbinfty : Tendsto b atTop atTop)
    (hG : ∀ n, Measurable (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction))
    (hratio : ∀ r > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | r < b n / ((t n ω).size : ℝ)}) atTop (𝓝 0))
    (hleaf : ∀ ε > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ∃ k < numLeaves (t n ω), ε < |(leafIndex (t n ω) k : ℝ) / ((t n ω).size : ℝ) -
        (k : ℝ) / (numLeaves (t n ω) : ℝ)|}) atTop (𝓝 0))
    (htight : IsTightMeasureSet (Set.range fun n =>
      ((μ n).map (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction) :
        Measure C(unitInterval, ℝ)))) :
    ∀ ε > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ε < dist
        (RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
          (toRootedMeasuredGHSpace (leafRootedCompactMeasuredSpace (t n ω))))
        (RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
          (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace (t n ω))))}) atTop (𝓝 0) := by
  let G : (n : ℕ) → Ω n → C(unitInterval, ℝ) :=
    fun n ω => (b n)⁻¹ • (t n ω).contourFunction
  let F : (n : ℕ) → Ω n → RootedMeasuredGHSpace := fun n ω =>
    RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
      (toRootedMeasuredGHSpace (leafRootedCompactMeasuredSpace (t n ω)))
  let V : (n : ℕ) → Ω n → RootedMeasuredGHSpace := fun n ω =>
    RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
      (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace (t n ω)))
  intro ε hε
  rw [Metric.tendsto_nhds]
  intro η hη
  have hη3 : 0 < η / 3 := by positivity
  obtain ⟨K, hK, hprob⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
      (ENNReal.ofReal (η / 3)) (ENNReal.ofReal_pos.mpr hη3)
  have hKprob (n : ℕ) : (μ n : Measure (Ω n)).real {ω | G n ω ∉ K} ≤ η / 3 := by
    have hp := hprob ((μ n).map (G n) : Measure C(unitInterval, ℝ)) ⟨n, rfl⟩
    change ((μ n : Measure (Ω n)).map (G n)) Kᶜ ≤ ENNReal.ofReal (η / 3) at hp
    rw [Measure.map_apply (hG n) hK.isClosed.measurableSet.compl] at hp
    have hp' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
    change ((μ n : Measure (Ω n)) ((G n) ⁻¹' Kᶜ)).toReal ≤ η / 3
    simpa only [ENNReal.toReal_ofReal hη3.le] using hp'
  obtain ⟨r, hr, hgood⟩ := exists_leaf_ratio_bound_on_compact K hK hε
  have htail : ∀ᶠ n in atTop, (μ n : Measure (Ω n)).real
      {ω | r < b n / ((t n ω).size : ℝ)} < η / 3 :=
    (hratio r hr).eventually_lt_const hη3
  have hleaftail : ∀ᶠ n in atTop, (μ n : Measure (Ω n)).real
      {ω | ∃ k < numLeaves (t n ω), r < |(leafIndex (t n ω) k : ℝ) /
        ((t n ω).size : ℝ) - (k : ℝ) / (numLeaves (t n ω) : ℝ)|} < η / 3 :=
    (hleaf r hr).eventually_lt_const hη3
  have hb1 : ∀ᶠ n in atTop, 1 ≤ b n := hbinfty.eventually (eventually_ge_atTop 1)
  filter_upwards [hb1, htail, hleaftail] with n hbn htailn hleafn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have hsubset : {ω | ε < dist (F n ω) (V n ω)} ⊆
      ({ω | G n ω ∉ K} ∪ {ω | r < b n / ((t n ω).size : ℝ)}) ∪
        {ω | ∃ k < numLeaves (t n ω), r < |(leafIndex (t n ω) k : ℝ) /
          ((t n ω).size : ℝ) - (k : ℝ) / (numLeaves (t n ω) : ℝ)|} := by
    intro ω hω
    by_cases hg : G n ω ∈ K
    · by_cases hq : r < b n / ((t n ω).size : ℝ)
      · exact Or.inl (Or.inr hq)
      · by_cases hl : ∃ k < numLeaves (t n ω), r < |(leafIndex (t n ω) k : ℝ) /
          ((t n ω).size : ℝ) - (k : ℝ) / (numLeaves (t n ω) : ℝ)|
        · exact Or.inr hl
        · push Not at hl
          have he := hgood (t n ω) (b n) (hb n) hbn hg (le_of_not_gt hq) hl
          exact ((not_le_of_gt hω) he).elim
    · exact Or.inl (Or.inl hg)
  calc
    _ ≤ (μ n : Measure (Ω n)).real
        (({ω | G n ω ∉ K} ∪ {ω | r < b n / ((t n ω).size : ℝ)}) ∪
          {ω | ∃ k < numLeaves (t n ω), r < |(leafIndex (t n ω) k : ℝ) /
            ((t n ω).size : ℝ) - (k : ℝ) / (numLeaves (t n ω) : ℝ)|}) :=
      measureReal_mono hsubset
    _ ≤ (μ n : Measure (Ω n)).real
        ({ω | G n ω ∉ K} ∪ {ω | r < b n / ((t n ω).size : ℝ)}) +
        (μ n : Measure (Ω n)).real
          {ω | ∃ k < numLeaves (t n ω), r < |(leafIndex (t n ω) k : ℝ) /
            ((t n ω).size : ℝ) - (k : ℝ) / (numLeaves (t n ω) : ℝ)|} :=
      measureReal_union_le _ _
    _ ≤ ((μ n : Measure (Ω n)).real {ω | G n ω ∉ K} +
        (μ n : Measure (Ω n)).real {ω | r < b n / ((t n ω).size : ℝ)}) +
        (μ n : Measure (Ω n)).real
          {ω | ∃ k < numLeaves (t n ω), r < |(leafIndex (t n ω) k : ℝ) /
            ((t n ω).size : ℝ) - (k : ℝ) / (numLeaves (t n ω) : ℝ)|} :=
      add_le_add (measureReal_union_le _ _) (le_refl _)
    _ < η := by have := hKprob n; linarith

end BGW.ContinuumTrees.LeafMeasure

namespace BGW.ContinuumTrees.FiniteTree

open BGW.PlaneTree

/-- **Vertex measure versus contour coding in probability** (the discrepancy step inside C38,
exported).  Under tight rescaled contour laws and vanishing divisor-to-size ratio, the rescaled
vertex-measured rooted tree is within `o_P(1)` of the tree coded by its rescaled contour. -/
theorem tendsto_dist_vertex_coded_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree) (b : ℕ → ℝ)
    (hb : ∀ n, 0 < b n) (hbinfty : Tendsto b atTop atTop)
    (hG : ∀ n, Measurable (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction))
    (hratio : ∀ r > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | r < b n / ((t n ω).size : ℝ)}) atTop (𝓝 0))
    (htight : IsTightMeasureSet (Set.range fun n =>
      ((μ n).map (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction) :
        Measure C(unitInterval, ℝ)))) :
    ∀ ε > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ε < dist
        (RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
          (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace (t n ω))))
        (Coding.rootedMeasuredGHSpace ((b n)⁻¹ • (t n ω).contourFunction))}) atTop (𝓝 0) := by
  let G : (n : ℕ) → Ω n → C(unitInterval, ℝ) :=
    fun n ω => (b n)⁻¹ • (t n ω).contourFunction
  let F : (n : ℕ) → Ω n → RootedMeasuredGHSpace := fun n ω =>
    RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
      (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace (t n ω)))
  intro ε hε
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨K, hK, hprob⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
      (ENNReal.ofReal (η / 2)) (ENNReal.ofReal_pos.mpr (half_pos hη))
  have hKprob (n : ℕ) : (μ n : Measure (Ω n)).real {ω | G n ω ∉ K} ≤ η / 2 := by
    have hp := hprob ((μ n).map (G n) : Measure C(unitInterval, ℝ)) ⟨n, rfl⟩
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

end BGW.ContinuumTrees.FiniteTree

namespace BGW.ContinuumTrees.LeafMeasure

open BGW.PlaneTree BGW.ContinuumTrees.FiniteTree

/-! ### Convergence in law (public CT9 interface) -/

/-- **C39, law-level form (CT9).**  Weak convergence of the rescaled contours on varying
probability spaces, vanishing divisor-to-size tails and vanishing leaf-index discrepancy in
probability give convergence in law, in the rooted measured GHP space, of the rescaled trees
carrying the uniform LEAF measure, to the same limit `ν.map Coding.rootedMeasuredGHSpace` as for
the vertex measure (C38, `tendsto_rooted_laws_of_contour`).  The measurability of the
vertex-measure map (`hF` of C38) is not needed. -/
theorem tendsto_rooted_leaf_laws_of_contour
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree) (b : ℕ → ℝ)
    (hb : ∀ n, 0 < b n) (hbinfty : Tendsto b atTop atTop)
    (hFL : ∀ n, Measurable (fun ω : Ω n =>
      RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
        (toRootedMeasuredGHSpace (leafRootedCompactMeasuredSpace (t n ω)))))
    (hG : ∀ n, Measurable (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction))
    (hratio : ∀ r > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | r < b n / ((t n ω).size : ℝ)}) atTop (𝓝 0))
    (hleaf : ∀ ε > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ∃ k < numLeaves (t n ω), ε < |(leafIndex (t n ω) k : ℝ) / ((t n ω).size : ℝ) -
        (k : ℝ) / (numLeaves (t n ω) : ℝ)|}) atTop (𝓝 0))
    {ν : ProbabilityMeasure C(unitInterval, ℝ)}
    (hlim : Tendsto (fun n => (μ n).map
      (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction)) atTop (𝓝 ν)) :
    Tendsto (fun n => (μ n).map (fun ω : Ω n =>
      RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
        (toRootedMeasuredGHSpace (leafRootedCompactMeasuredSpace (t n ω)))))
      atTop (𝓝 (ν.map Coding.rootedMeasuredGHSpace)) := by
  let G : (n : ℕ) → Ω n → C(unitInterval, ℝ) :=
    fun n ω => (b n)⁻¹ • (t n ω).contourFunction
  let F : (n : ℕ) → Ω n → RootedMeasuredGHSpace := fun n ω =>
    RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
      (toRootedMeasuredGHSpace (leafRootedCompactMeasuredSpace (t n ω)))
  let V : (n : ℕ) → Ω n → RootedMeasuredGHSpace := fun n ω =>
    RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
      (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace (t n ω)))
  let P : ℕ → ProbabilityMeasure C(unitInterval, ℝ) := fun n => (μ n).map (G n)
  have hcompact : IsCompact (insert ν (range P)) := hlim.isCompact_insert_range
  have htight0 := isTightMeasureSet_of_isCompact_closure
    (S := insert ν (range P)) (by
      rw [hcompact.isClosed.closure_eq]
      exact hcompact)
  have htight : IsTightMeasureSet (Set.range fun n =>
      ((μ n).map (G n) : Measure C(unitInterval, ℝ))) := by
    apply htight0.subset
    rintro _ ⟨n, rfl⟩
    exact ⟨P n, mem_insert_of_mem _ (mem_range_self n), rfl⟩
  have hLV := tendsto_dist_leaf_vertex_probability μ t b hb hbinfty hG hratio hleaf htight
  have hVC := tendsto_dist_vertex_coded_probability μ t b hb hbinfty hG hratio htight
  have herr : ∀ ε > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ε < dist (F n ω) (Coding.rootedMeasuredGHSpace (G n ω))}) atTop (𝓝 0) := by
    intro ε hε
    have h1 := hLV (ε / 2) (half_pos hε)
    have h2 := hVC (ε / 2) (half_pos hε)
    rw [Metric.tendsto_nhds]
    intro η hη
    have htail1 : ∀ᶠ n in atTop, (μ n : Measure (Ω n)).real
        {ω | ε / 2 < dist (F n ω) (V n ω)} < η / 2 :=
      h1.eventually_lt_const (half_pos hη)
    have htail2 : ∀ᶠ n in atTop, (μ n : Measure (Ω n)).real
        {ω | ε / 2 < dist (V n ω) (Coding.rootedMeasuredGHSpace (G n ω))} < η / 2 :=
      h2.eventually_lt_const (half_pos hη)
    filter_upwards [htail1, htail2] with n h1n h2n
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    have hsubset : {ω | ε < dist (F n ω) (Coding.rootedMeasuredGHSpace (G n ω))} ⊆
        {ω | ε / 2 < dist (F n ω) (V n ω)} ∪
          {ω | ε / 2 < dist (V n ω) (Coding.rootedMeasuredGHSpace (G n ω))} := by
      intro ω hω
      change ε < dist (F n ω) (Coding.rootedMeasuredGHSpace (G n ω)) at hω
      by_cases hlv : ε / 2 < dist (F n ω) (V n ω)
      · exact Or.inl hlv
      · right
        by_contra hvc
        have htri := dist_triangle (F n ω) (V n ω) (Coding.rootedMeasuredGHSpace (G n ω))
        have hlv' : dist (F n ω) (V n ω) ≤ ε / 2 := le_of_not_gt hlv
        have hvc' : dist (V n ω) (Coding.rootedMeasuredGHSpace (G n ω)) ≤ ε / 2 :=
          le_of_not_gt hvc
        linarith
    calc
      _ ≤ (μ n : Measure (Ω n)).real
          ({ω | ε / 2 < dist (F n ω) (V n ω)} ∪
            {ω | ε / 2 < dist (V n ω) (Coding.rootedMeasuredGHSpace (G n ω))}) :=
        measureReal_mono hsubset
      _ ≤ (μ n : Measure (Ω n)).real {ω | ε / 2 < dist (F n ω) (V n ω)} +
          (μ n : Measure (Ω n)).real
            {ω | ε / 2 < dist (V n ω) (Coding.rootedMeasuredGHSpace (G n ω))} :=
        measureReal_union_le _ _
      _ < η := by linarith
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
  exact tendsto_probabilityMap_of_error_probability μ hFL hCG herr hcode

/-- Hypothesis `hFL` for random trees measurable for the `⊤` σ-algebra on `PlaneTree`. -/
theorem measurable_leafRootedMeasuredGHSpace_of_top {X : Type*} [MeasurableSpace X]
    (t : X → PlaneTree) {b : ℝ} (hb : 0 < b) (ht : @Measurable X PlaneTree _ ⊤ t) :
    Measurable (fun x : X => RootedMeasuredGHSpace.scale b⁻¹ (inv_pos.mpr hb)
      (toRootedMeasuredGHSpace (leafRootedCompactMeasuredSpace (t x)))) :=
  measurable_comp_of_top t ht (fun τ => RootedMeasuredGHSpace.scale b⁻¹ (inv_pos.mpr hb)
    (toRootedMeasuredGHSpace (leafRootedCompactMeasuredSpace τ)))

/-- **Consumer form**: C39 law-level transfer for `⊤`-measurable random trees, with no separate
measurability hypothesis. -/
theorem tendsto_rooted_leaf_laws_of_contour_of_top
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree) (ht : ∀ n, @Measurable (Ω n) PlaneTree _ ⊤ (t n))
    (b : ℕ → ℝ) (hb : ∀ n, 0 < b n) (hbinfty : Tendsto b atTop atTop)
    (hratio : ∀ r > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | r < b n / ((t n ω).size : ℝ)}) atTop (𝓝 0))
    (hleaf : ∀ ε > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ∃ k < numLeaves (t n ω), ε < |(leafIndex (t n ω) k : ℝ) / ((t n ω).size : ℝ) -
        (k : ℝ) / (numLeaves (t n ω) : ℝ)|}) atTop (𝓝 0))
    {ν : ProbabilityMeasure C(unitInterval, ℝ)}
    (hlim : Tendsto (fun n => (μ n).map
      (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction)) atTop (𝓝 ν)) :
    Tendsto (fun n => (μ n).map (fun ω : Ω n =>
      RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
        (toRootedMeasuredGHSpace (leafRootedCompactMeasuredSpace (t n ω)))))
      atTop (𝓝 (ν.map Coding.rootedMeasuredGHSpace)) :=
  tendsto_rooted_leaf_laws_of_contour μ t b hb hbinfty
    (fun n => measurable_leafRootedMeasuredGHSpace_of_top (t n) (hb n) (ht n))
    (fun n => measurable_contour_of_top (t n) (b n) (ht n)) hratio hleaf hlim

end BGW.ContinuumTrees.LeafMeasure
