/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactContourGlobal
import BGW.Probability.WeakConvergence
import BGW.StableTrees.SurvivalBasic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Joint height and contour convergence at exact size

The contour limit and the global height/contour error give the diagonal joint limit.
The deterministic clock comparison transfers it to the library contour convention.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees.ExactContour

open BGW.StableTrees.DiscreteForest BGW.StableTrees.TailPair

/-- **C29 (joint height/contour, exact size)**: along every unbounded sequence of admissible
sizes, the rescaled height (time `nt`) and contour (time `2nt`) of the exact-size BGW tree
converge jointly to the excursion height `H^exc` in BOTH coordinates. -/
theorem tendsto_exactHeightContourLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k => exactHeightContourLaw μ B (q k) (hq k)) atTop
      (𝓝 ((excLaw θ).map (fun p => (p.2, p.2)))) := by
  let X k := treeContourPath B (q k) 1
  let Y k τ := treeHeightPath B (q k) 1 τ - treeContourPath B (q k) 1 τ
  have hX k : Measurable (X k) := measurable_treeContourPath B (q k) 1
  have hY k : Measurable (Y k) :=
    (measurable_treeHeightPath B (q k) 1).sub (measurable_treeContourPath B (q k) 1)
  have herr : ∀ ε > 0, Tendsto (fun k => (exactTreeLaw μ (q k) : Measure LocallyFinite.Tree).real
      {τ | ε < dist (Y k τ) 0}) atTop (𝓝 0) := by
    intro ε hε
    convert tendsto_contourHeightError h hqtop hq hε using 1
    funext k
    congr 1
    ext τ
    change (ε < dist (treeHeightPath B (q k) 1 τ - treeContourPath B (q k) 1 τ) 0) ↔
      ε < contourHeightError B (q k) 1 τ
    rw [dist_zero_right, contourHeightError_eq_dist, dist_comm, dist_eq_norm]
  have hjoint := BGW.Probability.tendsto_map_prodMk_of_tendsto_of_error
    (fun k => exactTreeLaw μ (q k)) hX hY (tendsto_exactContourLaw h hqtop hq) herr
  let Φ : C(Icc (0 : ℝ) 1, ℝ) × C(Icc (0 : ℝ) 1, ℝ) →
      C(Icc (0 : ℝ) 1, ℝ) × C(Icc (0 : ℝ) 1, ℝ) := fun z => (z.1 + z.2, z.1)
  have hΦ : Continuous Φ := by fun_prop
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hjoint hΦ
  have hseq k : ((exactTreeLaw μ (q k)).map (fun τ => (X k τ, Y k τ))).map Φ =
      exactHeightContourLaw μ B (q k) (hq k) := by
    apply Subtype.ext
    change ((exactTreeLaw μ (q k)).toMeasure.map (fun τ => (X k τ, Y k τ))).map Φ =
      (exactTreeLaw μ (q k)).toMeasure.map (heightContourPath B (q k))
    erw [Measure.map_map hΦ.measurable ((hX k).prodMk (hY k))]
    congr 1
    funext τ
    apply Prod.ext
    · change treeContourPath B (q k) 1 τ +
        (treeHeightPath B (q k) 1 τ - treeContourPath B (q k) 1 τ) = treeHeightPath B (q k) 1 τ
      abel
    · rfl
  have hlimit : (((excLaw θ).map Prod.snd).map
      (fun x : C(Icc (0 : ℝ) 1, ℝ) => (x, 0))).map Φ =
      (excLaw θ).map (fun p => (p.2, p.2)) := by
    apply Subtype.ext
    change (((excLaw θ).toMeasure.map Prod.snd).map
      (fun x : C(Icc (0 : ℝ) 1, ℝ) => (x, (0 : C(Icc (0 : ℝ) 1, ℝ))))).map Φ =
        (excLaw θ).toMeasure.map (fun p => (p.2, p.2))
    have hm : Measurable (fun x : C(Icc (0 : ℝ) 1, ℝ) => (x, (0 : C(Icc (0 : ℝ) 1, ℝ)))) := by
      fun_prop
    rw [Measure.map_map hΦ.measurable hm,
      Measure.map_map (hΦ.measurable.comp hm) measurable_snd]
    simp only [Φ, Function.comp_def, add_zero]
  have hmap' : Tendsto (fun k =>
      ((exactTreeLaw μ (q k)).map (fun τ => (X k τ, Y k τ))).map Φ) atTop
      (𝓝 ((((excLaw θ).map Prod.snd).map
        (fun x : C(Icc (0 : ℝ) 1, ℝ) => (x, (0 : C(Icc (0 : ℝ) 1, ℝ))))).map Φ)) := hmap
  rw [hlimit] at hmap'
  simpa only [hseq] using hmap'

/-- **C29 in the library contour convention** (`2(n-1)t`): the same limit. -/
theorem tendsto_exactHeightLibContourLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k => exactHeightLibContourLaw μ B (q k) (hq k)) atTop
      (𝓝 ((excLaw θ).map (fun p => (p.2, p.2)))) := by
  have hclose : ∀ ε > 0, Tendsto (fun k =>
      (exactTreeLaw μ (q k) : Measure LocallyFinite.Tree).real
        {τ | ε < dist (heightLibContourPath B (q k) τ) (heightContourPath B (q k) τ)})
      atTop (𝓝 0) := by
    intro ε hε
    have hsmall : ∀ᶠ k in atTop, 2 * |B (q k) / q k| ≤ ε := by
      have hh := (Survival.tendsto_B_div_n h).abs.const_mul 2
      have hh' : Tendsto (fun k => 2 * |B (q k) / q k|) atTop (𝓝 0) := by
        simpa only [abs_zero, mul_zero, Function.comp_def] using hh.comp hqtop
      exact hh'.eventually_le_const hε
    have he : ∀ᶠ k in atTop, (exactTreeLaw μ (q k) : Measure LocallyFinite.Tree).real
        {τ | ε < dist (heightLibContourPath B (q k) τ) (heightContourPath B (q k) τ)} = 0 := by
      filter_upwards [hsmall] with k hk
      have hsize : ∀ᵐ τ ∂(exactTreeLaw μ (q k) : Measure LocallyFinite.Tree),
          τ ∈ LocallyFinite.sizeEvent (q k) := by
        rw [exactTreeLaw_toMeasure μ (q k) (hq k)]
        exact ae_cond_mem (LocallyFinite.measurableSet_sizeEvent _)
      have hnull : ∀ᵐ τ ∂(exactTreeLaw μ (q k) : Measure LocallyFinite.Tree),
          τ ∉ {τ | ε < dist (heightLibContourPath B (q k) τ) (heightContourPath B (q k) τ)} := by
        filter_upwards [hsize] with τ hτ
        obtain ⟨t, rfl⟩ := (LocallyFinite.exists_toLocallyFinite_iff τ).mpr hτ.1
        have ht := (LocallyFinite.toLocallyFinite_mem_sizeEvent_iff t (q k)).mp hτ
        apply not_lt_of_ge
        apply le_trans _ hk
        have hlib : heightLibContourPath B (q k) t.toLocallyFinite =
            (treeHeightPath B (q k) 1 t.toLocallyFinite,
              (B (q k) / q k) • t.contourFunction) := by
          rw [heightLibContourPath, dite_eq_left t.finiteVertices_toLocallyFinite]
          change (treeHeightPath B (q k) 1 t.toLocallyFinite,
            (B (q k) / q k) •
              (PlaneTree.equivFiniteVertices.symm (PlaneTree.equivFiniteVertices
                t)).contourFunction) = _
          rw [Equiv.symm_apply_apply]
        rw [hlib]
        change dist (treeHeightPath B (q k) 1 t.toLocallyFinite,
            (B (q k) / q k) • t.contourFunction)
          (treeHeightPath B (q k) 1 t.toLocallyFinite, treeContourPath B (q k) 1
            t.toLocallyFinite) ≤ _
        rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
        apply (ContinuousMap.dist_le (by positivity)).mpr
        intro s
        rw [Real.dist_eq, ContinuousMap.smul_apply, smul_eq_mul, abs_sub_comm]
        exact abs_treeContourPath_sub_contourFunction_le B t ht s
      have hz : (exactTreeLaw μ (q k) : Measure LocallyFinite.Tree)
          {τ | ε < dist (heightLibContourPath B (q k) τ) (heightContourPath B (q k) τ)} = 0 := by
        simpa only [not_not, Set.mem_ofPred_eq] using ae_iff.mp hnull
      rw [measureReal_def, hz, ENNReal.toReal_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with k hk
    exact hk.symm
  exact BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability
    (fun k => exactTreeLaw μ (q k)) (fun k => measurable_heightLibContourPath B (q k))
    (fun k => measurable_heightContourPath B (q k)) hclose
    (tendsto_exactHeightContourLaw h hqtop hq)

end BGW.StableTrees.ExactContour
