/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactContourTerminal
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import BGW.Probability.WeakConvergence
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Convergence of the contour from its strict prefixes

Constant extensions of height prefixes approximate the contour. Terminal-window control
makes this approximation uniform in probability as the prefix tends to the whole interval.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees.ExactContour

open BGW.StableTrees.DiscreteForest BGW.StableTrees.TailPair

/-- Extend a continuous prefix to the unit interval by its terminal value. -/
noncomputable def extendPrefix (a : ℝ≥0) (g : C(Icc (0 : ℝ) (a : ℝ), ℝ)) :
    C(unitInterval, ℝ) :=
  g.comp ⟨fun t => ⟨min (t : ℝ) a, le_min t.property.1 a.coe_nonneg, min_le_right _ _⟩,
    by fun_prop⟩

/-- Constant extension is continuous in the uniform topologies. -/
theorem continuous_extendPrefix (a : ℝ≥0) : Continuous (extendPrefix a) :=
  ContinuousMap.continuous_precomp _

/-- Stop a continuous unit-interval path at a prefix time. -/
noncomputable def stopPrefix (a : ℝ≥0) (ha : a ≤ 1) (g : C(unitInterval, ℝ)) :
    C(unitInterval, ℝ) := extendPrefix a
      (g.comp ⟨Set.inclusion (Icc_subset_Icc_right (show (a : ℝ) ≤ 1 from ha)),
        continuous_inclusion _⟩)

/-- Stopping at a fixed prefix time is continuous in the uniform topology. -/
theorem continuous_stopPrefix (a : ℝ≥0) (ha : a ≤ 1) : Continuous (stopPrefix a ha) :=
  (continuous_extendPrefix a).comp (ContinuousMap.continuous_precomp _)

private theorem tendsto_stopPrefix {a : ℕ → ℝ≥0} (ha : ∀ j, a j ≤ 1)
    (hatop : Tendsto (fun j => (a j : ℝ)) atTop (𝓝 1)) (g : C(unitInterval, ℝ)) :
    Tendsto (fun j => stopPrefix (a j) (ha j) g) atTop (𝓝 g) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous g.continuous) (ε / 2) (half_pos hε)
  have he := hatop.eventually (lt_mem_nhds (show 1 - δ < 1 by linarith))
  rw [eventually_atTop] at he
  obtain ⟨N, hN⟩ := he
  refine ⟨N, ?_⟩
  intro j hj
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (ContinuousMap.dist_le (half_pos hε).le).mpr
  intro t
  apply (hosc (show dist
    (⟨min (t : ℝ) (a j), le_min t.property.1 (a j).coe_nonneg,
      (min_le_left _ _).trans t.property.2⟩ : unitInterval) t < δ from ?_)).le
  rw [Subtype.dist_eq, Real.dist_eq]
  change |min (t : ℝ) (a j) - (t : ℝ)| < δ
  rw [abs_of_nonpos (sub_nonpos.mpr (min_le_left _ _))]
  have hh := hN j hj
  rcases le_total (t : ℝ) (a j) with ht | ht
  · rw [min_eq_left ht]
    linarith
  · rw [min_eq_right ht]
    linarith [t.property.2]

private theorem tendsto_map_stopPrefix (ν : ProbabilityMeasure C(unitInterval, ℝ))
    {a : ℕ → ℝ≥0} (ha : ∀ j, a j ≤ 1)
    (hatop : Tendsto (fun j => (a j : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun j => ν.map (stopPrefix (a j) (ha j))) atTop (𝓝 ν) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro F
  simp_rw [ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_stopPrefix _ _).measurable.aemeasurable
      F.continuous.aestronglyMeasurable]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro j
    exact (F.continuous.comp (continuous_stopPrefix _ _)).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    exact ae_of_all _ fun g => F.norm_coe_le_norm _
  · exact ae_of_all _ fun g => F.continuous.continuousAt.tendsto.comp (tendsto_stopPrefix ha
    hatop g)

private theorem contourLin_nonneg (t : PlaneTree) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ t.contourLin s := by
  have hf := Nat.floor_le hs
  have hfl := Nat.lt_floor_add_one s
  apply add_nonneg <;> apply mul_nonneg
  · linarith
  · positivity
  · linarith
  · positivity

private theorem treeContourPath_nonneg {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {n : ℕ} (hn : 0 < n) (a : ℝ≥0) (τ : LocallyFinite.Tree)
    (s : Icc (0 : ℝ) (a : ℝ)) : 0 ≤ treeContourPath B n a τ s := by
  rw [treeContourPath, dite_eq_left (continuous_treeContourLin _)]
  change 0 ≤ B n / n * treeContourLin τ (2 * (n : ℝ) * s)
  apply mul_nonneg (div_nonneg (h.pos n hn).le (Nat.cast_nonneg _))
  rw [treeContourLin]
  split_ifs
  · exact contourLin_nonneg _ (by nlinarith [s.property.1, Nat.cast_nonneg (α := ℝ) n])
  · exact le_rfl

private theorem extension_error_le {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {n : ℕ} (hn : 0 < n) (a : ℝ≥0) (ha : a ≤ 1)
    (τ : LocallyFinite.Tree) {r : ℝ} (hr : 0 ≤ r)
    (he : contourHeightError B n a τ ≤ r)
    (htail : ∀ s : unitInterval, (a : ℝ) ≤ (s : ℝ) → treeContourPath B n 1 τ s ≤ r) :
    dist (extendPrefix a (treeHeightPath B n a τ)) (treeContourPath B n 1 τ) ≤ 3 * r := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro s
  rw [Real.dist_eq]
  by_cases hs : (s : ℝ) ≤ a
  · have hh := (contourHeightError_ge B n a τ ⟨s, s.property.1, hs⟩).trans he
    simp only [extendPrefix, ContinuousMap.comp_apply, ContinuousMap.coe_mk, min_eq_left hs]
    rw [treeHeightPath, dite_eq_left (continuous_treeHeightLin _),
      treeContourPath, dite_eq_left (continuous_treeContourLin _)]
    change |B n / n * treeHeightLin τ ((n : ℝ) * s) -
      B n / n * treeContourLin τ (2 * (n : ℝ) * s)| ≤ 3 * r
    simp only [treeContourPath, dite_eq_left (continuous_treeContourLin _),
      treeHeightPath, dite_eq_left (continuous_treeHeightLin _), ContinuousMap.coe_mk] at hh
    change |B n / n * treeContourLin τ (2 * (n : ℝ) * s) -
      B n / n * treeHeightLin τ ((n : ℝ) * s)| ≤ r at hh
    rw [abs_sub_comm] at hh
    exact hh.trans (by linarith : r ≤ 3 * r)

  · let sa : unitInterval := ⟨a, a.coe_nonneg, ha⟩
    have hh := (contourHeightError_ge B n a τ ⟨a, a.coe_nonneg, le_rfl⟩).trans he
    have hCa := htail sa le_rfl
    have hCs := htail s (le_of_not_ge hs)
    have hC0 := treeContourPath_nonneg h hn 1 τ s
    have hCa0 := treeContourPath_nonneg h hn 1 τ sa
    have hsame : treeContourPath B n a τ ⟨a, a.coe_nonneg, le_rfl⟩ =
        treeContourPath B n 1 τ sa := by
      simp only [treeContourPath, dite_eq_left (continuous_treeContourLin _),
        ContinuousMap.coe_mk, sa]
    rw [hsame] at hh
    have hH : |treeHeightPath B n a τ ⟨a, a.coe_nonneg, le_rfl⟩| ≤ 2 * r := by
      have hh' := abs_sub_le (treeHeightPath B n a τ ⟨a, a.coe_nonneg, le_rfl⟩)
        (treeContourPath B n 1 τ sa) 0
      rw [sub_zero, sub_zero, abs_of_nonneg hCa0, abs_sub_comm] at hh'
      linarith
    change |treeHeightPath B n a τ ⟨min (s : ℝ) a, _⟩ - treeContourPath B n 1 τ s| ≤ _
    have hse : (⟨min (s : ℝ) a, le_min s.property.1 a.coe_nonneg,
        min_le_right _ _⟩ : Icc (0 : ℝ) (a : ℝ)) = ⟨a, a.coe_nonneg, le_rfl⟩ :=
      Subtype.ext (min_eq_right (le_of_not_ge hs))
    rw [hse]
    have hh' := abs_sub_le (treeHeightPath B n a τ ⟨a, a.coe_nonneg, le_rfl⟩) 0
      (treeContourPath B n 1 τ s)
    simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hC0] at hh'
    linarith

set_option backward.isDefEq.respectTransparency false in
/-- The exact-size contour in the paper clock converges to the excursion height. -/
theorem tendsto_exactContourLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) :
    Tendsto (fun k => (exactTreeLaw μ (q k)).map (treeContourPath B (q k) 1)) atTop
      (𝓝 ((excLaw θ).map Prod.snd)) := by
  let a : ℕ → ℝ≥0 := fun j => ⟨1 - 1 / ((j : ℝ) + 2), by
    have hj := Nat.cast_nonneg (α := ℝ) j
    have hd : (0 : ℝ) < j + 2 := by positivity
    exact sub_nonneg.mpr ((div_le_one hd).mpr (by linarith))⟩
  have ha (j : ℕ) : a j ∈ Ioo (0 : ℝ≥0) 1 := by
    have hj := Nat.cast_nonneg (α := ℝ) j
    have hd : (0 : ℝ) < j + 2 := by positivity
    constructor
    · change (0 : ℝ) < 1 - 1 / ((j : ℝ) + 2)
      exact sub_pos.mpr ((div_lt_one hd).mpr (by linarith))
    · change 1 - 1 / ((j : ℝ) + 2) < 1
      exact sub_lt_self _ (by positivity)
  have hatop : Tendsto (fun j => (a j : ℝ)) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_atTop_add_const_right atTop (2 : ℝ)
        tendsto_natCast_atTop_atTop).const_div_atTop (1 : ℝ))
    change Tendsto (fun j : ℕ => 1 - 1 / ((j : ℝ) + 2)) atTop (𝓝 1)
    simpa only [sub_zero] using hh
  let ν := (excLaw θ).map Prod.snd
  let Z j := ν.map (stopPrefix (a j) (ha j).2.le)
  apply BGW.Probability.tendsto_of_tendsto_approx (fun k => exactTreeLaw μ (q k))
    (X := fun j k τ => extendPrefix (a j) (treeHeightPath B (q k) (a j) τ))
    (Z := Z) (fun k => measurable_treeContourPath B (q k) 1)
    (fun j k => (continuous_extendPrefix _).measurable.comp (measurable_treeHeightPath B (q k)
      (a j)))
  · intro j
    have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
      (tendsto_exactHeight_prefix h hqtop hq (a j) (ha j)) (continuous_extendPrefix (a j))
    convert ht using 1
    · funext k
      apply Subtype.ext
      exact (Measure.map_map (continuous_extendPrefix _).measurable
        (measurable_treeHeightPath B (q k) (a j))).symm
    · congr 1
      apply Subtype.ext
      change ((excLaw θ).toMeasure.map Prod.snd).map (stopPrefix (a j) (ha j).2.le) =
        (((excLaw θ).toMeasure.map (restrictPair (ha j).2.le)).map Prod.snd).map (extendPrefix
          (a j))
      rw [Measure.map_map (continuous_stopPrefix _ _).measurable measurable_snd,
        Measure.map_map (continuous_extendPrefix _).measurable measurable_snd,
        Measure.map_map ((continuous_extendPrefix _).measurable.comp measurable_snd)
          (measurable_restrictPair _)]
      rfl
  · exact tendsto_map_stopPrefix ν (fun j => (ha j).2.le) hatop
  · intro ε hε
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨d, hd, _, hterminal⟩ := exactContour_terminal_small h hqtop hq
      (show 0 < ε / 8 by positivity) (show 0 < η / 4 by positivity)
    have hcut := hatop.eventually (lt_mem_nhds (show 1 - d < 1 by linarith))
    rw [eventually_atTop] at hcut
    obtain ⟨N, hN⟩ := hcut
    refine ⟨N, ?_⟩
    intro j hj
    have hpref := (tendsto_contourHeightError_prefix h hqtop hq (a j) (ha j)
      (show 0 < ε / 8 by positivity)).eventually_le_const (show 0 < η / 4 by positivity)
    have hnn : 0 ≤ limsup (fun k => (exactTreeLaw μ (q k) : Measure LocallyFinite.Tree).real
        {τ | ε ≤ dist (extendPrefix (a j) (treeHeightPath B (q k) (a j) τ))
          (treeContourPath B (q k) 1 τ)}) atTop :=
      le_limsup_of_frequently_le (Frequently.of_forall fun _ => measureReal_nonneg)
        (isBoundedUnder_of ⟨1, fun _ => measureReal_le_one⟩)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    apply lt_of_le_of_lt _ (half_lt_self hη)
    apply limsup_le_of_le (Filter.isCoboundedUnder_le_of_le atTop fun _ => measureReal_nonneg)
    filter_upwards [hpref, hterminal,
      hqtop.eventually (eventually_ge_atTop 1)] with k hkpre hktail hkpos
    have hsub : {τ | ε ≤ dist (extendPrefix (a j) (treeHeightPath B (q k) (a j) τ))
        (treeContourPath B (q k) 1 τ)} ⊆
        {τ | ε / 8 < contourHeightError B (q k) (a j) τ} ∪
        {τ | ∃ t : Icc (0 : ℝ) 1, 1 - d ≤ (t : ℝ) ∧
          ε / 8 < B (q k) / q k * treeContourLin τ (2 * (q k : ℝ) * (t : ℝ))} := by
      intro τ hbad
      by_contra hh
      have he : contourHeightError B (q k) (a j) τ ≤ ε / 8 := by
        exact le_of_not_gt (fun he => hh (Or.inl he))
      have htail (s : unitInterval) (hs : (a j : ℝ) ≤ (s : ℝ)) :
          treeContourPath B (q k) 1 τ s ≤ ε / 8 := by
        by_contra hsbad
        apply hh
        right
        refine ⟨s, (hN j hj).le.trans hs, ?_⟩
        simpa only [treeContourPath, dite_eq_left (continuous_treeContourLin _),
          ContinuousMap.coe_mk] using lt_of_not_ge hsbad
      simp only [Set.mem_ofPred_eq] at hbad
      have hb := extension_error_le h (by omega) (a j) (ha j).2.le τ (by positivity) he htail
      linarith
    exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (by linarith))

end BGW.StableTrees.ExactContour
