/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.TailPairBasic
import BGW.StableTrees.TailPairLimit
import BGW.StableTrees.PathTailIntegralComparison
import BGW.StableTrees.PathTailGoodEvent
import BGW.MetricMeasure.WeakPerturbation
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Size-tail convergence of the walk and height pair

The forest pair is coupled along the full sequence and localized where the first long block
ends before a deterministic horizon. Its common endpoints select both coordinates. Letting
the horizon grow removes the localization. The terminal walk step is retained in the main law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees BGW.Probability.RealWalk

namespace BGW.StableTrees.TailPair

open BGW.StableTrees.DiscreteForest BGW.StableTrees.PathTail

/-- The walk closed at the tree size, together with the height of the same tree. -/
noncomputable def closedTreePairPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0)
    (τ : BGW.LocallyFinite.Tree) : D (T : ℝ) ℝ × C(Icc (0 : ℝ) (T : ℝ), ℝ) :=
  (realStepPath (T : ℝ) n (B n) (closedTreeIncrementSeq τ), treeHeightPath B n T τ)

/-- The closed pair path is measurable. -/
theorem measurable_closedTreePairPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (closedTreePairPath B n T) :=
  (measurable_closedTreePrefixPath B n T).prodMk (measurable_treeHeightPath B n T)

/-- The size-tail pair with the walk closed at size converges on every positive horizon. -/
theorem tendsto_tailClosedPairLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n => (tailTreeLaw μ n).map (closedTreePairPath B n T)) atTop
      (𝓝 (tailExcLaw θ T)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro φ
  have hsrc (n : ℕ) : (∫ x, φ x ∂((tailTreeLaw μ n).map (closedTreePairPath B n T))) =
      ∫ ω, φ (closedTreePairPath B n T (firstLongTree n ω)) ∂(offspringSeqLaw μ) := by
    rw [ProbabilityMeasure.toMeasure_map,
      integral_map (measurable_closedTreePairPath B n T).aemeasurable
      φ.continuous.aestronglyMeasurable]
    have hlaw := congrArg ProbabilityMeasure.toMeasure
      (firstLongTree_law μ h.critical h.nondegenerate n)
    rw [← hlaw, ProbabilityMeasure.toMeasure_map]
    exact integral_map (measurable_firstLongTree n).aemeasurable
      (φ.continuous.measurable.comp (measurable_closedTreePairPath B n T)).aestronglyMeasurable
  have htgt : (∫ x, φ x ∂(tailExcLaw θ T)) =
      ∫ f, φ (excursionPair θ T (firstLongMark f)) ∂(stableLocalLaw θ) := by
    rw [← map_firstLongMark_excursionPair h.alpha_mem T]
    exact integral_map ((measurable_excursionPair θ T).comp_aemeasurable
      (aemeasurable_firstLongMark h.alpha_mem)) φ.continuous.aestronglyMeasurable
  simp only [hsrc, htgt]
  rw [Metric.tendsto_atTop]
  intro ε hε
  let C : ℝ := ‖φ‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hφ (x : D (T : ℝ) ℝ × C(Icc (0 : ℝ) (T : ℝ), ℝ)) : |φ x| ≤ C := by
    have hh := φ.norm_coe_le_norm x
    rw [Real.norm_eq_abs] at hh
    dsimp [C]
    linarith
  obtain ⟨M, hM, G, hG, hsmall, hGend⟩ := exists_firstLongEnd_good_set h.alpha_mem
    (show 0 < ε / (8 * C) by positivity)
  obtain ⟨η, Y, hYm, hYlaw, hFlaw, hcouple⟩ := exists_localized_pair_coupling h M T hM hT
  let Γ := unitInterval × DLoc
  let S := D (M : ℝ) ℝ × C(Icc (0 : ℝ) (M : ℝ), ℝ)
  let G' : Set Γ := Prod.snd ⁻¹' G
  have hG' : MeasurableSet G' := measurable_snd hG
  have hmass : (η : Measure Γ).real G'ᶜ = (stableLocalLaw θ : Measure DLoc).real Gᶜ := by
    simp only [measureReal_def]
    congr 1
    rw [← hFlaw, Measure.map_apply measurable_snd hG.compl]
    rfl
  have hGend' : ∀ᵐ p ∂(η : Measure Γ),
      (p ∈ G' ↔ passageTime (firstLongLabel p.2) p.2 < M) := by
    rw [← hFlaw] at hGend
    exact ae_of_ae_map measurable_snd.aemeasurable hGend
  have hlimit : ∀ᵐ p ∂(η : Measure Γ), (firstLongEnds p.2).2 ≤ M →
      cutHeightPath M T (heightPrefix θ M (DLoc.restrict M p.2))
        (firstLongEnds p.2).1 (firstLongEnds p.2).2 =
          (excursionPair θ T (firstLongMark p.2)).2 := by
    have hh := ae_cutHeightPath_firstLongMark h.alpha_mem M T
    rw [← hFlaw] at hh
    exact ae_of_ae_map measurable_snd.aemeasurable hh
  let a (n : ℕ) (ω : ℕ → ℕ) := φ (closedTreePairPath B n T (firstLongTree n ω))
  let b (n : ℕ) (y : S) := φ (extractedForestPair M T (B n) n y)
  let o (n : ℕ) := forestPairPath B n M
  let z (p : Γ) := φ (excursionPair θ T (firstLongMark p.2))
  let E (n : ℕ) : Set S := if n = 0 then ∅ else selectionLocalEvent M (B n) n
  have hEm (n : ℕ) : MeasurableSet (E n) := by
    dsimp [E]
    split_ifs
    · exact MeasurableSet.empty
    · exact measurableSet_selectionLocalEvent M (B n) n
  have ham (n : ℕ) : Measurable (a n) := φ.continuous.measurable.comp
    ((measurable_closedTreePairPath B n T).comp (measurable_firstLongTree n))
  have hbm (n : ℕ) : Measurable (b n) := φ.continuous.measurable.comp
    (measurable_extractedForestPair M T (B n) n)
  have hom (n : ℕ) : Measurable (o n) := measurable_forestPairPath B n M
  have hzm : AEStronglyMeasurable z (η : Measure Γ) := by
    have hm := (measurable_excursionPair θ T).comp_aemeasurable
      (aemeasurable_firstLongMark h.alpha_mem)
    rw [← hFlaw] at hm
    exact (φ.continuous.measurable.comp_aemeasurable
      (hm.comp_measurable measurable_snd)).aestronglyMeasurable
  have hexact (n : ℕ) : ∀ᵐ ω ∂(offspringSeqLaw μ : Measure (ℕ → ℕ)),
      o n ω ∈ E n → a n ω = b n (o n ω) := by
    filter_upwards [ae_ladderFinite μ h.critical h.nondegenerate] with ω hω hE
    have hn : n ≠ 0 := by intro hn; simp [E, hn] at hE
    have hE' : forestPairPath B n M ω ∈ selectionLocalEvent M (B n) n := by
      simpa only [E, ite_eq_right hn] using hE
    exact congrArg φ (extractedForestPair_forestPairPath B (Nat.pos_of_ne_zero hn)
      (h.pos n (Nat.one_le_iff_ne_zero.mpr hn)).ne' M T hω hE').symm
  have hconv : ∀ᵐ p ∂(η : Measure Γ), p ∈ G' →
      Tendsto (fun n => b n (Y n p)) atTop (𝓝 (z p)) ∧
        ∀ᶠ n in atTop, Y n p ∈ E n := by
    filter_upwards [hcouple, hGend', hlimit] with p hp hg hl hpg
    have hend := hg.mp hpg
    obtain ⟨hc, he⟩ := hp.2.2 hend
    have hh := (continuous_cutHeightPath M T).continuousAt.tendsto.comp
      (hp.1.snd_nhds.prodMk_nhds (hc.fst_nhds.prodMk_nhds hc.snd_nhds.fst_nhds))
    have hh' : Tendsto (fun n => (extractedForestPair M T (B n) n (Y n p)).2) atTop
        (𝓝 (excursionPair θ T (firstLongMark p.2)).2) := by
      rw [← hl (le_of_lt hend)]
      exact hh
    have hw : Tendsto (fun n => (extractedForestPair M T (B n) n (Y n p)).1) atTop
        (𝓝 (excursionPair θ T (firstLongMark p.2)).1) := hc.snd_nhds.snd_nhds
    refine ⟨φ.continuous.continuousAt.tendsto.comp (hw.prodMk_nhds hh'), ?_⟩
    filter_upwards [he, eventually_gt_atTop 0] with n hn hnpos
    dsimp only [E]
    rw [ite_eq_right (Nat.ne_of_gt hnpos)]
    exact hn
  have hest := PathTail.eventually_abs_integral_sub_le_of_reconstruction_ae
    (offspringSeqLaw μ) η a b o Y z ham hbm hom hYm hzm hYlaw E hEm
    hexact G' hG' hC.le (fun n ω => hφ _) (fun n y => hφ _) (fun p => hφ _) hconv
    (show 0 < ε / 2 by positivity)
  have hbad : 4 * C * (η : Measure Γ).real G'ᶜ < ε / 2 := by
    rw [hmass]
    have hh := mul_lt_mul_of_pos_left hsmall (show 0 < 4 * C by positivity)
    have heq : 4 * C * (ε / (8 * C)) = ε / 2 := by field_simp; ring
    rwa [heq] at hh
  have hzt : (∫ p, z p ∂(η : Measure Γ)) =
      ∫ f, φ (excursionPair θ T (firstLongMark f)) ∂(stableLocalLaw θ) := by
    have hm : AEStronglyMeasurable (fun f : DLoc => φ (excursionPair θ T (firstLongMark f)))
        ((η : Measure Γ).map Prod.snd) := by
      rw [hFlaw]
      exact (φ.continuous.measurable.comp_aemeasurable
        ((measurable_excursionPair θ T).comp_aemeasurable
          (aemeasurable_firstLongMark h.alpha_mem))).aestronglyMeasurable
    have he := integral_map measurable_snd.aemeasurable hm
    rw [hFlaw] at he
    exact he.symm
  rw [hzt] at hest
  obtain ⟨N, hN⟩ := eventually_atTop.mp hest
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  apply (hN n hn).trans
  linarith only [hbad]

/-- **C28, every positive horizon**: the rescaled (walk, height) pair of a BGW tree conditioned
on size `≥ n` converges jointly to the excursion/height pair under `N(· | ζ > 1)` on `[0,T]`. -/
theorem tendsto_tailPairLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n : ℕ => tailPairLaw μ B n T) atTop (𝓝 (tailExcLaw θ T)) := by
  have herrdist (n : ℕ) (τ : BGW.LocallyFinite.Tree) :
      dist (treePairPath B n T τ) (closedTreePairPath B n T τ) ≤ |1 / B n| := by
    rw [Prod.dist_eq]
    refine max_le (dist_treePrefixPath_closed_le B n T τ) ?_
    change dist (treeHeightPath B n T τ) (treeHeightPath B n T τ) ≤ |1 / B n|
    rw [dist_self]
    exact abs_nonneg _
  have hB := h.isRealStableAttracted.tendsto_norming_atTop
  have hinv : Tendsto (fun n => |1 / B n|) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, abs_zero, Function.comp_def] using (tendsto_inv_atTop_zero.comp hB).abs
  have herr (ε : ℝ) (hε : 0 < ε) : Tendsto (fun n =>
      (tailTreeLaw μ n : Measure BGW.LocallyFinite.Tree).real {τ |
        ε < dist (treePairPath B n T τ) (closedTreePairPath B n T τ)}) atTop (𝓝 0) := by
    have heq : ∀ᶠ n in atTop,
        (tailTreeLaw μ n : Measure BGW.LocallyFinite.Tree).real {τ |
          ε < dist (treePairPath B n T τ) (closedTreePairPath B n T τ)} = 0 := by
      filter_upwards [hinv.eventually_lt_const hε] with n hn
      have hs : {τ : BGW.LocallyFinite.Tree |
          ε < dist (treePairPath B n T τ) (closedTreePairPath B n T τ)} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro τ hτ
        exact (not_lt_of_ge (herrdist n τ)) (hn.trans hτ)
      rw [hs]
      simp
    exact tendsto_const_nhds.congr' (heq.mono fun _ hn => hn.symm)
  exact BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability
    (fun n => tailTreeLaw μ n) (fun n => measurable_treePairPath B n T)
    (fun n => measurable_closedTreePairPath B n T) herr (tendsto_tailClosedPairLaw h hT)

end BGW.StableTrees.TailPair
