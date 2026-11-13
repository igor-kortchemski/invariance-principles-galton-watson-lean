/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.PathTailDefs
public import BGW.StableTrees.PathTailCoding
import BGW.StableTrees.PathTailMeasurable
import BGW.StableTrees.PathTailCoupling
import BGW.StableTrees.PathTailLocalization
import BGW.StableTrees.PathTailGoodEvent
import BGW.StableTrees.PathTailIntegralComparison
import BGW.StableTrees.PathTailLawCoding
import BGW.MetricMeasure.WeakPerturbation

import Mathlib.Data.List.GetD

/-!
# Tail-conditioned tree walk paths

The joint endpoints and cut of the first long block converge by a full-sequence Skorokhod
representation localized at a deterministic source horizon. K02 coding and the uniform closing
comparison identify the tail-conditioned tree-path limit on every positive horizon.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest (tailTreeLaw)

namespace BGW.StableTrees.PathTail

open BGW BGW.Skorokhod BGW.Probability.RealWalk BGW.StableTrees

private theorem last_increment (t : PlaneTree) :
    t.increments.getD (t.increments.length - 1) 0 = -1 := by
  have hn : t.increments ≠ [] := by
    intro he
    have hs := t.sum_increments
    rw [he] at hs
    norm_num at hs
  have hpos : 0 < t.increments.length := List.length_pos_iff.mpr hn
  have hp := t.sum_take_increments_nonneg (i := t.increments.length - 1) (by omega)
  have hl := t.neg_one_le_increment (List.getLast_mem hn)
  have hs := congrArg List.sum (List.dropLast_append_getLast hn)
  rw [List.sum_append, List.sum_singleton, t.sum_increments, List.dropLast_eq_take] at hs
  have he : t.increments.getLast hn = -1 := by omega
  rw [List.getD_eq_getElem _ _ (by omega), ← List.getLast_eq_getElem hn, he]

/-- Uniform closing error between the tree path and the closed path (transfers to J1 with the
identity time change). -/
theorem treePrefixPath_close_error (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0)
    (τ : BGW.LocallyFinite.Tree) (t : Set.Icc (0 : ℝ) (T : ℝ)) :
    |treePrefixPath B n T τ t -
      realStepPath (T : ℝ) n (B n) (closedTreeIncrementSeq τ) t| ≤
        |1 / B n| := by
  rw [treePrefixPath, realStepPath_apply, realStepPath_apply, ← sub_div]
  by_cases hτ : BGW.LocallyFinite.FiniteVertices τ
  · obtain ⟨u, rfl⟩ := (BGW.LocallyFinite.exists_toLocallyFinite_iff τ).mpr hτ
    have hu : treeIncrements u.toLocallyFinite = u.increments := by
      rw [treeIncrements, dite_eq_left u.finiteVertices_toLocallyFinite]
      change (PlaneTree.equivFiniteVertices.symm (PlaneTree.equivFiniteVertices u)).increments = _
      rw [Equiv.symm_apply_apply]
    let k := u.increments.length - 1
    have hpos : 0 < u.increments.length := by
      rw [PlaneTree.length_increments]
      exact u.size_pos
    have hdiff (i : ℕ) :
        treeIncrementSeq u.toLocallyFinite i - closedTreeIncrementSeq u.toLocallyFinite i =
          if i = k then -1 else 0 := by
      by_cases hi : i + 1 < u.increments.length
      · have hik : i ≠ k := by dsimp [k]; omega
        simp only [closedTreeIncrementSeq, hu, ite_eq_left hi, ite_eq_right hik, sub_self]
      · by_cases hik : i = k
        · subst i
          simp only [closedTreeIncrementSeq, hu, ite_eq_right hi, sub_zero, ite_true]
          simp only [treeIncrementSeq, hu, k]
          rw [last_increment]
          norm_num
        · have hout : u.increments.length ≤ i := by dsimp [k] at hik; omega
          simp only [closedTreeIncrementSeq, treeIncrementSeq, hu, ite_eq_right hi,
            ite_eq_right hik,
            List.getD_eq_default _ _ hout, Int.cast_zero, sub_self]
    simp only [partialSum]
    rw [← Finset.sum_sub_distrib]
    simp_rw [hdiff]
    rw [Finset.sum_ite_eq']
    split_ifs <;> simp [abs_div]
  · have hi : treeIncrements τ = [] := by simp [treeIncrements, hτ]
    simp [partialSum, treeIncrementSeq, closedTreeIncrementSeq, hi]

/-- The closing estimate also bounds the Skorokhod distance by the identity time change. -/
theorem dist_treePrefixPath_closed_le (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0)
    (τ : BGW.LocallyFinite.Tree) :
    dist (treePrefixPath B n T τ)
      (realStepPath (T : ℝ) n (B n) (closedTreeIncrementSeq τ)) ≤ |1 / B n| := by
  let : Nonempty (Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0, le_rfl, T.2⟩⟩
  refine (dist_le_iSup_dist _ _).trans ?_
  apply ciSup_le
  intro t
  simpa only [Real.dist_eq] using treePrefixPath_close_error B n T τ t

/-- The law of the selected first-long-block triple (endpoints and cut) of the iid walk. -/
noncomputable def selectedBlockTripleLaw (μ : PMF ℕ) (B : ℕ → ℝ)
    (n : ℕ) (T : ℝ≥0) : ProbabilityMeasure (ℝ × ℝ × D (T : ℝ) ℝ) :=
  (iidLaw (realOffspringStepLaw μ)).map (extractionTriple (B n) n T)

/-- Measurability (a.e.) of the extraction triple under the iid law. -/
theorem aemeasurable_extractionTriple {μ : PMF ℕ} {θ : ℝ}
    {B : ℕ → ℝ} (h : StableDomain μ θ B) (n : ℕ) (T : ℝ≥0) :
    AEMeasurable (extractionTriple (B n) n T)
      (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)) := by
  -- The stronger measurable statement does not need the domain assumption.
  have _h := h
  exact (measurable_extractionTriple (B n) n T).aemeasurable

/-- **Joint endpoint/cut convergence of the first long block** (retained for K14). -/
theorem tendsto_selectedBlockTripleLaw {μ : PMF ℕ} {θ : ℝ}
    {B : ℕ → ℝ} (h : StableDomain μ θ B)
    (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => selectedBlockTripleLaw μ B n T) atTop
      (𝓝 ((stableLocalLaw θ).map (longCutTriple T))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro φ
  have hsrc (n : ℕ) : (∫ x, φ x ∂(selectedBlockTripleLaw μ B n T)) =
      ∫ ω, φ (extractionTriple (B n) n T ω) ∂(iidLaw (realOffspringStepLaw μ)) :=
    integral_map (measurable_extractionTriple _ _ _).aemeasurable
      φ.continuous.aestronglyMeasurable
  have htgt : (∫ x, φ x ∂((stableLocalLaw θ).map (longCutTriple T))) =
      ∫ f, φ (longCutTriple T f) ∂(stableLocalLaw θ) :=
    integral_map (aemeasurable_longCutTriple h.alpha_mem T)
      φ.continuous.aestronglyMeasurable
  simp only [hsrc, htgt]
  rw [Metric.tendsto_atTop]
  intro ε hε
  let C : ℝ := ‖φ‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hφ (x : ℝ × ℝ × D (T : ℝ) ℝ) : |φ x| ≤ C := by
    have hh := φ.norm_coe_le_norm x
    rw [Real.norm_eq_abs] at hh
    dsimp [C]
    linarith
  obtain ⟨M, hM, G, hG, hsmall, hGend⟩ := exists_firstLongEnd_good_set h.alpha_mem
    (show 0 < ε / (8 * C) by positivity)
  obtain ⟨η, Y, hYm, hYlaw, hFlaw, hcouple⟩ := exists_localized_extraction_coupling h M T hM hT
  let Γ := unitInterval × DLoc
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
  let a (n : ℕ) (ω : ℕ → ℝ) := φ (extractionTriple (B n) n T ω)
  let b (n : ℕ) (y : D (M : ℝ) ℝ) :=
    φ (extractionTriple (B n) n T (reconstructIncrements M n (B n) y))
  let o (n : ℕ) := realStepPath (M : ℝ) n (B n)
  let z (p : Γ) := φ (longCutTriple T p.2)
  let E (n : ℕ) : Set (D (M : ℝ) ℝ) := {y |
    firstLongIndex n (reconstructIncrements M n (B n) y) ∈
      longBlockSet n (reconstructIncrements M n (B n) y) ∧
    ladderTime (reconstructIncrements M n (B n) y)
      (firstLongIndex n (reconstructIncrements M n (B n) y) + 1) ≤ ⌊(n : ℝ) * M⌋₊}
  have hEm (n : ℕ) : MeasurableSet (E n) :=
    (measurable_reconstructIncrements M n (B n))
      (measurableSet_extractionLocalEvent ⌊(n : ℝ) * M⌋₊ n)
  have ham (n : ℕ) : Measurable (a n) :=
    φ.continuous.measurable.comp (measurable_extractionTriple _ _ _)
  have hbm (n : ℕ) : Measurable (b n) :=
    (ham n).comp (measurable_reconstructIncrements M n (B n))
  have hom (n : ℕ) : Measurable (o n) := measurable_realStepPath _ _ _
  have hzm : AEStronglyMeasurable z (η : Measure Γ) := by
    have hm := aemeasurable_longCutTriple h.alpha_mem T
    rw [← hFlaw] at hm
    exact (φ.continuous.measurable.comp_aemeasurable
      (hm.comp_measurable measurable_snd)).aestronglyMeasurable
  have hexact (n : ℕ) (ω : ℕ → ℝ) (hEω : o n ω ∈ E n) : a n ω = b n (o n ω) := by
    have hp : ∀ i < ⌊(n : ℝ) * M⌋₊,
        reconstructIncrements M n (B n) (o n ω) i = ω i := by
      intro i hi
      have hn : 0 < n := by
        by_contra hn
        have hz : n = 0 := by omega
        simp [hz] at hi
      exact reconstructIncrements_stepPath hn (h.pos n (by omega)).ne' ω hi
    exact congrArg φ (extractionTriple_eq_of_prefix hp hEω.1 hEω.2 (B n) T)
  have hconv : ∀ᵐ p ∂(η : Measure Γ), p ∈ G' →
      Tendsto (fun n => b n (Y n p)) atTop (𝓝 (z p)) ∧
        ∀ᶠ n in atTop, Y n p ∈ E n := by
    filter_upwards [hcouple, hGend'] with p hp hg hpg
    obtain ⟨hc, he⟩ := hp.2 (hg.mp hpg)
    exact ⟨φ.continuous.continuousAt.tendsto.comp hc, he⟩
  have hest := eventually_abs_integral_sub_le_of_reconstruction
    (iidLaw (realOffspringStepLaw μ)) η a b o Y z ham hbm hom hYm hzm hYlaw E hEm
    hexact G' hG' hC.le (fun n ω => hφ _) (fun n y => hφ _) (fun p => hφ _) hconv
    (show 0 < ε / 2 by positivity)
  have hbad : 4 * C * (η : Measure Γ).real G'ᶜ < ε / 2 := by
    rw [hmass]
    have hh := (mul_lt_mul_of_pos_left hsmall (show 0 < 4 * C by positivity))
    have heq : 4 * C * (ε / (8 * C)) = ε / 2 := by field_simp; ring
    rwa [heq] at hh
  have hzt : (∫ p, z p ∂(η : Measure Γ)) =
      ∫ f, φ (longCutTriple T f) ∂(stableLocalLaw θ) := by
    have hm : AEStronglyMeasurable (fun f : DLoc => φ (longCutTriple T f))
        ((η : Measure Γ).map Prod.snd) := by
      rw [hFlaw]
      exact (φ.continuous.measurable.comp_aemeasurable
        (aemeasurable_longCutTriple h.alpha_mem T)).aestronglyMeasurable
    have he := integral_map measurable_snd.aemeasurable hm
    rw [hFlaw] at he
    exact he.symm
  rw [hzt] at hest
  obtain ⟨N, hN⟩ := eventually_atTop.mp hest
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  apply (hN n hn).trans
  linarith only [hbad]

/-- **Tail walk path theorem (K05b main theorem).**  For every `T > 0` the tail-conditioned tree
path on `[0,T]` converges weakly to the excursion under `N(· | ζ > 1)` restricted to `[0,T]`. -/
theorem tendsto_tailWalkLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => tailWalkLaw μ B n T) atTop
      (𝓝 (tailLevyExcLaw θ T)) := by
  let π : ℝ × ℝ × D (T : ℝ) ℝ → D (T : ℝ) ℝ := fun p => p.2.2
  have hπ : Continuous π := continuous_snd.snd
  have hclosed : Tendsto (fun n => (tailTreeLaw μ n).map (fun τ =>
      realStepPath (T : ℝ) n (B n) (closedTreeIncrementSeq τ))) atTop
        (𝓝 (tailLevyExcLaw θ T)) := by
    have hp := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n => selectedBlockTripleLaw μ B n T)
      ((stableLocalLaw θ).map (longCutTriple T)) (tendsto_selectedBlockTripleLaw h T hT) hπ
    have heq (n : ℕ) : (selectedBlockTripleLaw μ B n T).map π =
        (tailTreeLaw μ n).map (fun τ =>
          realStepPath (T : ℝ) n (B n) (closedTreeIncrementSeq τ)) := by
      apply ProbabilityMeasure.toMeasure_injective
      change Measure.map π (Measure.map (extractionTriple (B n) n T)
          (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ))) = _
      rw [Measure.map_map hπ.measurable (measurable_extractionTriple _ _ _)]
      exact congrArg ProbabilityMeasure.toMeasure (map_selectedBlockCut_eq_closedTail h n T)
    have hlim : ((stableLocalLaw θ).map (longCutTriple T)).map π = tailLevyExcLaw θ T :=
      map_longCutTriple_path h.alpha_mem T
    simpa only [heq, hlim] using hp
  have hB := h.isRealStableAttracted.tendsto_norming_atTop
  have hinv : Tendsto (fun n => |1 / B n|) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, abs_zero, Function.comp_def] using (tendsto_inv_atTop_zero.comp hB).abs
  have herr (ε : ℝ) (hε : 0 < ε) : Tendsto (fun n =>
      (tailTreeLaw μ n : Measure BGW.LocallyFinite.Tree).real {τ |
        ε < dist (treePrefixPath B n T τ)
          (realStepPath (T : ℝ) n (B n) (closedTreeIncrementSeq τ))}) atTop (𝓝 0) := by
    have heq : ∀ᶠ n in atTop,
        (tailTreeLaw μ n : Measure BGW.LocallyFinite.Tree).real {τ |
          ε < dist (treePrefixPath B n T τ)
            (realStepPath (T : ℝ) n (B n) (closedTreeIncrementSeq τ))} = 0 := by
      filter_upwards [hinv.eventually_lt_const hε] with n hn
      have hs : {τ : BGW.LocallyFinite.Tree | ε < dist (treePrefixPath B n T τ)
          (realStepPath (T : ℝ) n (B n) (closedTreeIncrementSeq τ))} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro τ hτ
        exact (not_lt_of_ge (dist_treePrefixPath_closed_le B n T τ)) (hn.trans hτ)
      rw [hs]
      simp
    exact tendsto_const_nhds.congr' (heq.mono fun _ hn => hn.symm)
  exact BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability
    (fun n => tailTreeLaw μ n) (fun n => measurable_treePrefixPath B n T)
    (fun n => measurable_closedTreePrefixPath B n T) herr hclosed

/-- **Form consumed by K07**: along an unbounded sequence, for `a ∈ (0,1)`.  There is
deliberately no admissibility hypothesis: inclusive tail conditioning is not exact-size
conditioning. -/
theorem tendsto_tailWalkPrefixLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop)
    (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    Tendsto (fun k => tailWalkPrefixLaw μ B (q k) a) atTop
      (𝓝 (tailPrefixLimit θ a)) := by
  simpa only [tailWalkPrefixLaw_eq_tailWalkLaw, tailPrefixLimit_eq_tailLevyExcLaw,
    Function.comp_def] using
    (tendsto_tailWalkLaw h a ha.1).comp hqtop

end BGW.StableTrees.PathTail
