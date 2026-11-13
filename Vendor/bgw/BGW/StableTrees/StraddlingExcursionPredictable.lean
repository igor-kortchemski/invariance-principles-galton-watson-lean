/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasure

/-!
# Predictable passage starts and fixed levels

Left passage times are predictable by a rational supremum of left-continuous adapted
steps. The diffuse intensity of the marked excursion measure excludes jumps at fixed levels.

## References

J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees
private theorem predictable_passage_step (a : ℝ≥0) :
    Measurable[predictableSigma] (fun p : ℝ≥0 × DLoc =>
      if a < p.1 then (firstPassageBelow a p.2 : ℝ≥0∞) else 0) := by
  apply measurable_predictable_of_leftContinuous (H := fun x f =>
    if a < x then firstPassageBelow a f else 0)
  · intro x
    by_cases hx : a < x
    · simp only [hx, ↓reduceIte]
      exact (isStoppingTime_firstPassageBelow a).measurable.mono
        (IsStoppingTime.measurableSpace_mono (isStoppingTime_firstPassageBelow a)
          (isStoppingTime_firstPassageBelow x) (fun f => firstPassageBelow_mono f hx.le)) le_rfl
    · simp only [hx, ↓reduceIte]
      exact measurable_const
  · intro f x _hx
    by_cases hax : a < x
    · refine (show ContinuousWithinAt (fun _ : ℝ≥0 =>
        (firstPassageBelow a f : ℝ≥0∞)) (Iio x) x from continuousWithinAt_const)
          |>.congr_of_eventuallyEq ?_ ?_
      · have hnear : ∀ᶠ y : ℝ≥0 in 𝓝 x, a < y := Ioi_mem_nhds hax
        filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with y hy
        simp [hy]
      · simp [hax]
    · refine (show ContinuousWithinAt (fun _ : ℝ≥0 => (0 : ℝ≥0∞)) (Iio x) x
        from continuousWithinAt_const).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with y hy
        have hn : ¬ a < y := not_lt_of_ge (hy.le.trans (le_of_not_gt hax))
        simp [hn]
      · simp [hax]

/-- The left passage-time process is measurable for the stopped predictable sigma algebra. -/
theorem measurable_predictable_passageTimeMinus :
    Measurable[predictableSigma] (fun p : ℝ≥0 × DLoc => passageTimeMinus p.1 p.2) := by
  have hrat (x : ℝ≥0) (f : DLoc) :
      (⨆ y : Set.Iio x, firstPassageBelow y f) =
      ⨆ q : ℚ, if 0 ≤ q ∧ (q : ℝ) < (x : ℝ) then
        firstPassageBelow (Real.toNNReal q) f else 0 := by
    apply le_antisymm
    · apply iSup_le
      intro y
      obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn
        (show (y : ℝ) < (x : ℝ) by exact_mod_cast y.2)
      have hq0 : 0 ≤ (q : ℝ) := (by positivity : (0 : ℝ) ≤ (y : ℝ≥0)).trans hyq.le
      have hle : firstPassageBelow y f ≤ firstPassageBelow (Real.toNNReal q) f := by
        apply firstPassageBelow_mono f
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
        exact_mod_cast hyq.le
      apply hle.trans
      apply le_iSup_of_le q
      simp only [show 0 ≤ q from by exact_mod_cast hq0, hqx, and_self, ↓reduceIte, le_rfl]
    · apply iSup_le
      intro q
      by_cases hq : 0 ≤ q ∧ (q : ℝ) < (x : ℝ)
      · simp only [hq]
        have hq0 : 0 ≤ (q : ℝ) := by exact_mod_cast hq.1
        have hqx : Real.toNNReal q < x := by
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]
          exact hq.2
        exact le_iSup (fun y : Set.Iio x => firstPassageBelow y f) ⟨Real.toNNReal q, hqx⟩
      · simp [hq]
  unfold passageTimeMinus
  apply Measurable.untopD 0
  have heq : (fun p : ℝ≥0 × DLoc => ⨆ y : Set.Iio p.1, firstPassageBelow y p.2) =
      fun p => ⨆ q : ℚ, if 0 ≤ q ∧ (q : ℝ) < (p.1 : ℝ) then
        firstPassageBelow (Real.toNNReal q) p.2 else 0 := by
    funext p
    exact hrat p.1 p.2
  rw [heq]
  apply Measurable.iSup
  intro q
  by_cases hq : 0 ≤ q
  · have hqR : 0 ≤ (q : ℝ) := by exact_mod_cast hq
    have heq : (fun p : ℝ≥0 × DLoc =>
        if 0 ≤ q ∧ (q : ℝ) < (p.1 : ℝ) then firstPassageBelow (Real.toNNReal q) p.2 else 0) =
        (fun p : ℝ≥0 × DLoc => if Real.toNNReal q < p.1 then
          firstPassageBelow (Real.toNNReal q) p.2 else 0) := by
      funext p
      simp only [hq, true_and, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hqR]
    rw [heq]
    exact predictable_passage_step _
  · simp only [hq, false_and, ↓reduceIte]
    exact measurable_const

private theorem ae_not_jump_fixed {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), x ∉ passageJumpSet f := by
  let := sigmaFinite_excursionMeasure hθ
  obtain ⟨ξ, hξ, heq⟩ := exists_measurable_modification_excursionPointMeasure hθ
  have hB : MeasurableSet ({x} ×ˢ (univ : Set Excursion)) :=
    (measurableSet_singleton x).prod MeasurableSet.univ
  have hl : lebNN {x} = 0 := by
    have he : MeasurableEmbedding ((↑) : ℝ≥0 → ℝ) :=
      MeasurableEmbedding.subtype_coe measurableSet_Ici
    rw [lebNN, he.comap_apply]
    simp
  have hm : ∫⁻ f, ξ f ({x} ×ˢ (univ : Set Excursion))
      ∂(stableLocalLaw θ : Measure DLoc) = 0 := by
    rw [lintegral_pointMeasure_eq_prod hθ hξ heq hB, Measure.prod_prod, hl, zero_mul]
  have hz : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ξ f ({x} ×ˢ (univ : Set Excursion)) = 0 :=
    (lintegral_eq_zero_iff ((Measure.measurable_coe hB).comp hξ)).mp hm
  filter_upwards [hz, heq, ae_excursionPointMeasure_singleton_prod hθ] with f hf he ha
  rw [he, ha x univ MeasurableSet.univ] at hf
  simpa only [mem_univ, and_true, ite_eq_right_iff, one_ne_zero, imp_false] using hf

/-- At every fixed local-time level, the left passage time equals the passage time a.s. -/
theorem ae_passageTimeMinus_eq_passageTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), passageTimeMinus x f = passageTime x f := by
  filter_upwards [ae_not_jump_fixed hθ x, ae_passageTime_eq_firstPassageBelow hθ]
    with f hn hf
  by_cases hx : x = 0
  · subst x
    simp only [passageTimeMinus, iSup_of_empty, hf.2]
    rfl
  · have hs : (⨆ y : Set.Iio x, firstPassageBelow y f) ≤ firstPassageBelow x f := by
      apply iSup_le
      intro y
      exact firstPassageBelow_mono f y.2.le
    have hfin : firstPassageBelow x f < ⊤ := by rw [hf.1 x]; exact WithTop.coe_lt_top _
    obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top hfin.ne hs)
    have hrep : (⨆ y : Set.Iio x, firstPassageBelow y f) =
        (passageTimeMinus x f : WithTop ℝ≥0) := by
      simp only [passageTimeMinus, ← hu, WithTop.untopD_coe]
    rw [hrep, hf.1 x] at hs
    have hle : passageTimeMinus x f ≤ passageTime x f := by exact_mod_cast hs
    exact le_antisymm hle (le_of_not_gt fun hlt => hn ⟨pos_iff_ne_zero.mpr hx, hlt⟩)
end BGW.StableTrees
