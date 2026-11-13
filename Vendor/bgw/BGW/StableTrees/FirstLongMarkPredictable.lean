/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.FirstLongMarkMeasurable
public import BGW.StableTrees.StraddlingExcursionPredictable
import Mathlib.Data.NNRat.Encodable

/-!
# The predictable indicator of no earlier long mark

Stopped measurable rational-window counts give a predictable process which agrees with the
indicator of being at or before the first long label. Its expectation is the Poisson void
probability.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

variable {θ : ℝ}

private noncomputable def stoppedLongCount (hθ : 1 < θ ∧ θ ≤ 2) (q : ℚ≥0)
    (f : DLoc) : ℝ≥0∞ :=
  (exists_stopped_measurable_restrict_Iic hθ (q : ℝ≥0)).choose f
    (Ioc 0 (q : ℝ≥0) ×ˢ {e : Excursion | 1 < e.lifetime})

private theorem measurable_stoppedLongCount (hθ : 1 < θ ∧ θ ≤ 2) (q : ℚ≥0) :
    Measurable[(isStoppingTime_firstPassageBelow (q : ℝ≥0)).measurableSpace]
      (stoppedLongCount hθ q) :=
  (Measure.measurable_coe (measurableSet_Ioc.prod
    (measurableSet_lt measurable_const measurable_excursion_lifetime))).comp
      (exists_stopped_measurable_restrict_Iic hθ (q : ℝ≥0)).choose_spec.1

private theorem ae_stoppedLongCount (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ q : ℚ≥0,
      stoppedLongCount hθ q f =
        excursionPointMeasure f (Ioc 0 (q : ℝ≥0) ×ˢ {e : Excursion | 1 < e.lifetime}) := by
  apply ae_all_iff.mpr
  intro q
  filter_upwards [(exists_stopped_measurable_restrict_Iic hθ (q : ℝ≥0)).choose_spec.2]
    with f hf
  rw [stoppedLongCount, ← hf,
    Measure.restrict_apply (measurableSet_Ioc.prod
      (measurableSet_lt measurable_const measurable_excursion_lifetime))]
  congr 1
  ext p
  simp only [mem_inter_iff, mem_prod, mem_Ioc, mem_Iic, mem_ofPred_eq, mem_univ, and_true]
  tauto

private def hasEarlierLong (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) (f : DLoc) : Prop :=
  ∃ q : ℚ≥0, (q : ℝ≥0) < x ∧ stoppedLongCount hθ q f ≠ 0

open scoped Classical in
private noncomputable def noEarlierLong (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0)
    (f : DLoc) : ℝ≥0∞ :=
  if hasEarlierLong hθ x f then 0 else 1

private theorem measurable_noEarlierLong (hθ : 1 < θ ∧ θ ≤ 2) :
    Measurable[predictableSigma] (fun p : ℝ≥0 × DLoc => noEarlierLong hθ p.1 p.2) := by
  classical
  apply measurable_predictable_of_leftContinuous
  · intro x
    apply Measurable.ite
    · change MeasurableSet[(isStoppingTime_firstPassageBelow x).measurableSpace]
        {f | ∃ q : ℚ≥0, (q : ℝ≥0) < x ∧ stoppedLongCount hθ q f ≠ 0}
      simp only [ofPred_exists]
      apply MeasurableSet.iUnion
      intro q
      by_cases hqx : (q : ℝ≥0) < x
      · simp only [hqx, true_and]
        have hm : Measurable[(isStoppingTime_firstPassageBelow x).measurableSpace]
            (stoppedLongCount hθ q) :=
          (measurable_stoppedLongCount hθ q).mono
            (IsStoppingTime.measurableSpace_mono
              (isStoppingTime_firstPassageBelow (q : ℝ≥0))
              (isStoppingTime_firstPassageBelow x)
              (fun f => firstPassageBelow_mono f hqx.le)) le_rfl
        exact (measurableSet_eq_fun hm measurable_const).compl
      · simp only [hqx, false_and, ofPred_false, MeasurableSet.empty]
    · exact measurable_const
    · exact measurable_const
  · intro f x _hx
    by_cases h : hasEarlierLong hθ x f
    · obtain ⟨q, hqx, hq⟩ := h
      have hx : hasEarlierLong hθ x f := ⟨q, hqx, hq⟩
      refine (show ContinuousWithinAt (fun _ : ℝ≥0 => (0 : ℝ≥0∞)) (Iio x) x
        from continuousWithinAt_const).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [(eventually_gt_nhds hqx).filter_mono nhdsWithin_le_nhds] with y hy
        have hy' : hasEarlierLong hθ y f := ⟨q, hy, hq⟩
        simp only [noEarlierLong, hy', ↓reduceIte]
      · simp only [noEarlierLong, hx, ↓reduceIte]
    · refine (show ContinuousWithinAt (fun _ : ℝ≥0 => (1 : ℝ≥0∞)) (Iio x) x
        from continuousWithinAt_const).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with y hy
        have hn : ¬ hasEarlierLong hθ y f := by
          rintro ⟨q, hqy, hq⟩
          exact h ⟨q, hqy.trans hy, hq⟩
        simp only [noEarlierLong, hn, ↓reduceIte]
      · simp only [noEarlierLong, h, ↓reduceIte]

private theorem ae_noEarlierLong (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x : ℝ≥0,
      noEarlierLong hθ x f = if firstLongLabel f < x then 0 else 1 := by
  classical
  filter_upwards [ae_stoppedLongCount hθ, ae_longCount_eq_zero_iff hθ] with f hs hc
  intro x
  have hiff : hasEarlierLong hθ x f ↔ firstLongLabel f < x := by
    constructor
    · rintro ⟨q, hqx, hq⟩
      have hq' : ¬ (q : ℝ≥0) < firstLongLabel f := fun h => hq ((hs q).trans ((hc q).mpr h))
      exact (le_of_not_gt hq').trans_lt hqx
    · intro h
      obtain ⟨q, hLq, hqx⟩ := exists_rat_btwn
        (show (firstLongLabel f : ℝ) < x from h)
      let q' : ℚ≥0 := ⟨q, by exact_mod_cast ((firstLongLabel f).2.trans hLq.le)⟩
      have hLq' : firstLongLabel f < (q' : ℝ≥0) := by exact_mod_cast hLq
      refine ⟨q', by exact_mod_cast hqx, ?_⟩
      rw [hs q']
      exact fun hz => (not_lt_of_ge hLq'.le) ((hc q').mp hz)
  simp only [noEarlierLong, hiff]

/-- A predictable version of the indicator that the first long label has not yet passed. -/
theorem exists_predictable_firstLongIndicator (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ H : ℝ≥0 → DLoc → ℝ≥0∞,
      Measurable[predictableSigma] (fun p : ℝ≥0 × DLoc => H p.1 p.2) ∧
      (∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x : ℝ≥0,
        H x f = if firstLongLabel f < x then 0 else 1) ∧
      ∀ x : ℝ≥0, (∫⁻ f, H x f ∂(stableLocalLaw θ : Measure DLoc)) =
        ENNReal.ofReal (Real.exp (-((x : ℝ) * longRate θ))) := by
  classical
  refine ⟨noEarlierLong hθ, measurable_noEarlierLong hθ, ae_noEarlierLong hθ, ?_⟩
  intro x
  rw [← measure_no_longMarks hθ x]
  obtain ⟨ξ, hξ, hξeq⟩ := exists_measurable_modification_excursionPointMeasure hθ
  have hset : MeasurableSet {f | ξ f
      (Ioc 0 x ×ˢ {e : Excursion | 1 < e.lifetime}) = 0} :=
    measurableSet_eq_fun (measurable_count hξ (measurableSet_Ioc.prod
      (measurableSet_lt measurable_const measurable_excursion_lifetime))) measurable_const
  calc
    _ = ∫⁻ f, {f | ξ f (Ioc 0 x ×ˢ {e : Excursion | 1 < e.lifetime}) = 0}.indicator
        1 f ∂(stableLocalLaw θ : Measure DLoc) := by
      apply lintegral_congr_ae
      filter_upwards [ae_noEarlierLong hθ, ae_longCount_eq_zero_iff hθ,
        ae_firstLongLabel_mem hθ, ae_passageTimeMinus_eq_passageTime hθ x, hξeq]
        with f hf hc hL hx hξf
      have hne : firstLongLabel f ≠ x := fun h => (h ▸ hL.1.2).ne hx
      simp only [hf x, Set.indicator_apply, mem_ofPred_eq, Pi.one_apply, hξf, hc x]
      rcases lt_or_gt_of_ne hne with h | h <;> simp [h, not_lt_of_ge h.le]
    _ = _ := by
      rw [lintegral_indicator_one hset]
      apply measure_congr
      filter_upwards [hξeq] with f hf
      simp only [hf]

end BGW.StableTrees
