/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCorrectionBasic

/-!
# State and time localization of the error process

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem exit_eq_passage (K : ℝ) (f : DLoc) :
    supReflectedExit K f = DLoc.strictPassageAbove K (supReflectedFromLoc 0 f) := by
  unfold supReflectedExit DLoc.strictPassageAbove
  apply iInf_congr
  intro t
  change (if K < supReflectedFrom 0 f t then (t : ℝ≥0∞) else ⊤) =
    ⨅ (_ : K < supReflectedFrom 0 f t), (t : ℝ≥0∞)
  by_cases h : K < supReflectedFrom 0 f t <;> simp [h]

/-- Strict reflected exits are stopping times of the right continuous filtration. -/
theorem isStoppingTime_supReflectedExit (K : ℝ) :
    IsStoppingTime DLoc.filtration (supReflectedExit K) := by
  apply isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro t
  change MeasurableSet[DLoc.filtration t] {f : DLoc | supReflectedExit K f < (t : ℝ≥0∞)}
  have he : {f : DLoc | supReflectedExit K f < t} =
      ⋃ q : {q : ℚ // 0 ≤ q ∧ (q : ℝ) < t},
        {f : DLoc | K < supReflectedFrom 0 f (Real.toNNReal q.1)} := by
    ext f
    change supReflectedExit K f < (t : ℝ≥0∞) ↔ _
    rw [exit_eq_passage]
    have hp := DLoc.strictPassageAbove_lt_iff K (supReflectedFromLoc 0 f) t
    change (DLoc.strictPassageAbove K (supReflectedFromLoc 0 f) < (t : ℝ≥0∞)) ↔
      ∃ q : ℚ, 0 ≤ q ∧ (q : ℝ) < t ∧ K < supReflectedFrom 0 f (Real.toNNReal q) at hp
    apply hp.trans
    simp only [mem_iUnion, mem_ofPred_eq]
    exact ⟨fun ⟨q, hq0, hqt, hq⟩ => ⟨⟨q, hq0, hqt⟩, hq⟩,
      fun ⟨⟨q, hq0, hqt⟩, hq⟩ => ⟨q, hq0, hqt, hq⟩⟩
  rw [he]
  apply MeasurableSet.iUnion
  intro q
  have hqt : Real.toNNReal (q.1 : ℝ) ≤ t :=
    (Real.toNNReal_le_iff_le_coe).mpr q.2.2.le
  have hm : MeasurableSet[DLoc.rawFiltration (Real.toNNReal (q.1 : ℝ))]
      {f : DLoc | K < supReflectedFrom 0 f (Real.toNNReal (q.1 : ℝ))} :=
    measurableSet_lt measurable_const
    (measurable_rawFiltration_supReflectedFrom 0 (Real.toNNReal (q.1 : ℝ)))
  exact ((DLoc.rawFiltration.mono hqt).trans
    (DLoc.rawFiltration.le_rightCont t)) _ hm

/-- The cutoff combines a state exit and a deterministic stopping horizon. -/
theorem isStoppingTime_errCutoff (n : ℕ) : IsStoppingTime DLoc.filtration (errCutoff n) :=
  (isStoppingTime_supReflectedExit n).min (isStoppingTime_const _ (n : ℝ≥0))

private theorem reflected_le_before_exit {K : ℝ} {f : DLoc} {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < supReflectedExit K f) : supReflectedFrom 0 f t ≤ K := by
  by_contra h
  have he : supReflectedExit K f ≤ t :=
    iInf_le_of_le t (by simp only [ite_eq_left (not_le.mp h), le_refl])
  exact ht.not_ge he

/-- No-positive-jump reflection stays below the cutoff even at its exit epoch. -/
theorem ae_supReflectedFrom_le_of_le_errCutoff {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ (n : ℕ) (t : ℝ≥0),
      (t : ℝ≥0∞) ≤ errCutoff n f → supReflectedFrom 0 f t ≤ n := by
  filter_upwards [ae_supReflectedFrom_le_leftLim hθ, ae_eval_zero_stableLocalLaw hθ]
    with f hf h0
  intro n t ht
  have hte : (t : ℝ≥0∞) ≤ supReflectedExit n f := ht.trans (min_le_left _ _)
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ t from zero_le) with htz | ht0
  · subst t
    simp [supReflectedFrom, supRunning_zero, h0]
  · have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht0⟩
    apply (hf 0 t).trans
    apply le_of_tendsto ((isCadlag_supReflectedFrom 0 f).tendsto_nhdsLT_leftLim t)
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact reflected_le_before_exit ((ENNReal.coe_lt_coe.mpr hs).trans_le hte)

end BGW.StableTrees
