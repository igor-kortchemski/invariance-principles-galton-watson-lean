/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StraddlingExcursionBasic
public import BGW.StableTrees.StraddlingExcursionPredictable

/-!
# Compensation for the straddling excursion

Among the passage marks, exactly one lifetime straddles a fixed positive time.
The predictable compensation formula therefore computes its joint test-function integral.

## References

J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Test functional for a passage start and a mark whose lifetime straddles the fixed time. -/
noncomputable def straddleTest (θ : ℝ) (t : ℝ≥0)
    (F : (ℝ × ℝ) × Excursion → ℝ≥0∞) (g : ℝ≥0) (e : Excursion) : ℝ≥0∞ :=
  if (g : ℝ) < t ∧ (t : ℝ) < (g : ℝ) + e.lifetime then
    F (((g : ℝ), (e.lifetime : ℝ)), normalizeExc θ e) else 0

private theorem measurable_compensation_test (θ : ℝ) (t : ℝ≥0)
    {F : (ℝ × ℝ) × Excursion → ℝ≥0∞} (hF : Measurable F) :
    @Measurable _ _ (predictableSigma.prod inferInstance) _
      (fun p : (ℝ≥0 × DLoc) × Excursion =>
        straddleTest θ t F (passageTimeMinus p.1.1 p.1.2) p.2) := by
  let : MeasurableSpace (ℝ≥0 × DLoc) := predictableSigma
  have hg : Measurable (fun p : (ℝ≥0 × DLoc) × Excursion =>
      (passageTimeMinus p.1.1 p.1.2 : ℝ)) :=
    (measurable_predictable_passageTimeMinus.comp measurable_fst).coe_nnreal_real
  have he : Measurable (fun p : (ℝ≥0 × DLoc) × Excursion => (p.2.lifetime : ℝ)) :=
    (measurable_excursion_lifetime.comp measurable_snd).coe_nnreal_real
  have hn : Measurable (fun p : (ℝ≥0 × DLoc) × Excursion => normalizeExc θ p.2) :=
    (measurable_normalizeExc θ).comp measurable_snd
  exact (hF.comp ((hg.prodMk he).prodMk hn)).ite
    ((measurableSet_lt hg measurable_const).inter
      (measurableSet_lt measurable_const (hg.add he))) measurable_const

/-- Predictable compensation for the unique excursion straddling a positive fixed time. -/
theorem lintegral_straddleData_compensation (θ : ℝ) (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t)
    {F : (ℝ × ℝ) × Excursion → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ f, F (straddleData θ t f) ∂(stableLocalLaw θ : Measure DLoc) =
    ∫⁻ f, ∫⁻ x, ∫⁻ e, straddleTest θ t F (passageTimeMinus x f) e
      ∂excursionMeasure θ ∂lebNN ∂(stableLocalLaw θ : Measure DLoc) := by
  let H : (ℝ≥0 × DLoc) × Excursion → ℝ≥0∞ := fun p =>
    straddleTest θ t F (passageTimeMinus p.1.1 p.1.2) p.2
  have hH : @Measurable _ _ (predictableSigma.prod inferInstance) _ H :=
    measurable_compensation_test θ t hF
  rw [← excursion_compensation_predictable_general hθ hH]
  apply lintegral_congr_ae
  filter_upwards [ae_straddle_spec hθ ht, ae_passageJumpSet_countable hθ,
    ae_jumpExcursion_spec hθ] with f hs hc hj
  have hmeas : Measurable (fun p : ℝ≥0 × Excursion => H ((p.1, f), p.2)) := by
    have hHa : Measurable H :=
      hH.comp (((measurable_id.mono le_rfl predictableSigma_le_prod).comp
        measurable_fst).prodMk measurable_snd)
    exact hHa.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  rw [excursionPointMeasure, ite_eq_left hc, lintegral_sum_measure]
  simp_rw [lintegral_dirac' _ hmeas]
  let j : passageJumpSet f := ⟨localTimeNN f t, hs.1⟩
  have hsingle : ∀ y : passageJumpSet f, y ≠ j →
      H ((y, f), jumpExcursion y f) = 0 := by
    intro y hne
    have hl := (hj y y.2).2.1
    have hle : passageTimeMinus y f ≤ passageTime y f := y.2.2.le
    have hnot : ¬ ((passageTimeMinus y f : ℝ) < t ∧
        (t : ℝ) < (passageTimeMinus y f : ℝ) + (jumpExcursion y f).lifetime) := by
      intro h
      have ht1 : passageTimeMinus y f < t := by exact_mod_cast h.1
      have ht2 : t < passageTime y f := by
        rw [hl, NNReal.coe_sub hle] at h
        exact_mod_cast (by linarith [h.2] : (t : ℝ) < passageTime y f)
      apply hne
      apply Subtype.ext
      exact hs.2.2.2.2.2.2 y y.2 ⟨ht1, ht2⟩
    exact ite_eq_right hnot
  rw [tsum_eq_single j hsingle]
  have htest : ((straddleStart t f : ℝ) < t ∧
      (t : ℝ) < (straddleStart t f : ℝ) + (straddlingExcursion t f).lifetime) := by
    refine ⟨by exact_mod_cast hs.2.1, ?_⟩
    rw [hs.2.2.2.2.2.1]
    dsimp [straddleLife]
    exact_mod_cast (by linarith [show (t : ℝ) < straddleEnd t f from hs.2.2.1] :
      (t : ℝ) < (straddleStart t f : ℝ) +
        ((straddleEnd t f : ℝ) - (straddleStart t f : ℝ)))
  change F (straddleData θ t f) = straddleTest θ t F (straddleStart t f)
    (straddlingExcursion t f)
  rw [straddleTest, ite_eq_left htest]
  rw [hs.2.2.2.2.2.1]
  rfl
end BGW.StableTrees
