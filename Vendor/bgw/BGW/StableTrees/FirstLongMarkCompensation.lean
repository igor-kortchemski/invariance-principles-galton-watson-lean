/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.FirstLongMarkPredictable

/-!
# Compensation at the first long excursion

The predictable no-earlier-mark indicator leaves exactly one term in the marked sum.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

variable {θ : ℝ}

private theorem predictable_fst :
    Measurable[predictableSigma] (Prod.fst : ℝ≥0 × DLoc → ℝ≥0) := by
  have h : Measurable[predictableSigma] (fun p : ℝ≥0 × DLoc => (p.1 : ℝ≥0∞)) :=
    measurable_predictable_of_leftContinuous (fun _ => measurable_const)
      (fun _ _ _ => ENNReal.continuous_coe.continuousAt.continuousWithinAt)
  simpa only [ENNReal.toNNReal_coe] using h.ennreal_toNNReal

/-- Nonnegative tests of the first label and mark, evaluated by predictable compensation. -/
theorem lintegral_firstLong_pair (hθ : 1 < θ ∧ θ ≤ 2)
    {F : ℝ≥0 × Excursion → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ f, F (firstLongLabel f, firstLongMark f) ∂(stableLocalLaw θ : Measure DLoc)) =
      ∫⁻ x, ENNReal.ofReal (Real.exp (-((x : ℝ) * longRate θ))) *
        (∫⁻ e in {e : Excursion | 1 < e.lifetime}, F (x, e) ∂excursionMeasure θ) ∂lebNN := by
  classical
  let := sigmaFinite_excursionMeasure hθ
  let := sigmaFinite_lebNN
  let P : Measure DLoc := stableLocalLaw θ
  let A : Set Excursion := {e | 1 < e.lifetime}
  have hA : MeasurableSet A := measurableSet_lt measurable_const measurable_excursion_lifetime
  obtain ⟨H, hH, hHeq, hHmean⟩ := exists_predictable_firstLongIndicator hθ
  let J : (ℝ≥0 × DLoc) × Excursion → ℝ≥0∞ := fun p =>
    H p.1.1 p.1.2 * A.indicator (fun e => F (p.1.1, e)) p.2
  have hJ : @Measurable _ _ (predictableSigma.prod inferInstance) _ J := by
    let : MeasurableSpace (ℝ≥0 × DLoc) := predictableSigma
    have htime : Measurable (fun p : (ℝ≥0 × DLoc) × Excursion => p.1.1) :=
      predictable_fst.comp measurable_fst
    exact (hH.comp measurable_fst).mul
      ((hF.comp (htime.prodMk measurable_snd)).indicator (measurable_snd hA))
  have hJambient : Measurable J :=
    hJ.comp (((measurable_id.mono le_rfl predictableSigma_le_prod).comp
      measurable_fst).prodMk measurable_snd)
  have hsingle : (∫⁻ f, F (firstLongLabel f, firstLongMark f) ∂P) =
      ∫⁻ f, ∫⁻ p, J ((p.1, f), p.2) ∂excursionPointMeasure f ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hHeq, ae_exists_longLabel hθ, ae_jumpExcursion_spec hθ,
      ae_passageJumpSet_countable hθ] with f hf hleast hs hc
    obtain ⟨L, hL⟩ := hleast
    have hlabel : firstLongLabel f = L := firstLongLabel_eq_of_isLeast hL
    have hmem : firstLongLabel f ∈ longLabelSet f := hlabel.symm ▸ hL.1
    let j : passageJumpSet f := ⟨firstLongLabel f, hmem.1⟩
    have hjmeas : Measurable (fun p : ℝ≥0 × Excursion => J ((p.1, f), p.2)) :=
      hJambient.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
    rw [excursionPointMeasure, ite_eq_left hc, lintegral_sum_measure]
    simp_rw [lintegral_dirac' _ hjmeas]
    have hzero (y : passageJumpSet f) (hy : y ≠ j) : J ((y, f), jumpExcursion y f) = 0 := by
      by_cases hlong : jumpExcursion y f ∈ A
      · have hyLong : (y : ℝ≥0) ∈ longLabelSet f := ⟨y.2, by
          change 1 < (jumpExcursion y f).lifetime at hlong
          rwa [(hs y y.2).2.1] at hlong⟩
        have hle : firstLongLabel f ≤ y := by rw [hlabel]; exact hL.2 hyLong
        have hne : firstLongLabel f ≠ (y : ℝ≥0) := fun h => hy (Subtype.ext h.symm)
        have hlt : firstLongLabel f < y := lt_of_le_of_ne hle hne
        simp only [J, hf, hlt, ↓reduceIte, zero_mul]
      · simp only [J, Set.indicator_of_notMem hlong, mul_zero]
    rw [tsum_eq_single j hzero]
    have hjlong : jumpExcursion (firstLongLabel f) f ∈ A := by
      change 1 < (jumpExcursion (firstLongLabel f) f).lifetime
      rw [(hs _ hmem.1).2.1]
      exact hmem.2
    simp only [J, hf, j, lt_self_iff_false, ↓reduceIte,
      Set.indicator_of_mem hjlong, one_mul, firstLongMark]
  rw [hsingle, excursion_compensation_predictable_general hθ hJ]
  let K : ℝ≥0 → ℝ≥0∞ := fun x => ∫⁻ e in A, F (x, e) ∂excursionMeasure θ
  have hK : Measurable K := hF.lintegral_prod_right'
  have hHambient : Measurable (fun p : ℝ≥0 × DLoc => H p.1 p.2) :=
    hH.mono predictableSigma_le_prod le_rfl
  have heval (f : DLoc) (x : ℝ≥0) :
      (∫⁻ e, J ((x, f), e) ∂excursionMeasure θ) = H x f * K x := by
    change (∫⁻ e, H x f * A.indicator (fun e => F (x, e)) e ∂excursionMeasure θ) = _
    have hFx : Measurable (fun e : Excursion => F (x, e)) :=
      hF.comp measurable_prodMk_left
    rw [lintegral_const_mul _ (hFx.indicator hA), lintegral_indicator hA]
  simp_rw [heval]
  have hmeas : Measurable (fun p : DLoc × ℝ≥0 => H p.2 p.1 * K p.2) :=
    (hHambient.comp measurable_swap).mul (hK.comp measurable_snd)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  apply lintegral_congr
  intro x
  have hHx : Measurable (fun f : DLoc => H x f) :=
    hHambient.comp measurable_prodMk_left
  rw [lintegral_mul_const _ hHx, hHmean x]

end BGW.StableTrees
