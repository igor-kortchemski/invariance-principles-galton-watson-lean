/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightPassagePastSlope
import BGW.StableTrees.ExcursionMeasureCompensationGeneral
import BGW.StableTrees.SupremumFactorizationCompensation

/-!
# Excluding predictable null events at every jump atom

The predictable bad slope event is null at deterministic levels: the full-filter
finite-reading estimate gives the dyadic extended-reading estimate at each fixed positive
level, all conversions taking place on the common finite-passage event.

General predictable compensation on finite level and lifetime boxes then excludes a
predictable event that is null at each deterministic positive level. Countable exhaustion
retains every excursion atom on one host event.
-/

@[expose] public section

open MeasureTheory MeasurableSpace Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The bad predictable left-slope event has probability zero at every fixed positive level. -/
theorem ae_notMem_excursionHeightLeftSlopeBad {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (x : ℝ≥0) (hx : 0 < x) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), (x, f) ∉ excursionHeightLeftSlopeBad := by
  filter_upwards [ae_tendsto_passageTimeMinus_leftSlope hθ x hx,
    ae_passagePast_eq_passageTimeMinus hθ] with f hf hp
  let ε (n : ℕ) : ℝ≥0 := 1 / (2 : ℝ≥0) ^ n
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun n => hεpos n⟩
    have hh := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    simpa [ε, div_eq_mul_inv, inv_pow] using hh
  have hh : Tendsto (fun n => ENNReal.ofReal
      (((passageTimeMinus x f : ℝ) - (passageTimeMinus (x - ε n) f : ℝ)) / (ε n : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.toNNReal_coe, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hf.comp hε)
  change ¬ ¬ Tendsto _ atTop (𝓝 (0 : ℝ≥0∞))
  apply not_not.mpr
  convert hh using 1
  funext n
  rw [hp x, hp (x - ε n), ENNReal.ofReal_div_of_pos
    (show (0 : ℝ) < ε n from hεpos n)]
  have he := ENNReal.ofReal_sub (passageTimeMinus x f : ℝ)
    (q := (passageTimeMinus (x - ε n) f : ℝ)) (NNReal.coe_nonneg _)
  apply congrArg₂ (fun a b : ℝ≥0∞ => a / b)
  · simpa only [ENNReal.ofReal_coe_nnreal] using he.symm
  · simp only [ENNReal.ofReal_coe_nnreal]
    rfl

/-- Predictable events null at each positive deterministic level occur at no jump atom. -/
theorem ae_avoid_predictable_event_at_jumps {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {B : Set (ℝ≥0 × DLoc)} (hB : MeasurableSet[predictableSigma] B)
    (hnull : ∀ x : ℝ≥0, 0 < x → ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), (x, f) ∉ B) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f, (x, f) ∉ B := by
  let P : Measure DLoc := stableLocalLaw θ
  let := sigmaFinite_lebNN
  let := sigmaFinite_excursionMeasure hθ
  have hBfull : MeasurableSet B := predictableSigma_le_prod _ hB
  have hright : ∀ᵐ f ∂P, ∀ᵐ x ∂lebNN, (x, f) ∉ B := by
    apply (MeasureTheory.Measure.ae_ae_comm hBfull.compl).mp
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp lebNN_singleton_zero] with x hx
    have hx0 : x ≠ 0 := by simpa only [mem_singleton_iff] using hx
    exact hnull x (pos_iff_ne_zero.mpr hx0)
  have hbox (n : ℕ) : ∀ᵐ f ∂P, ∀ x ∈ passageJumpSet f,
      (x, jumpExcursion x f) ∈ Ioc 0 (n + 1 : ℝ≥0) ×ˢ excursionLifetimeSlab n →
        (x, f) ∉ B := by
    let E : Set (ℝ≥0 × Excursion) := Ioc 0 (n + 1 : ℝ≥0) ×ˢ excursionLifetimeSlab n
    have hE : MeasurableSet E := measurableSet_Ioc.prod (measurableSet_excursionLifetimeSlab n)
    let H0 (p : (ℝ≥0 × DLoc) × Excursion) : ℝ≥0∞ :=
      (B ×ˢ (univ : Set Excursion)).indicator (fun _ => 1) p
    let H (p : (ℝ≥0 × DLoc) × Excursion) : ℝ≥0∞ :=
      E.indicator (fun _ => H0 p) (p.1.1, p.2)
    have hH0 : @Measurable _ _ (predictableSigma.prod inferInstance) _ H0 := by
      exact measurable_const.indicator (hB.prod MeasurableSet.univ)
    have hH : @Measurable _ _ (predictableSigma.prod inferInstance) _ H := by
      let : MeasurableSpace (ℝ≥0 × DLoc) := predictableSigma
      have hm : Measurable (fun p : (ℝ≥0 × DLoc) × Excursion => (p.1.1, p.2)) :=
        (measurable_predictable_level.comp measurable_fst).prodMk measurable_snd
      exact hH0.indicator (hm hE)
    have hzeroR : (∫⁻ f, ∫⁻ x, ∫⁻ e, H ((x, f), e) ∂excursionMeasure θ ∂lebNN ∂P) = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [hright] with f hf
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [hf] with x hx
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards with e
      simp [H, H0, hx]
    have hzero : (∫⁻ f, ∫⁻ p, H ((p.1, f), p.2) ∂excursionPointMeasure f ∂P) = 0 :=
      (excursion_compensation_predictable_general hθ hH).trans hzeroR
    have hm : AEMeasurable (fun f =>
        ∫⁻ p, H ((p.1, f), p.2) ∂excursionPointMeasure f) P := by
      obtain ⟨ν, hν, hνfin, hae⟩ := exists_finite_modification_excursionPointMeasure hθ
        (n + 1) (1 / (n + 1)) (by positivity)
      let := hνfin
      have hmeas := (Measure.measurable_lintegral hH0).comp
        (measurable_predictableMarkedMeasure hν)
      let : MeasurableSpace ((ℝ≥0 × DLoc) × Excursion) := predictableSigma.prod inferInstance
      apply hmeas.aemeasurable.congr
      filter_upwards [hae] with f hf
      have hsec : @Measurable _ _ inferInstance (predictableSigma.prod inferInstance)
          (fun p : ℝ≥0 × Excursion => ((p.1, f), p.2)) :=
        ((measurable_predictable_timeSection f).comp measurable_fst).prodMk measurable_snd
      change (∫⁻ p, H0 p ∂predictableMarkedMeasure f (ν f)) = _
      rw [predictableMarkedMeasure, lintegral_map hH0 hsec, hf]
      exact (lintegral_indicator hE (fun p => H0 ((p.1, f), p.2))).symm
    filter_upwards [(lintegral_eq_zero_iff' hm).mp hzero,
      ae_passageJumpSet_countable hθ] with f hf hc
    intro x hx hEx hbad
    have hterm : (∫⁻ p, H ((p.1, f), p.2)
        ∂Measure.dirac (x, jumpExcursion x f)) ≤
          ∫⁻ p, H ((p.1, f), p.2) ∂excursionPointMeasure f := by
      rw [excursionPointMeasure, ite_eq_left hc, lintegral_sum_measure]
      exact ENNReal.le_tsum (f := fun i : passageJumpSet f =>
        ∫⁻ p, H ((p.1, f), p.2) ∂Measure.dirac ((i : ℝ≥0), jumpExcursion i f)) ⟨x, hx⟩
    rw [hf, lintegral_dirac] at hterm
    have hone : H ((x, f), jumpExcursion x f) = 1 := by
      have hEx' : (x, jumpExcursion x f) ∈ E := hEx
      simp [H, H0, hEx', hbad]
    rw [hone] at hterm
    exact one_ne_zero (le_antisymm hterm zero_le)
  filter_upwards [ae_all_iff.mpr hbox] with f hf
  intro x hx
  obtain ⟨i, hi⟩ := exists_nat_gt x
  obtain ⟨j, hj⟩ := mem_iUnion.mp (iUnion_excursionLifetimeSlab ▸ mem_univ (jumpExcursion x f))
  apply hf (max i j) x hx
  refine ⟨⟨hx.1, hi.le.trans ?_⟩, monotone_excursionLifetimeSlab (le_max_right i j) hj⟩
  exact_mod_cast (le_max_left i j).trans (Nat.le_succ (max i j))

/-- Almost surely every excursion jump atom has a vanishing dyadic left passage slope. -/
theorem ae_no_bad_leftSlope_at_jumps {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      (x, f) ∉ excursionHeightLeftSlopeBad :=
  ae_avoid_predictable_event_at_jumps hθ measurableSet_excursionHeightLeftSlopeBad
    (ae_notMem_excursionHeightLeftSlopeBad hθ)

end BGW.StableTrees
