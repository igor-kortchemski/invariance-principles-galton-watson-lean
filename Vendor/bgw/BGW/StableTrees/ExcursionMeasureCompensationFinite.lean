/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasurePredictableMeasure
public import BGW.StableTrees.ExcursionMeasureFiniteModification

/-! Finite-box predictable compensation by equality of measures on generating rectangles.

See Bertoin, *Lévy Processes*, Chapter IV, and Kallenberg,
*Foundations of Modern Probability*, Chapters 12 and 22.
-/

@[expose] public section

open MeasureTheory MeasurableSpace Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- Predictable compensation on a bounded time window and a positive lifetime slab. -/
theorem excursion_compensation_predictable_finite {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (K ε : ℝ≥0) (hε : 0 < ε)
    {H : (ℝ≥0 × DLoc) × Excursion → ℝ≥0∞}
    (hH : @Measurable _ _ (predictableSigma.prod inferInstance) _ H) :
    (∫⁻ f, ∫⁻ p in Ioc 0 K ×ˢ {e : Excursion | ε < e.lifetime},
      H ((p.1, f), p.2) ∂(excursionPointMeasure f)
        ∂(stableLocalLaw θ : Measure DLoc)) =
      ∫⁻ q, H q ∂(((lebNN.restrict (Ioc 0 K)).prod
        (stableLocalLaw θ : Measure DLoc)).prod
          ((excursionMeasure θ).restrict {e : Excursion | ε < e.lifetime})) := by
  classical
  let P : Measure DLoc := stableLocalLaw θ
  let Aε := {e : Excursion | ε < e.lifetime}
  let E := Ioc 0 K ×ˢ Aε
  have hAε : MeasurableSet Aε :=
    measurableSet_lt measurable_const measurable_excursion_lifetime
  have hE : MeasurableSet E := measurable_box hAε
  let := sigmaFinite_excursionMeasure hθ
  let := sigmaFinite_lebNN
  let Rfull := ((lebNN.restrict (Ioc 0 K)).prod P).prod
    ((excursionMeasure θ).restrict Aε)
  have hid : @Measurable _ _ inferInstance (predictableSigma.prod inferInstance)
      (id : ((ℝ≥0 × DLoc) × Excursion) → _) :=
    ((measurable_id.mono le_rfl predictableSigma_le_prod).comp measurable_fst).prodMk
      measurable_snd
  let R := @Measure.map _ _ inferInstance (predictableSigma.prod inferInstance) id Rfull
  have hRint := @lintegral_map _ _
    ((inferInstance : MeasurableSpace ℝ≥0).prod inferInstance |>.prod inferInstance)
    (predictableSigma.prod inferInstance) Rfull H id hH hid
  obtain ⟨ν, hν, hνfin, hνae⟩ := exists_finite_modification_excursionPointMeasure hθ K ε hε
  let := hνfin
  let M := fun f => predictableMarkedMeasure f (ν f)
  have hM : Measurable M := measurable_predictableMarkedMeasure hν
  let L := Measure.join (P.map M)
  let : MeasurableSpace ((ℝ≥0 × DLoc) × Excursion) := predictableSigma.prod inferInstance
  let C := insert univ excursionPredictableRectangles
  have hspan : IsCountablySpanning C := ⟨fun _ => univ, fun _ => mem_insert _ _,
    eq_univ_of_forall fun p => mem_iUnion.mpr ⟨0, mem_univ p⟩⟩
  have hgen : (inferInstance : MeasurableSpace ((ℝ≥0 × DLoc) × Excursion)) =
      generateFrom (image2 (· ×ˢ ·) C {A : Set Excursion | MeasurableSet A}) :=
    (@generateFrom_eq_prod _ _ predictableSigma inferInstance C
      {A : Set Excursion | MeasurableSet A} predictableSigma_eq_generate.symm
        generateFrom_measurableSet hspan isCountablySpanning_measurableSet).symm
  have hpi := (isPiSystem_excursionPredictableRectangles.insert_univ).prod
    (isPiSystem_measurableSet (α := Excursion))
  have hset {S : Set (ℝ≥0 × DLoc)} (hS : S ∈ C) : MeasurableSet[predictableSigma] S := by
    rw [predictableSigma_eq_generate]
    exact measurableSet_generateFrom hS
  have hL {S : Set ((ℝ≥0 × DLoc) × Excursion)} (hS : MeasurableSet S) :
      L S = ∫⁻ f, M f S ∂P := by
    change Measure.join _ S = _
    rw [Measure.join_apply hS, lintegral_map (Measure.measurable_coe hS) hM]
  have hrectL {D : Set ℝ≥0} {F : Set DLoc} {A : Set Excursion}
      (hS : MeasurableSet ((D ×ˢ F) ×ˢ A)) :
      L ((D ×ˢ F) ×ˢ A) =
        ∫⁻ f, F.indicator (fun f => excursionPointMeasure f
          ((D ∩ Ioc 0 K) ×ˢ (A ∩ Aε))) f ∂P := by
    rw [hL hS]
    apply lintegral_congr_ae
    filter_upwards [hνae] with f hf
    have hm : @Measurable _ _ inferInstance (predictableSigma.prod inferInstance)
        (fun p : ℝ≥0 × Excursion => ((p.1, f), p.2)) :=
      ((measurable_predictable_timeSection f).comp measurable_fst).prodMk measurable_snd
    change predictableMarkedMeasure f (ν f) _ = _
    rw [predictableMarkedMeasure, Measure.map_apply hm hS, hf,
      Measure.restrict_apply' hE]
    by_cases hfF : f ∈ F
    · rw [indicator_of_mem hfF]
      congr 1
      ext p
      simp [E, hfF, and_assoc, and_left_comm, and_comm]
    · rw [indicator_of_notMem hfF]
      have hz : ((fun p : ℝ≥0 × Excursion => ((p.1, f), p.2)) ⁻¹'
          ((D ×ˢ F) ×ˢ A)) ∩ E = ∅ := by ext p; simp [hfF]
      rw [hz, measure_empty]
  have hrectR {D : Set ℝ≥0} {F : Set DLoc} {A : Set Excursion}
      (hD : MeasurableSet D) (hF : MeasurableSet F) (hA : MeasurableSet A)
      (hS : MeasurableSet ((D ×ˢ F) ×ˢ A)) :
      R ((D ×ˢ F) ×ˢ A) =
        lebNN (D ∩ Ioc 0 K) * P F * excursionMeasure θ (A ∩ Aε) := by
    change (@Measure.map _ _
      ((inferInstance : MeasurableSpace ℝ≥0).prod inferInstance |>.prod inferInstance)
      (predictableSigma.prod inferInstance) id Rfull) _ = _
    rw [Measure.map_apply hid hS]
    change Rfull ((D ×ˢ F) ×ˢ A) = _
    rw [Measure.prod_prod, Measure.prod_prod, Measure.restrict_apply hD,
      Measure.restrict_apply hA]
  have hwholeL : L univ = (K : ℝ≥0∞) * excursionMeasure θ Aε := by
    have heq := hrectL (D := univ) (F := univ) (A := univ) (by simp)
    simp only [univ_prod_univ, univ_inter, indicator_univ] at heq
    rw [heq]
    simpa only [tsub_zero] using
      lintegral_excursionPointMeasure_window hθ (show 0 ≤ K from bot_le) hAε
  have hwholeR : R univ = (K : ℝ≥0∞) * excursionMeasure θ Aε := by
    have heq := hrectR (D := univ) (F := univ) (A := univ) .univ .univ .univ (by simp)
    simpa [P, lebNN_Ioc] using heq
  have : IsFiniteMeasure L := ⟨by
    rw [hwholeL]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top
      (excursionMeasure_lifetime_slab_lt_top hθ hε)⟩
  have hsame : L = R := by
    apply ext_of_generate_finite _ hgen hpi
    · rintro _ ⟨S, hS, A, hA, rfl⟩
      change MeasurableSet A at hA
      rcases hS with rfl | hS
      · have hSL : MeasurableSet (((univ : Set ℝ≥0) ×ˢ (univ : Set DLoc)) ×ˢ A) := by
          simpa using (MeasurableSet.univ.prod hA)
        rw [← univ_prod_univ (α := ℝ≥0) (β := DLoc), hrectL hSL,
          hrectR MeasurableSet.univ MeasurableSet.univ hA hSL]
        simp only [indicator_univ, univ_inter, measure_univ, mul_one]
        simpa only [tsub_zero, lebNN_Ioc] using
          lintegral_excursionPointMeasure_window hθ (show 0 ≤ K from bot_le) (hA.inter hAε)
      rcases hS with ⟨a, b, F, hab, hF, rfl⟩ | ⟨F, hF, rfl⟩
      · have hpred := hset (mem_insert_of_mem _ (Or.inl ⟨a, b, F, hab, hF, rfl⟩))
        have hFm := (isStoppingTime_firstPassageBelow a).measurableSpace_le F hF
        rw [hrectL (hpred.prod hA), hrectR measurableSet_Ioc hFm hA (hpred.prod hA)]
        have hinterval : Ioc a b ∩ Ioc 0 K = Ioc a (min b K) := by
          rw [Ioc_inter_Ioc, max_eq_left (show 0 ≤ a from bot_le)]
        rw [hinterval, lebNN_Ioc]
        by_cases ha : a ≤ min b K
        · have hs := excursion_compensation_step hθ ha (hA.inter hAε)
            (Y := F.indicator (fun _ => 1)) (measurable_const.indicator hF)
          have hprod : (fun f => F.indicator (fun _ => 1) f *
              excursionPointMeasure f (Ioc a (min b K) ×ˢ (A ∩ Aε))) =
              F.indicator (fun f => excursionPointMeasure f
                (Ioc a (min b K) ×ˢ (A ∩ Aε))) := by
            funext f
            by_cases hf : f ∈ F <;> simp [hf]
          rw [hprod] at hs
          simp only [lintegral_indicator hFm, lintegral_const, one_mul,
            Measure.restrict_apply_univ] at hs
          simpa only [P, lintegral_indicator hFm, mul_assoc, mul_left_comm, mul_comm] using hs
        · have hz : Ioc a (min b K) = ∅ := Ioc_eq_empty_of_le (le_of_not_ge ha)
          simp [hz, tsub_eq_zero_of_le (le_of_not_ge ha)]
      · have hpred := hset (mem_insert_of_mem _ (Or.inr ⟨F, hF, rfl⟩))
        have hFm := (isStoppingTime_firstPassageBelow 0).measurableSpace_le F hF
        rw [hrectL (hpred.prod hA),
          hrectR (measurableSet_singleton 0) hFm hA (hpred.prod hA)]
        have hz : ({0} : Set ℝ≥0) ∩ Ioc 0 K = ∅ := by ext t; simp
        simp [hz]
    · rw [hwholeL, hwholeR]
  calc
    _ = ∫⁻ q, H q ∂L := by
      rw [show L = Measure.join (P.map M) from rfl,
        Measure.lintegral_join hH.aemeasurable,
        lintegral_map (Measure.measurable_lintegral hH) hM]
      apply lintegral_congr_ae
      filter_upwards [hνae] with f hf
      have hm : @Measurable _ _ inferInstance (predictableSigma.prod inferInstance)
          (fun p : ℝ≥0 × Excursion => ((p.1, f), p.2)) :=
        ((measurable_predictable_timeSection f).comp measurable_fst).prodMk measurable_snd
      symm
      calc
        (∫⁻ q, H q ∂M f) = ∫⁻ p, H ((p.1, f), p.2) ∂ν f :=
          lintegral_map hH hm
        _ = _ := by rw [hf]
    _ = ∫⁻ q, H q ∂R := by rw [hsame]
    _ = _ := hRint

end BGW.StableTrees
