/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasurePredictable

/-! Measurable finite random measures on the predictable marked space.

See Bertoin, *Lévy Processes*, Chapter IV, and Kallenberg,
*Foundations of Modern Probability*, Chapters 12 and 22.
-/

@[expose] public section

open MeasureTheory MeasurableSpace Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- Attach the sample path to a time-mark measure, with the predictable target sigma algebra. -/
noncomputable def predictableMarkedMeasure (f : DLoc) (μ : Measure (ℝ≥0 × Excursion)) :
    @Measure ((ℝ≥0 × DLoc) × Excursion) (predictableSigma.prod inferInstance) :=
  @Measure.map _ _ inferInstance (predictableSigma.prod inferInstance)
    (fun p => ((p.1, f), p.2)) μ

private theorem measurable_markedSection (f : DLoc) :
    @Measurable _ _ inferInstance (predictableSigma.prod inferInstance)
      (fun p : ℝ≥0 × Excursion => ((p.1, f), p.2)) :=
  ((measurable_predictable_timeSection f).comp measurable_fst).prodMk measurable_snd

/-- Finite measurable random measures remain measurable after the predictable sample-path
coordinate is attached. This uses the pi system of predictable rectangles. -/
theorem measurable_predictableMarkedMeasure {μ : DLoc → Measure (ℝ≥0 × Excursion)}
    (hμ : Measurable μ) [∀ f, IsFiniteMeasure (μ f)] :
    Measurable (fun f => predictableMarkedMeasure f (μ f)) := by
  let : MeasurableSpace (ℝ≥0 × DLoc) := predictableSigma
  let C := insert univ excursionPredictableRectangles
  have hspan : IsCountablySpanning C := ⟨fun _ => univ, fun _ => mem_insert _ _,
    eq_univ_of_forall fun p => mem_iUnion.mpr ⟨0, mem_univ p⟩⟩
  have hgen : (inferInstance : MeasurableSpace ((ℝ≥0 × DLoc) × Excursion)) =
      generateFrom (image2 (· ×ˢ ·) C {A : Set Excursion | MeasurableSet A}) := by
    exact (generateFrom_eq_prod predictableSigma_eq_generate.symm
      generateFrom_measurableSet hspan isCountablySpanning_measurableSet).symm
  have hpi : IsPiSystem (image2 (· ×ˢ ·) C {A : Set Excursion | MeasurableSet A}) :=
    (isPiSystem_excursionPredictableRectangles.insert_univ).prod isPiSystem_measurableSet
  have hset (S : Set (ℝ≥0 × DLoc)) (hS : S ∈ C) : MeasurableSet S := by
    change MeasurableSet[predictableSigma] S
    rw [predictableSigma_eq_generate]
    exact measurableSet_generateFrom hS
  have hfinite (f : DLoc) : IsFiniteMeasure (predictableMarkedMeasure f (μ f)) := by
    dsimp [predictableMarkedMeasure]
    infer_instance
  let := hfinite
  apply Measurable.measure_of_isPiSystem hgen hpi
  · rintro _ ⟨S, hS, A, hA, rfl⟩
    rcases hS with rfl | hS
    · have heq : (fun f => predictableMarkedMeasure f (μ f) (univ ×ˢ A)) =
          fun f => μ f (univ ×ˢ A) := by
        funext f
        rw [predictableMarkedMeasure, Measure.map_apply (measurable_markedSection f)
          (MeasurableSet.univ.prod hA)]
        rfl
      rw [heq]
      exact measurable_count hμ (MeasurableSet.univ.prod hA)
    rcases hS with ⟨a, b, F, hab, hF, rfl⟩ | ⟨F, hF, rfl⟩
    · have heq : (fun f => predictableMarkedMeasure f (μ f) ((Ioc a b ×ˢ F) ×ˢ A)) =
          F.indicator (fun f => μ f (Ioc a b ×ˢ A)) := by
        funext f
        rw [predictableMarkedMeasure, Measure.map_apply (measurable_markedSection f)
          ((hset _ (mem_insert_of_mem _ (Or.inl ⟨a, b, F, hab, hF, rfl⟩))).prod hA)]
        by_cases hf : f ∈ F
        · rw [indicator_of_mem hf]
          congr 1
          ext p
          simp [hf]
        · rw [indicator_of_notMem hf]
          have hempty : (fun p : ℝ≥0 × Excursion => ((p.1, f), p.2)) ⁻¹'
              ((Ioc a b ×ˢ F) ×ˢ A) = ∅ := by ext p; simp [hf]
          rw [hempty, measure_empty]
      rw [heq]
      exact (measurable_count hμ (measurable_box hA)).indicator
        ((isStoppingTime_firstPassageBelow a).measurableSpace_le F hF)
    · have heq : (fun f => predictableMarkedMeasure f (μ f) (({0} ×ˢ F) ×ˢ A)) =
          F.indicator (fun f => μ f ({0} ×ˢ A)) := by
        funext f
        rw [predictableMarkedMeasure, Measure.map_apply (measurable_markedSection f)
          ((hset _ (mem_insert_of_mem _ (Or.inr ⟨F, hF, rfl⟩))).prod hA)]
        by_cases hf : f ∈ F
        · rw [indicator_of_mem hf]
          congr 1
          ext p
          simp [hf]
        · rw [indicator_of_notMem hf]
          have hempty : (fun p : ℝ≥0 × Excursion => ((p.1, f), p.2)) ⁻¹'
              (({0} ×ˢ F) ×ˢ A) = ∅ := by ext p; simp [hf]
          rw [hempty, measure_empty]
      rw [heq]
      exact (measurable_count hμ ((measurableSet_singleton 0).prod hA)).indicator
        ((isStoppingTime_firstPassageBelow 0).measurableSpace_le F hF)
  · have heq : (fun f => predictableMarkedMeasure f (μ f) univ) = fun f => μ f univ := by
      funext f
      rw [predictableMarkedMeasure, Measure.map_apply (measurable_markedSection f)
        MeasurableSet.univ, preimage_univ]
    rw [heq]
    exact measurable_count hμ MeasurableSet.univ

end BGW.StableTrees
