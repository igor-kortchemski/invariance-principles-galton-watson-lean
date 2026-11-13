/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureIntensity

/-! Compensation for tests measurable in the stopped past at a deterministic local-time level.

See Bertoin, *Lévy Processes*, Chapter IV, and Kallenberg,
*Foundations of Modern Probability*, Chapters 12 and 22.
-/

@[expose] public section

open MeasureTheory MeasurableSpace Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- The mean window formula also holds for the original point measure. -/
theorem lintegral_excursionPointMeasure_window {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {a b : ℝ≥0} (hab : a ≤ b) {A : Set Excursion} (hA : MeasurableSet A) :
    (∫⁻ f, excursionPointMeasure f (Ioc a b ×ˢ A) ∂(stableLocalLaw θ : Measure DLoc)) =
      ((b - a : ℝ≥0) : ℝ≥0∞) * excursionMeasure θ A := by
  obtain ⟨ξ, hξ, hae⟩ := exists_measurable_modification_excursionPointMeasure hθ
  rw [← lintegral_windowMark_eq hθ hξ hae hab hA]
  apply lintegral_congr_ae
  exact hae.mono fun f hf => congrArg (fun μ => μ (Ioc a b ×ˢ A)) hf.symm

private theorem aemeasurable_future_excursionPointMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (a : ℝ≥0) : AEMeasurable
    (fun f => excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f))
      (stableLocalLaw θ : Measure DLoc) := by
  have hm : Measurable (fun μ : Measure (ℝ≥0 × Excursion) =>
      ((μ.restrict (Ioi a ×ˢ univ)).map (fun p => (p.1 - a, p.2)))) :=
    (Measure.measurable_map _ (by fun_prop)).comp
      (measurable_restrict_pointMeasure measurable_id
        (measurableSet_Ioi.prod MeasurableSet.univ))
  exact (hm.comp_aemeasurable (aemeasurable_excursionPointMeasure hθ)).congr
    ((ae_excursionPointMeasure_shift hθ).mono fun f hf => (hf a).symm)

/-- The future marked process is independent of every test measurable in the stopped past. -/
theorem indepFun_stopped_future_excursionPointMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (a : ℝ≥0) {Y : DLoc → ℝ≥0∞}
    (hY : Measurable[(isStoppingTime_firstPassageBelow a).measurableSpace] Y) :
    IndepFun Y (fun f => excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f))
      (stableLocalLaw θ : Measure DLoc) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro S B hS hB
  rw [measure_inter_excursionPointMeasure_shiftAt hθ a (hY hS) hB]
  congr 1
  rw [← Measure.map_apply_of_aemeasurable
    (aemeasurable_future_excursionPointMeasure hθ a) hB,
    map_excursionPointMeasure_shiftAt hθ a,
    Measure.map_apply_of_aemeasurable (aemeasurable_excursionPointMeasure hθ) hB]

private theorem ae_future_count_eq_window {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {a b : ℝ≥0} (hab : a ≤ b) {A : Set Excursion} (hA : MeasurableSet A) :
    (fun f => excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f)
      (Ioc 0 (b - a) ×ˢ A)) =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      (fun f => excursionPointMeasure f (Ioc a b ×ˢ A)) := by
  filter_upwards [ae_excursionPointMeasure_shift hθ] with f hf
  rw [hf a, Measure.map_apply (by fun_prop) (measurable_box hA),
    Measure.restrict_apply ((show Measurable
      (fun p : ℝ≥0 × Excursion => (p.1 - a, p.2)) from by fun_prop)
        (measurable_box hA))]
  congr 1
  ext p
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_Ioc, mem_Ioi, mem_univ,
    and_true, tsub_pos_iff_lt, tsub_le_iff_right, tsub_add_cancel_of_le hab]
  tauto

/-- **Step compensation** relative to `F_{T_a}`: for `Y` measurable in the stopped σ-algebra of
`T_a` (not merely the natural history of the point measure), `a ≤ b`, measurable `A`:
`E[Y · μ((a,b] × A)] = E[Y] (b - a) N(A)`. -/
theorem excursion_compensation_step {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {a b : ℝ≥0} (hab : a ≤ b)
    {A : Set Excursion} (hA : MeasurableSet A) {Y : DLoc → ℝ≥0∞}
    (hY : Measurable[(isStoppingTime_firstPassageBelow a).measurableSpace] Y) :
    ∫⁻ f, Y f * excursionPointMeasure f (Ioc a b ×ˢ A) ∂(stableLocalLaw θ : Measure DLoc) =
      (∫⁻ f, Y f ∂(stableLocalLaw θ : Measure DLoc)) *
        (((b - a : ℝ≥0) : ℝ≥0∞) * excursionMeasure θ A) := by
  let Z : DLoc → Measure (ℝ≥0 × Excursion) :=
    fun f => excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f)
  let C : Measure (ℝ≥0 × Excursion) → ℝ≥0∞ := fun μ => μ (Ioc 0 (b - a) ×ˢ A)
  have hC : Measurable C := Measure.measurable_coe (measurable_box hA)
  have hZ : AEMeasurable Z (stableLocalLaw θ : Measure DLoc) :=
    aemeasurable_future_excursionPointMeasure hθ a
  have hYm : Measurable Y :=
    hY.mono (isStoppingTime_firstPassageBelow a).measurableSpace_le le_rfl
  have hind : IndepFun Y (fun f => C (Z f)) (stableLocalLaw θ : Measure DLoc) :=
    (indepFun_stopped_future_excursionPointMeasure hθ a hY).comp measurable_id hC
  have hmean : (∫⁻ f, C (Z f) ∂(stableLocalLaw θ : Measure DLoc)) =
      ((b - a : ℝ≥0) : ℝ≥0∞) * excursionMeasure θ A := by
    rw [← lintegral_map' hC.aemeasurable hZ, map_excursionPointMeasure_shiftAt hθ a,
      lintegral_map' hC.aemeasurable (aemeasurable_excursionPointMeasure hθ)]
    simpa [C] using lintegral_excursionPointMeasure_window hθ ((show 0 ≤ b - a from bot_le)) hA
  calc
    _ = ∫⁻ f, Y f * C (Z f) ∂(stableLocalLaw θ : Measure DLoc) := by
      apply lintegral_congr_ae
      exact (ae_future_count_eq_window hθ hab hA).mono fun f hf =>
        congrArg (Y f * ·) hf.symm
    _ = (∫⁻ f, Y f ∂(stableLocalLaw θ : Measure DLoc)) *
        (∫⁻ f, C (Z f) ∂(stableLocalLaw θ : Measure DLoc)) :=
      lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hYm.aemeasurable
        (hC.comp_aemeasurable hZ) hind
    _ = _ := by rw [hmean]

end BGW.StableTrees
