/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureCompensationGeneral
public import BGW.StableTrees.ExcursionMeasurePredictableLeft

/-! Compensation for left-continuous adapted processes, deduced from predictable compensation.

See Bertoin, *Lévy Processes*, Chapter IV, and Kallenberg,
*Foundations of Modern Probability*, Chapters 12 and 22.
-/

@[expose] public section

open MeasureTheory MeasurableSpace Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- **Predictable compensation formula**: `H x ·` is `F_{T_x}`-measurable and `x ↦ H x f` is
left-continuous on `(0,∞)` (a left-continuous adapted, hence predictable, integrand), `G ≥ 0`
measurable on excursions, `K ≥ 0`:
`E ∑_{x ∈ J, x ≤ K} H(x,f) G(e_x) = E[∫_0^K H(x,f) dx] · ∫ G dN`. -/
theorem excursion_compensation_predictable {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (K : ℝ≥0)
    {H : ℝ≥0 → DLoc → ℝ≥0∞}
    (hadapted : ∀ x, Measurable[(isStoppingTime_firstPassageBelow x).measurableSpace] (H x))
    (hleft : ∀ f x, 0 < x → ContinuousWithinAt (fun y => H y f) (Iio x) x)
    {G : Excursion → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ f, ∫⁻ p in Ioc 0 K ×ˢ univ, H p.1 f * G p.2 ∂(excursionPointMeasure f)
        ∂(stableLocalLaw θ : Measure DLoc) =
      (∫⁻ f, ∫⁻ x in Ioc 0 K, H x f ∂lebNN
          ∂(stableLocalLaw θ : Measure DLoc)) *
        ∫⁻ e, G e ∂(excursionMeasure θ) := by
  let := sigmaFinite_excursionMeasure hθ
  let := sigmaFinite_lebNN
  have hHp := measurable_predictable_of_leftContinuous hadapted hleft
  have hHfull : Measurable (fun p : ℝ≥0 × DLoc => H p.1 p.2) :=
    hHp.mono predictableSigma_le_prod le_rfl
  have hK : MeasurableSet[predictableSigma] (Ioc 0 K ×ˢ (univ : Set DLoc)) := by
    rw [predictableSigma_eq_generate]
    exact measurableSet_generateFrom (mem_insert_of_mem _ (Or.inl
      ⟨0, K, univ, bot_le, MeasurableSet.univ, rfl⟩))
  let J : (ℝ≥0 × DLoc) × Excursion → ℝ≥0∞ := fun q =>
    (Ioc 0 K ×ˢ (univ : Set DLoc)).indicator
      (fun p => H p.1 p.2) q.1 * G q.2
  have hJ : @Measurable _ _ (predictableSigma.prod inferInstance) _ J :=
    ((hHp.indicator hK).comp measurable_fst).mul (hG.comp measurable_snd)
  have hleftJ (f : DLoc) :
      (∫⁻ p, J ((p.1, f), p.2) ∂(excursionPointMeasure f)) =
        ∫⁻ p in Ioc 0 K ×ˢ univ, H p.1 f * G p.2 ∂(excursionPointMeasure f) := by
    rw [← lintegral_indicator (measurable_box MeasurableSet.univ)]
    apply lintegral_congr
    intro p
    by_cases hp : p.1 ∈ Ioc 0 K <;> simp [J, hp]
  have heint (f : DLoc) (x : ℝ≥0) :
      (∫⁻ e, J ((x, f), e) ∂(excursionMeasure θ)) =
        (Ioc 0 K).indicator (fun x => H x f) x * ∫⁻ e, G e ∂(excursionMeasure θ) := by
    by_cases hx : x ∈ Ioc 0 K <;> simp [J, hx, lintegral_const_mul _ hG]
  have htime (f : DLoc) : Measurable (fun x => H x f) :=
    hHfull.comp measurable_prodMk_right
  have hint : Measurable (fun f => ∫⁻ x in Ioc 0 K, H x f ∂lebNN) :=
    hHfull.lintegral_prod_left'
  calc
    _ = ∫⁻ f, ∫⁻ p, J ((p.1, f), p.2) ∂(excursionPointMeasure f)
        ∂(stableLocalLaw θ : Measure DLoc) := by simp_rw [hleftJ]
    _ = ∫⁻ f, ∫⁻ x, ∫⁻ e, J ((x, f), e) ∂(excursionMeasure θ) ∂lebNN
        ∂(stableLocalLaw θ : Measure DLoc) := excursion_compensation_predictable_general hθ hJ
    _ = _ := by
      simp_rw [heint, lintegral_mul_const _ ((htime _).indicator measurableSet_Ioc),
        lintegral_indicator measurableSet_Ioc]
      exact lintegral_mul_const _ hint

end BGW.StableTrees
