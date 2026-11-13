/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumFactorizationCompensation
public import BGW.StableTrees.SupremumFactorizationReversal
public import BGW.StableTrees.SupremumFactorizationResolvent
public import BGW.StableTrees.SupremumFactorizationMeasurable

/-! # Transferring excursion factorization through the exponential clock

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem measurable_infimum_test_real {F G : ℝ → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) :
    Measurable (fun p : ℝ × DLoc =>
      F (localTime p.2 p.1.toNNReal) * G ((reflectedFrom 0 p.2).1 p.1.toNNReal)) := by
  change Measurable (infimumTestReal F G)
  exact measurable_infimumTestReal hF hG

/-- The two excursion factors for the supremum and drawdown, before normalization. -/
theorem lintegral_supRunning_supReflected_excursion_factors {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) {F G : ℝ → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ p, F (supRunning p.1 p.2.toNNReal) * G (supReflected p.1 p.2.toNNReal)
      ∂expClockLaw θ q) =
    (∫⁻ f, (∫⁻ x, expNeg (ENNReal.ofReal q * passagePast x f) * G x ∂lebNN)
      ∂(stableLocalLaw θ : Measure DLoc)) *
      ∫⁻ e, excursionDiscount q F e ∂excursionMeasure θ := by
  have hClock : Measurable (fun p : DLoc × ℝ =>
      F (supRunning p.1 p.2.toNNReal) * G (supReflected p.1 p.2.toNNReal)) :=
    (hF.comp measurable_supRunning_expTime).mul (hG.comp measurable_supReflected_expTime)
  rw [lintegral_expClockLaw θ hq hClock]
  have hrev : (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (q * Real.exp (-q * t)) *
      ∫⁻ f, F (supRunning f t.toNNReal) * G (supReflected f t.toNNReal)
        ∂(stableLocalLaw θ : Measure DLoc)) =
      ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (q * Real.exp (-q * t)) *
        ∫⁻ f, G (localTime f t.toNNReal) * F ((reflectedFrom 0 f).1 t.toNNReal)
          ∂(stableLocalLaw θ : Measure DLoc) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ)),
      ae_restrict_mem measurableSet_Ici] with t hne ht
    rw [lintegral_sup_drawdown_reverse_local hθ
      (Real.toNNReal_pos.mpr (lt_of_le_of_ne ht hne.symm)) hF hG]
  rw [hrev]
  have hd : Measurable (fun p : ℝ × DLoc =>
      ENNReal.ofReal (q * Real.exp (-q * p.1))) := by fun_prop
  have hi : Measurable (fun p : ℝ × DLoc =>
      G (localTime p.2 p.1.toNNReal) * F ((reflectedFrom 0 p.2).1 p.1.toNNReal)) :=
    measurable_infimum_test_real hG hF
  have hm : Measurable (fun p : ℝ × DLoc => ENNReal.ofReal (q * Real.exp (-q * p.1)) *
      (G (localTime p.2 p.1.toNNReal) * F ((reflectedFrom 0 p.2).1 p.1.toNNReal))) :=
    hd.mul hi
  have hinner (t : ℝ) :
      ENNReal.ofReal (q * Real.exp (-q * t)) *
        (∫⁻ f, G (localTime f t.toNNReal) * F ((reflectedFrom 0 f).1 t.toNNReal)
          ∂(stableLocalLaw θ : Measure DLoc)) =
      ∫⁻ f, ENNReal.ofReal (q * Real.exp (-q * t)) *
        (G (localTime f t.toNNReal) * F ((reflectedFrom 0 f).1 t.toNNReal))
          ∂(stableLocalLaw θ : Measure DLoc) := by
    exact (lintegral_const_mul _ (hi.comp measurable_prodMk_left)).symm
  simp_rw [hinner]
  rw [lintegral_lintegral_swap hm.aemeasurable]
  simpa only [mul_assoc] using lintegral_infimum_resolvent_factorization hθ hq hG hF

end BGW.StableTrees
