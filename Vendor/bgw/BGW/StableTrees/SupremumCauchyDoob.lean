/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCauchyMaximal

/-!
# Real compact Doob estimates for occupation differences

The extended compact maximal inequality is converted to an integrable real supremum.

## References

* [J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV]
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- Real compact Doob inequality, with square integrability of the supremum. -/
theorem integral_sq_sup_Iic_le_four_mul {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hrc : ∀ ω t, ContinuousWithinAt (fun s => M s ω) (Ici t) t)
    (T : ℝ≥0) (h2 : Integrable (fun ω => M T ω ^ 2) μ) :
    Integrable (fun ω => (⨆ t : Set.Iic T, |M t ω|) ^ 2) μ ∧
      ∫ ω, (⨆ t : Set.Iic T, |M t ω|) ^ 2 ∂μ ≤ 4 * ∫ ω, M T ω ^ 2 ∂μ := by
  let S := fun ω => ⨆ t ∈ Icc (0 : ℝ≥0) T, ‖M t ω‖ₑ
  let A := fun ω => ⨆ t : Set.Iic T, |M t ω|
  have hS : Measurable S := measurable_sup_Icc_enorm
    (fun t => (hM.stronglyMeasurable t).measurable.mono (ℱ.le t) le_rfl) hrc T
  have he (ω : Ω) : S ω = ⨆ t : Set.Iic T, ‖M t ω‖ₑ := by
    simp only [S, mem_Icc, zero_le, true_and, iSup_subtype, mem_Iic]
  have hA (ω : Ω) : A ω = (S ω).toReal := by
    rw [he, ENNReal.toReal_iSup (fun _ => enorm_ne_top)]
    simp only [toReal_enorm, Real.norm_eq_abs, A]
  have hAm : Measurable A := by
    have heq : A = fun ω => (S ω).toReal := funext hA
    rw [heq]
    exact hS.ennreal_toReal
  have hbound := lintegral_sq_sup_Icc_le_four_mul_of_martingale hM hrc T
  have hfin : (∫⁻ ω, ‖M T ω‖ₑ ^ 2 ∂μ) < ∞ := by
    have hf := h2.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at hf
    simpa only [enorm_pow] using hf
  have hfinite : 4 * (∫⁻ ω, ‖M T ω‖ₑ ^ 2 ∂μ) < ∞ :=
    ENNReal.mul_lt_top (by norm_num) hfin
  have hle : (∫⁻ ω, ENNReal.ofReal (A ω ^ 2) ∂μ) ≤
      4 * ∫⁻ ω, ‖M T ω‖ₑ ^ 2 ∂μ := by
    apply le_trans (lintegral_mono (fun ω => ?_)) hbound
    change ENNReal.ofReal (A ω ^ 2) ≤ S ω ^ 2
    rw [hA, ← ENNReal.toReal_pow]
    exact ENNReal.ofReal_toReal_le
  have hi : Integrable (fun ω => A ω ^ 2) μ :=
    ⟨hAm.aestronglyMeasurable.pow 2,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun ω => sq_nonneg (A ω)))).2
        (hle.trans_lt hfinite)⟩
  refine ⟨hi, ?_⟩
  have hr := ENNReal.toReal_mono hfinite.ne hle
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun ω => sq_nonneg (A ω)))
    hi.aestronglyMeasurable] at hr
  have hterminal : ∫ ω, M T ω ^ 2 ∂μ = (∫⁻ ω, ‖M T ω‖ₑ ^ 2 ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun ω => sq_nonneg _))
      h2.aestronglyMeasurable]
    congr 1
    apply lintegral_congr
    intro ω
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2, Real.norm_eq_abs, sq_abs]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ← hterminal] using hr

set_option maxHeartbeats 400000 in
-- The concrete reflected process requires unfolding nested measurable compositions.
/-- **Doob `L²` on compacts**: a uniform resolvent difference bound controls the maximum. -/
theorem integral_sq_sup_occupationDiffMartingale_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) {D : ℝ}
    (hD : ∀ y : ℝ, |supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y| ≤ D)
    (T : ℝ≥0) :
    Integrable (fun f => (⨆ t : Set.Iic T, |occupationDiffMartingale θ ε η t f|) ^ 2)
        (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (⨆ t : Set.Iic T, |occupationDiffMartingale θ ε η t f|) ^ 2
        ∂(stableLocalLaw θ : Measure DLoc) ≤ 16 * D := by
  let B := discountedOccupation (fun s f => supReflectedFrom 0 f s)
    (fun r => supOccKernel ε r - supOccKernel η r)
  have hk : Measurable (fun r => supOccKernel ε r - supOccKernel η r) :=
    (measurable_supOccKernel ε).sub (measurable_supOccKernel η)
  have hb (r : ℝ) : |supOccKernel ε r - supOccKernel η r| ≤ ε⁻¹ + η⁻¹ := by
    apply (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_of_nonneg (supOccKernel_mem_Icc hε r).1]
      exact (supOccKernel_mem_Icc hε r).2
    · rw [abs_of_nonneg (supOccKernel_mem_Icc hη r).1]
      exact (supOccKernel_mem_Icc hη r).2
  have hZ : Measurable (fun p : ℝ≥0 × DLoc => supReflectedFrom 0 p.2 p.1) :=
    measurable_supReflectedFrom_uncurry.comp
      (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))
  have hB2 : Integrable (fun f => B f ^ 2) (stableLocalLaw θ : Measure DLoc) :=
    integrable_sq_discountedOccupation_of_bounded hZ hk hb
  have hm := martingale_occupationDiffMartingale hθ hε hη
  have he := occupationDiffMartingale_eq_condExp hθ hε hη T
  have hBm : Measurable B := by
    have hF : Measurable (fun p : ℝ × DLoc => Real.exp (-p.1) *
        (supOccKernel ε (supReflectedFrom 0 p.2 p.1.toNNReal) -
          supOccKernel η (supReflectedFrom 0 p.2 p.1.toNNReal))) :=
      (Real.continuous_exp.measurable.comp measurable_fst.neg).mul
        (hk.comp (hZ.comp (measurable_real_toNNReal.prodMap measurable_id)))
    exact hF.stronglyMeasurable.integral_prod_left'.measurable
  have hmem : MemLp B 2 (stableLocalLaw θ : Measure DLoc) :=
    (memLp_two_iff_integrable_sq hBm.aestronglyMeasurable).2 hB2
  have hJ2 : Integrable (fun f => occupationDiffMartingale θ ε η T f ^ 2)
      (stableLocalLaw θ : Measure DLoc) :=
    ((MemLp.condExp (m := DLoc.filtration T) (by norm_num) hmem).integrable_sq).congr
      (he.mono fun f hf => congrArg (fun x : ℝ => x ^ 2) hf)
  have hjensen := integral_norm_condExp_rpow_le (m := DLoc.filtration T)
    (by norm_num : (1 : ℝ) ≤ 2) (f := B) (by simpa using hB2)
  have hJT : (∫ f, occupationDiffMartingale θ ε η T f ^ 2
      ∂(stableLocalLaw θ : Measure DLoc)) ≤ 4 * D := by
    have he2 := integral_congr_ae (he.mono fun f hf => congrArg (fun x : ℝ => x ^ 2) hf)
    simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs] at hjensen
    rw [he2] at hjensen
    exact hjensen.trans (integral_sq_discountedOccupation_supOccupation_sub_le hθ 0 hε hη hD)
  obtain ⟨hi, hle⟩ := integral_sq_sup_Iic_le_four_mul hm
    (rightContinuous_occupationDiffMartingale hθ hε hη) T hJ2
  exact ⟨hi, hle.trans (by linarith)⟩

end BGW.StableTrees
