/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureLaplace
public import BGW.StableTrees.StablePassageSubordinator

/-! The lifetime Laplace exponent obtained from the driftless passage subordinator.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VIII. -/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem ae_passageTime_one_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), 0 < passageTime 1 f := by
  have hz := passageLaw_Iic_zero hθ (x := 1) (by norm_num)
  rw [passageLaw, Measure.map_apply (measurable_passageTime 1).coe_nnreal_real
    measurableSet_Iic, measure_eq_zero_iff_ae_notMem] at hz
  filter_upwards [hz] with f hf
  exact_mod_cast (lt_of_not_ge hf)

private theorem ae_lintegral_lifetime_window {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (∫⁻ p, (Ioc (0 : ℝ≥0) 1).indicator
        (fun _ => (p.2.lifetime : ℝ≥0∞)) p.1 ∂excursionPointMeasure f) =
      (passageTime 1 f : ℝ≥0∞) := by
  classical
  filter_upwards [ae_passageTime_eq_tsum_lifetime hθ, ae_passageJumpSet_countable hθ,
    ae_passageTime_one_pos hθ] with f hs hc hp
  have hsum : Summable (fun x : {x ∈ passageJumpSet f | x ≤ 1} =>
      (jumpExcursion x f).lifetime) := by
    by_contra hn
    have hz := tsum_eq_zero_of_not_summable hn
    rw [← hs 1] at hz
    exact hp.ne' hz
  rw [excursionPointMeasure, ite_eq_left hc, lintegral_sum_measure]
  simp_rw [lintegral_dirac]
  change (∑' x : passageJumpSet f, (Ioc (0 : ℝ≥0) 1).indicator
    (fun y => ((jumpExcursion y f).lifetime : ℝ≥0∞)) x) = _
  rw [tsum_subtype (passageJumpSet f),
    hs 1, ENNReal.coe_tsum hsum,
    tsum_subtype {x ∈ passageJumpSet f | x ≤ 1}
      (fun x => ((jumpExcursion x f).lifetime : ℝ≥0∞))]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ passageJumpSet f
  · have hx0 : 0 < x := hx.1
    by_cases hx1 : x ≤ 1 <;> simp [hx, hx0, hx1]
  · simp [hx]

private theorem expNeg_ofReal {x : ℝ} (hx : 0 ≤ x) :
    expNeg (ENNReal.ofReal x) = ENNReal.ofReal (Real.exp (-x)) := by
  simp [expNeg, ENNReal.toReal_ofReal hx]

private theorem expNeg_injective : Function.Injective expNeg := by
  intro x y h
  have hzero (z : ℝ≥0∞) (hz : z ≠ ⊤) : expNeg z ≠ 0 := by
    simp only [expNeg, ite_eq_right hz]
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  by_cases hx : x = ⊤
  · by_cases hy : y = ⊤
    · exact hx.trans hy.symm
    · exact False.elim (hzero y hy (h.symm.trans (by simp [hx])))
  by_cases hy : y = ⊤
  · exact False.elim (hzero x hx (h.trans (by simp [hy])))
  have he := congrArg ENNReal.toReal h
  simp only [expNeg, ite_eq_right hx, ite_eq_right hy,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at he
  have hr := neg_injective (Real.exp_injective he)
  rw [← ENNReal.ofReal_toReal hx, ← ENNReal.ofReal_toReal hy, hr]

/-- **Laplace exponent of the lifetime**: `∫ (1 - e^{-q ζ}) dN = q^{1/θ}` for `q ≥ 0`
(integrand in `ℝ≥0∞`; `1 - e^{-qζ} ∈ [0,1]`). -/
theorem lintegral_one_sub_exp_lifetime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 ≤ q) :
    ∫⁻ e, ENNReal.ofReal (1 - Real.exp (-q * (e.lifetime : ℝ))) ∂(excursionMeasure θ) =
      ENNReal.ofReal (q ^ (1 / θ)) := by
  classical
  let P : Measure DLoc := stableLocalLaw θ
  let L : Excursion → ℝ≥0∞ := fun e =>
    ENNReal.ofReal (1 - Real.exp (-q * (e.lifetime : ℝ)))
  let v : ℝ≥0 × Excursion → ℝ≥0∞ := fun p =>
    (Ioc (0 : ℝ≥0) 1).indicator (fun _ => (p.2.lifetime : ℝ≥0∞)) p.1
  let g : ℝ≥0 × Excursion → ℝ≥0∞ := fun p => ENNReal.ofReal q * v p
  have hv : Measurable v := by
    exact Measurable.ite (measurable_fst measurableSet_Ioc)
      (measurable_excursion_lifetime.coe_nnreal_ennreal.comp measurable_snd) measurable_const
  have hg : Measurable g := measurable_const.mul hv
  have hL : Measurable L := by
    exact (measurable_const.sub
      ((measurable_const.mul measurable_excursion_lifetime.coe_nnreal_real).exp)).ennreal_ofReal
  obtain ⟨ξ, hξ, hae⟩ := exists_measurable_modification_excursionPointMeasure hθ
  have hinner : ∀ᵐ f ∂P, (∫⁻ p, g p ∂ξ f) =
      ENNReal.ofReal (q * (passageTime 1 f : ℝ)) := by
    filter_upwards [hae, ae_lintegral_lifetime_window hθ] with f hf hvf
    rw [hf, lintegral_const_mul _ hv, hvf]
    rw [ENNReal.ofReal_mul hq, ENNReal.ofReal_coe_nnreal]
  have hsub : (fun p => 1 - expNeg (g p)) =
      (fun p : ℝ≥0 × Excursion =>
        (Ioc (0 : ℝ≥0) 1).indicator (fun _ => L p.2) p.1) := by
    funext p
    by_cases hp : p.1 ∈ Ioc (0 : ℝ≥0) 1
    · simp only [g, v, indicator_of_mem hp]
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hq,
        expNeg_ofReal (mul_nonneg hq p.2.lifetime.coe_nonneg)]
      simp only [L, neg_mul, ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
    · simp [g, v, hp]
  have hprod : (∫⁻ p, 1 - expNeg (g p) ∂lebNN.prod (excursionMeasure θ)) =
      ∫⁻ e, L e ∂excursionMeasure θ := by
    let := sigmaFinite_excursionMeasure hθ
    rw [hsub]
    have hmeas : Measurable (fun p : ℝ≥0 × Excursion =>
        (Ioc (0 : ℝ≥0) 1).indicator (fun _ => L p.2) p.1) := by
      exact Measurable.ite (measurable_fst measurableSet_Ioc)
        (hL.comp measurable_snd) measurable_const
    rw [lintegral_prod _ hmeas.aemeasurable]
    have hi (s : ℝ≥0) :
        (∫⁻ e, (Ioc (0 : ℝ≥0) 1).indicator (fun _ => L e) s
          ∂excursionMeasure θ) =
        (Ioc (0 : ℝ≥0) 1).indicator (fun _ => ∫⁻ e, L e ∂excursionMeasure θ) s := by
      by_cases hs : s ∈ Ioc (0 : ℝ≥0) 1 <;> simp [hs]
    simp_rw [hi]
    rw [lintegral_indicator_const measurableSet_Ioc, lebNN_Ioc]
    simp
  have hexp :
      (∫⁻ f, expNeg (∫⁻ p, g p ∂ξ f) ∂P) =
        ENNReal.ofReal (Real.exp (-(q ^ (1 / θ)))) := by
    calc
      _ = ∫⁻ f, ENNReal.ofReal (Real.exp (-q * (passageTime 1 f : ℝ))) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hinner] with f hf
        rw [hf, expNeg_ofReal (mul_nonneg hq (passageTime 1 f).coe_nonneg), neg_mul]
      _ = ENNReal.ofReal (∫ f, Real.exp (-q * (passageTime 1 f : ℝ)) ∂P) := by
        symm
        apply ofReal_integral_eq_lintegral_ofReal
        · apply Integrable.of_bound
            ((measurable_const.mul
              (measurable_passageTime 1).coe_nnreal_real).exp.aestronglyMeasurable) 1
          filter_upwards [] with f
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          apply Real.exp_le_one_iff.mpr
          change -q * (passageTime 1 f : ℝ) ≤ 0
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq)
            (passageTime 1 f).coe_nonneg
        · exact Eventually.of_forall fun _ => (Real.exp_pos _).le
      _ = _ := by
        have hi := integral_exp_neg_passageLaw hθ 1 hq
        rw [passageLaw, integral_map (measurable_passageTime 1).coe_nnreal_real.aemeasurable
          (by fun_prop : AEStronglyMeasurable (fun t : ℝ => Real.exp (-q * t))
            ((stableLocalLaw θ : Measure DLoc).map (fun f => (passageTime 1 f : ℝ))))] at hi
        simpa [P] using congrArg ENNReal.ofReal hi
  apply expNeg_injective
  rw [expNeg_ofReal (Real.rpow_nonneg hq _)]
  have hh := excursion_laplaceFunctional hθ hξ hae hg
  rw [hprod] at hh
  exact hh.symm.trans hexp

end BGW.StableTrees
