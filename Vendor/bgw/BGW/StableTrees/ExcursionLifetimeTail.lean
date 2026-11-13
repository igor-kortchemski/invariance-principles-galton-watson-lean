/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionLifetimeScaling
public import BGW.StableTrees.ExcursionLifetimeLaplace
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Power-law lifetime tails from scaling and the unit Laplace exponent.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VIII. -/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Scaling determines every positive lifetime tail from its value at one. -/
theorem excursionMeasure_lifetime_tail_scale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (t : ℝ) (ht : 0 < t) :
    excursionMeasure θ {e : Excursion | t < (e.lifetime : ℝ)} =
      ENNReal.ofReal (t ^ (-(1 / θ))) *
        excursionMeasure θ {e : Excursion | 1 < (e.lifetime : ℝ)} := by
  let c : Ioi (0 : ℝ) := ⟨t⁻¹, inv_pos.mpr ht⟩
  have hm := congrArg (fun μ : Measure Excursion =>
    μ {e : Excursion | 1 < (e.lifetime : ℝ)})
    (map_excursionScale_excursionMeasure hθ c)
  rw [Measure.map_apply (measurable_excursionScale θ c)
    (measurableSet_lt measurable_const measurable_excursion_lifetime.coe_nnreal_real),
    Measure.smul_apply, smul_eq_mul] at hm
  have hpre : excursionScale θ c ⁻¹' {e : Excursion | 1 < (e.lifetime : ℝ)} =
      {e : Excursion | t < (e.lifetime : ℝ)} := by
    ext e
    simp only [mem_preimage, mem_ofPred_eq, excursionScale_lifetime]
    change 1 < t⁻¹ * (e.lifetime : ℝ) ↔ t < (e.lifetime : ℝ)
    rw [← div_eq_inv_mul, lt_div_iff₀ ht, one_mul]
  rw [hpre] at hm
  simpa only [c, Real.inv_rpow ht.le, Real.rpow_neg ht.le] using hm

private theorem lifetime_layercake (θ : ℝ) :
    (∫⁻ e, ENNReal.ofReal (1 - Real.exp (-(e.lifetime : ℝ))) ∂excursionMeasure θ) =
      ∫⁻ t in Ioi (0 : ℝ), excursionMeasure θ {e : Excursion | t < (e.lifetime : ℝ)} *
        ENNReal.ofReal (Real.exp (-t)) := by
  have h := lintegral_comp_eq_lintegral_meas_lt_mul (excursionMeasure θ)
    (Eventually.of_forall (fun e : Excursion => e.lifetime.coe_nonneg))
    measurable_excursion_lifetime.coe_nnreal_real.aemeasurable
    (fun t _ => (Real.continuous_exp.comp continuous_neg).intervalIntegrable 0 t)
    (Eventually.of_forall (fun t : ℝ => (Real.exp_pos (-t)).le))
  simp only [Function.comp_def] at h
  convert h using 1
  apply lintegral_congr
  intro e
  congr 1
  rw [intervalIntegral.integral_comp_neg, integral_exp]
  simp

private theorem lintegral_gamma {a : ℝ} (ha : 0 < a) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (a - 1) * Real.exp (-t))) =
      ENNReal.ofReal (Real.Gamma a) := by
  rw [Real.Gamma_eq_integral ha]
  symm
  rw [ofReal_integral_eq_lintegral_ofReal]
  · apply lintegral_congr
    intro t
    rw [mul_comm]
  · exact Real.GammaIntegral_convergent ha
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht.le _)

/-- **Lifetime tail**: `N(ζ > t) = t^{-1/θ} / Γ(1 - 1/θ)` for `t > 0`. -/
theorem excursionMeasure_lifetime_tail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ) (ht : 0 < t) :
    excursionMeasure θ {e : Excursion | t < (e.lifetime : ℝ)} =
      ENNReal.ofReal (t ^ (-(1 / θ)) / Real.Gamma (1 - 1 / θ)) := by
  have hθ0 : 0 < θ := lt_trans zero_lt_one hθ.1
  have ha : 0 < 1 - 1 / θ := sub_pos.mpr ((div_lt_one hθ0).mpr hθ.1)
  have hG : 0 < Real.Gamma (1 - 1 / θ) := Real.Gamma_pos_of_pos ha
  let C := excursionMeasure θ {e : Excursion | 1 < (e.lifetime : ℝ)}
  have hunit : C * ENNReal.ofReal (Real.Gamma (1 - 1 / θ)) = 1 := by
    calc
      _ = ∫⁻ u in Ioi (0 : ℝ), C *
          ENNReal.ofReal (u ^ (-(1 / θ)) * Real.exp (-u)) := by
        rw [lintegral_const_mul _ (by fun_prop),
          show -(1 / θ) = (1 - 1 / θ) - 1 by ring, lintegral_gamma ha]
      _ = ∫⁻ u in Ioi (0 : ℝ),
          excursionMeasure θ {e : Excursion | u < (e.lifetime : ℝ)} *
            ENNReal.ofReal (Real.exp (-u)) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        rw [excursionMeasure_lifetime_tail_scale hθ u hu,
          ENNReal.ofReal_mul (Real.rpow_nonneg hu.le _)]
        ring
      _ = _ := by
        rw [← lifetime_layercake θ]
        simpa using lintegral_one_sub_exp_lifetime hθ (q := 1) (by norm_num)
  have hC : C = (ENNReal.ofReal (Real.Gamma (1 - 1 / θ)))⁻¹ := by
    apply (ENNReal.mul_left_inj (ENNReal.ofReal_ne_zero_iff.mpr hG)
      ENNReal.ofReal_ne_top).mp
    rw [hunit, ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hG)
      ENNReal.ofReal_ne_top]
  rw [excursionMeasure_lifetime_tail_scale hθ t ht]
  change ENNReal.ofReal (t ^ (-(1 / θ))) * C = _
  rw [hC, ← ENNReal.ofReal_inv_of_pos hG, ← ENNReal.ofReal_mul
    (Real.rpow_nonneg ht.le _)]
  simp only [div_eq_mul_inv]

end BGW.StableTrees
