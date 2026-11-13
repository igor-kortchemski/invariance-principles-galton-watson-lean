/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Consequences of quantitative tail bounds

Geometric tail bounds give almost sure convergence, while exponential tail bounds give finite
real moments with explicit Gamma-function estimates.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical

namespace BGW.Probability

/-- Nonnegative sequences with geometric upper tails converge to zero almost surely. -/
theorem ae_tendsto_zero_of_geometric_tails {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℝ) (hD : ∀ᵐ ω ∂μ, ∀ n, 0 ≤ D n ω)
    (htail : ∀ δ : ℝ, 0 < δ → ∃ C r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ n, μ {ω | δ < D n ω} ≤ ENNReal.ofReal (C * r ^ n)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => D n ω) atTop (𝓝 0) := by
  have hevent (m : ℕ) : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, D n ω ≤ 1 / ((m : ℝ) + 1) := by
    obtain ⟨C, r, hr0, hr1, hb⟩ := htail (1 / ((m : ℝ) + 1)) (by positivity)
    have hs : Summable (fun n : ℕ => C * r ^ n) :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left C
    have hsum : (∑' n, μ {ω | 1 / ((m : ℝ) + 1) < D n ω}) ≠ ⊤ :=
      ne_top_of_le_ne_top hs.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hb)
    exact (ae_eventually_notMem hsum).mono fun ω hω =>
      hω.mono fun n hn => not_lt.mp hn
  filter_upwards [hD, ae_all_iff.mpr hevent] with ω hω hbound
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (hω n)
  · intro b hb
    obtain ⟨m, hm⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (gt_mem_nhds hb)).exists
    exact (hbound m).mono fun n hn => hn.trans_lt hm

/-- Exponential upper tails give finite real moments, with an explicit Gamma bound. -/
theorem integrable_rpow_of_exp_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω → ℝ) (hF : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω)
    {D p : ℝ} (hD : 0 ≤ D) (hp : 0 < p)
    (htail : ∀ v : ℝ, 0 ≤ v → μ {ω | v < F ω} ≤ ENNReal.ofReal (D * Real.exp (-v))) :
    Integrable (fun ω => F ω ^ p) μ ∧
      ∫ ω, F ω ^ p ∂μ ≤ D * p * Real.Gamma p := by
  have hpow : Measurable (fun ω => F ω ^ p) := hF.pow_const p
  have hpow0 : ∀ ω, 0 ≤ F ω ^ p := fun ω => Real.rpow_nonneg (hF0 ω) p
  have hbound : (∫⁻ ω, ENNReal.ofReal (F ω ^ p) ∂μ) ≤
      ENNReal.ofReal (D * p * Real.Gamma p) := by
    rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ (ae_of_all _ hF0) hF.aemeasurable hp]
    calc
      _ ≤ ENNReal.ofReal p * ∫⁻ v in Ioi (0 : ℝ),
          ENNReal.ofReal (D * Real.exp (-v)) * ENNReal.ofReal (v ^ (p - 1)) := by
        apply mul_le_mul_right
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        gcongr
        exact htail v hv.le
      _ = ENNReal.ofReal (D * p * Real.Gamma p) := by
        simp_rw [ENNReal.ofReal_mul hD, mul_assoc]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have he : (∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-v)) *
            ENNReal.ofReal (v ^ (p - 1))) = ENNReal.ofReal (Real.Gamma p) := by
          simp_rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
          rw [← ofReal_integral_eq_lintegral_ofReal (Real.GammaIntegral_convergent hp)
            (by
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
              exact mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hv.le _))]
          rw [← Real.Gamma_eq_integral hp]
        rw [he, ← ENNReal.ofReal_mul hD, ← ENNReal.ofReal_mul hp.le]
        congr 1
        ring
  have hi : Integrable (fun ω => F ω ^ p) μ :=
    ⟨hpow.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hpow0)).mpr
      (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hpow0)] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound

end BGW.Probability
