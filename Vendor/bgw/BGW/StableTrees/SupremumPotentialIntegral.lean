/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialRegularity
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Absolute continuity of the stable scale series

Nonnegative derivatives give integrability at zero. The series at `|q|` dominates
signed rates, and the fundamental theorem of calculus identifies the integral.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace BGW.StableTrees

/-- The termwise derivative is Borel, including its specified value at zero. -/
theorem measurable_stableSeriesDeriv {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) :
    Measurable (stableSeriesDeriv θ q) := by
  have he : stableSeriesDeriv θ q = (Ioi 0).indicator (deriv (stableSeries θ q)) := by
    funext x
    by_cases hx : 0 < x
    · rw [indicator_of_mem (s := Ioi (0 : ℝ)) hx, (hasDerivAt_stableSeries hθ q hx).deriv]
    · simp [stableSeriesDeriv, hx]
  rw [he]
  exact (measurable_deriv _).indicator measurableSet_Ioi

/-- The derivative series is nonnegative at nonnegative rates. -/
theorem stableSeriesDeriv_nonneg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 ≤ q)
    (x : ℝ) : 0 ≤ stableSeriesDeriv θ q x := by
  unfold stableSeriesDeriv
  split_ifs with hx
  · apply tsum_nonneg
    intro n
    have hn : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have he : 0 < θ * (n + 1) - 1 := by nlinarith [hθ.1]
    exact div_nonneg (mul_nonneg (pow_nonneg hq _) (Real.rpow_nonneg hx.le _))
      (Real.Gamma_pos_of_pos he).le
  · exact le_rfl

/-- Absolute derivative bounds for signed rates follow from the positive-rate series. -/
theorem norm_stableSeriesDeriv_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q x : ℝ) :
    ‖stableSeriesDeriv θ q x‖ ≤ stableSeriesDeriv θ |q| x := by
  by_cases hx : 0 < x
  · have he : (fun n : ℕ => ‖stableSeriesDerivTerm θ q n x‖) =
        (fun n : ℕ => stableSeriesDerivTerm θ |q| n x) := by
      funext n
      have hn : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hg : 0 < Real.Gamma (θ * (n + 1) - 1) :=
        Real.Gamma_pos_of_pos (by nlinarith [hθ.1])
      simp only [stableSeriesDerivTerm, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
        abs_of_nonneg (Real.rpow_nonneg hx.le _), abs_of_pos hg]
    simp only [stableSeriesDeriv, ite_eq_left hx]
    have hb := norm_tsum_le_tsum_norm (summable_stableSeriesDerivTerm hθ q hx).norm
    rwa [he] at hb
  · simp [stableSeriesDeriv, hx]

/-- Local integrability of `W_q'` at `0` (integrable singularity `x^{θ-2}` for `θ < 2`). -/
theorem integrableOn_stableSeriesDeriv {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) (K : ℝ) :
    IntegrableOn (stableSeriesDeriv θ q) (Ioc 0 K) := by
  have hi : IntegrableOn (stableSeriesDeriv θ |q|) (Ioc 0 K) := by
    apply intervalIntegral.integrableOn_deriv_of_nonneg
      ((continuousOn_stableSeries hθ |q|).mono (fun _ hx => hx.1))
      (fun x hx => hasDerivAt_stableSeries hθ |q| hx.1)
    intro x _
    exact stableSeriesDeriv_nonneg hθ (abs_nonneg q) x
  exact hi.mono' (measurable_stableSeriesDeriv hθ q).aestronglyMeasurable
    (ae_of_all _ (fun x => norm_stableSeriesDeriv_le hθ q x))

/-- `W_q(x) = ∫_0^x W_q'` (absolute continuity at the singular endpoint `0`). -/
theorem integral_stableSeriesDeriv {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ∫ y in Ioc 0 x, stableSeriesDeriv θ q y = stableSeries θ q x := by
  have hi : IntervalIntegrable (stableSeriesDeriv θ q) volume 0 x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
    exact integrableOn_stableSeriesDeriv hθ q x
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx
    ((continuousOn_stableSeries hθ q).mono (fun _ hy => hy.1))
    (fun y hy => hasDerivAt_stableSeries hθ q hy.1) hi
  simpa only [intervalIntegral.integral_of_le hx, stableSeries_zero hθ q, sub_zero] using he

end BGW.StableTrees
