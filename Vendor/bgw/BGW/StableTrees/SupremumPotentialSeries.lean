/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialBasic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Convergence and differentiation of the stable scale series

Gamma monotonicity gives factorial majorants for every compact interval.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.StableTrees

private theorem summable_gamma_series {a : ℝ} (ha : 1 < a) (b q : ℝ)
    {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ => q ^ n * x ^ (a * n + b) / Real.Gamma (a * n + b + 1)) := by
  let K := max x 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨N, hN⟩ := exists_nat_ge ((1 - b) / (a - 1))
  have hb : 1 - b ≤ (a - 1) * (N : ℝ) := by
    nlinarith [(div_le_iff₀ (by linarith : 0 < a - 1)).1 hN]
  have hs := (Real.summable_pow_div_factorial (|q| * K ^ a)).mul_left (K ^ b)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_left _ _) hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (le_max_right _ _) hn)
  have he : (n : ℝ) + 1 ≤ a * n + b := by nlinarith
  have hg : (n.factorial : ℝ) ≤ Real.Gamma (a * n + b + 1) := by
    rw [← Real.Gamma_nat_eq_factorial]
    apply Real.Gamma_strictMonoOn_Ici.monotoneOn
    · change 2 ≤ (n : ℝ) + 1
      linarith
    · change 2 ≤ a * n + b + 1
      linarith
    · linarith
  have hxp : x ^ (a * n + b) ≤ K ^ (a * n + b) :=
    Real.rpow_le_rpow hx (le_max_left _ _) (by linarith)
  have hg0 : 0 < Real.Gamma (a * n + b + 1) := Real.Gamma_pos_of_pos (by linarith)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
    abs_of_nonneg (Real.rpow_nonneg hx _), abs_of_pos hg0]
  calc
    _ ≤ |q| ^ n * K ^ (a * n + b) / (n.factorial : ℝ) := by
      exact div_le_div₀ (mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg hK.le _))
        (mul_le_mul_of_nonneg_left hxp (pow_nonneg (abs_nonneg _) _))
        (by positivity) hg
    _ = K ^ b * ((|q| * K ^ a) ^ n / (n.factorial : ℝ)) := by
      rw [Real.rpow_add hK, Real.rpow_mul_natCast hK.le, mul_pow]
      ring

/-- Absolute convergence of the stable scale series at nonnegative arguments. -/
theorem summable_stableSeriesTerm {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ => stableSeriesTerm θ q n x) := by
  have he : (fun n : ℕ => stableSeriesTerm θ q n x) =
      (fun n : ℕ => q ^ n * x ^ (θ * n + (θ - 1)) /
        Real.Gamma (θ * n + (θ - 1) + 1)) := by
    funext n
    unfold stableSeriesTerm
    rw [show θ * (n + 1) - 1 = θ * n + (θ - 1) by ring,
      show θ * (n + 1) = θ * n + (θ - 1) + 1 by ring]
  rw [he]
  exact summable_gamma_series hθ.1 (θ - 1) q hx

/-- Absolute convergence of the termwise derivative away from the endpoint. -/
theorem summable_stableSeriesDerivTerm {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) {x : ℝ}
    (hx : 0 < x) : Summable (fun n : ℕ => stableSeriesDerivTerm θ q n x) := by
  have he : (fun n : ℕ => stableSeriesDerivTerm θ q n x) =
      (fun n : ℕ => q ^ n * x ^ (θ * n + (θ - 2)) /
        Real.Gamma (θ * n + (θ - 2) + 1)) := by
    funext n
    unfold stableSeriesDerivTerm
    rw [show θ * (n + 1) - 2 = θ * n + (θ - 2) by ring,
      show θ * (n + 1) - 1 = θ * n + (θ - 2) + 1 by ring]
  rw [he]
  exact summable_gamma_series hθ.1 (θ - 2) q hx.le

end BGW.StableTrees
