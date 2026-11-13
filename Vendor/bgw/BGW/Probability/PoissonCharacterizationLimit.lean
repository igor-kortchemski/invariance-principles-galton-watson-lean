/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! Numerical limits for binomial and finite-mark grid approximations. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators

namespace BGW.Probability

/-- The expected number of occupied cells tends to the exponential rate. -/
lemma tendsto_grid_mean (a : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * (1 - Real.exp (-a / n))) atTop (𝓝 a) := by
  apply (tendsto_add_atTop_iff_nat 1).1
  have hd : HasDerivAt (fun x : ℝ => 1 - Real.exp (-a * x)) a 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul (-a)).exp.const_sub 1) using 1 <;> simp
  have hu : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩
  simpa [Function.comp_def, smul_eq_mul, div_eq_mul_inv] using
    hd.tendsto_slope_zero_right.comp hu

end BGW.Probability
