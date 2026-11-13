/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightPassageSlope
import Mathlib.Algebra.Order.Archimedean.Basic

public import BGW.Skorokhod.PathRegularity

/-!
# Interpolation of vanishing left slopes

A monotone nonnegative numerator with a vanishing dyadic quotient has a vanishing quotient
along the full positive filter. The numerator, rather than its quotient, is monotone.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- At a fixed positive level the finite right passage process has a zero full left slope. -/
theorem ae_tendsto_passageTime_leftSlope {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (x : ℝ≥0) (hx : 0 < x) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure BGW.Skorokhod.DLoc),
      Tendsto (fun ε : ℝ =>
        ((passageTime x f : ℝ) - (passageTime (x - ε.toNNReal) f : ℝ)) / ε)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [ae_tendsto_passageTime_left_dyadic hθ x hx,
    ae_isCadlag_monotone_passage hθ] with f hseq hf
  let U (ε : ℝ) : ℝ := (passageTime x f : ℝ) - (passageTime (x - ε.toNNReal) f : ℝ)
  have hmono : MonotoneOn U (Ioi 0) := by
    intro ε _ η _ hεη
    exact sub_le_sub_left (show (passageTime (x - η.toNNReal) f : ℝ) ≤
      passageTime (x - ε.toNNReal) f from hf.2.1
        (tsub_le_tsub_left (Real.toNNReal_mono hεη) x)) _
  have hnon (ε : ℝ) (_hε : 0 < ε) : 0 ≤ U ε :=
    sub_nonneg.mpr (show (passageTime (x - ε.toNNReal) f : ℝ) ≤ passageTime x f from
      hf.2.1 tsub_le_self)
  apply tendsto_div_zero_of_dyadic hmono hnon (show (0 : ℝ) < x from hx)
  have heq (n : ℕ) : (x : ℝ) * (1 / 2 : ℝ) ^ n =
      ((x / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by simp [div_eq_mul_inv, inv_pow]
  have hfun : (fun n : ℕ => U ((x : ℝ) * (1 / 2 : ℝ) ^ n) /
      ((x : ℝ) * (1 / 2 : ℝ) ^ n)) =
      (fun n : ℕ => ((passageTime x f : ℝ) -
        (passageTime (x - x / (2 : ℝ≥0) ^ n) f : ℝ)) /
          ((x / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) := by
    funext n
    dsimp only [U]
    rw [heq, Real.toNNReal_coe]
  rwa [hfun]

end BGW.StableTrees
