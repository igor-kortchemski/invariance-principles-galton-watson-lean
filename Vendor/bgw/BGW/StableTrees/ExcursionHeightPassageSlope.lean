/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightPassageTail
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Normed

public import BGW.Probability.TailBounds

/-!
# Almost sure decay from geometric tail bounds

Summable geometric tails give almost sure convergence to zero of nonnegative difference
quotients. The criterion retains countably many thresholds on a single full-measure event.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Probability

namespace BGW.StableTrees

/-- At each deterministic positive level the left dyadic passage increments have zero slope. -/
theorem ae_tendsto_passageTime_left_dyadic {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (x : ℝ≥0) (hx : 0 < x) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure BGW.Skorokhod.DLoc),
      Tendsto (fun n : ℕ =>
        ((passageTime x f : ℝ) - (passageTime (x - x / (2 : ℝ≥0) ^ n) f : ℝ)) /
          ((x / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
  let ε (n : ℕ) : ℝ≥0 := x / (2 : ℝ≥0) ^ n
  let D (n : ℕ) (f : BGW.Skorokhod.DLoc) : ℝ :=
    ((passageTime x f : ℝ) - (passageTime (x - ε n) f : ℝ)) / (ε n : ℝ)
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεle (n : ℕ) : ε n ≤ x := by
    exact div_le_self zero_le (one_le_pow₀ (by norm_num : (1 : ℝ≥0) ≤ 2))
  have hnon : ∀ᵐ f ∂(stableLocalLaw θ : Measure BGW.Skorokhod.DLoc), ∀ n, 0 ≤ D n f := by
    filter_upwards [ae_isCadlag_monotone_passage hθ] with f hf
    intro n
    exact div_nonneg (sub_nonneg.mpr (show (passageTime (x - ε n) f : ℝ) ≤
      passageTime x f from hf.2.1 tsub_le_self)) (hεpos n).le
  apply ae_tendsto_zero_of_geometric_tails _ D hnon
  intro δ hδ
  let β : ℝ := 1 - 1 / θ
  have hθpos : 0 < θ := zero_lt_one.trans hθ.1
  have hβ : 0 < β := sub_pos.mpr ((div_lt_one hθpos).mpr hθ.1)
  let r : ℝ := (1 / 2 : ℝ) ^ β
  refine ⟨δ ^ (-1 / θ) * (x : ℝ) ^ β / (1 - Real.exp (-1)), r,
    (Real.rpow_nonneg (by norm_num) _), ?_, ?_⟩
  · exact Real.rpow_lt_one (by norm_num) (by norm_num) hβ
  · intro n
    have heq : {f : BGW.Skorokhod.DLoc | δ < D n f} =
        {f | δ * (ε n : ℝ) <
          (passageTime ((x - ε n) + ε n) f : ℝ) - (passageTime (x - ε n) f : ℝ)} := by
      ext f
      rw [tsub_add_cancel_of_le (hεle n)]
      exact (lt_div_iff₀ (show (0 : ℝ) < ε n from hεpos n))
    rw [heq]
    have hb := measure_passageIncrement_gt_le hθ (x - ε n) (ε n)
      (mul_pos hδ (show (0 : ℝ) < ε n from hεpos n))
    have hcoef : (ε n : ℝ) * (δ * (ε n : ℝ)) ^ (-1 / θ) =
        δ ^ (-1 / θ) * (ε n : ℝ) ^ β := by
      rw [Real.mul_rpow hδ.le (show (0 : ℝ) ≤ ε n from (hεpos n).le)]
      calc
        _ = δ ^ (-1 / θ) * ((ε n : ℝ) ^ (1 : ℝ) * (ε n : ℝ) ^ (-1 / θ)) := by
          rw [Real.rpow_one]
          ring
        _ = _ := by
          rw [← Real.rpow_add (show (0 : ℝ) < ε n from hεpos n)]
          rw [show (1 : ℝ) + -1 / θ = β by dsimp [β]; ring]
    have hεeq : (ε n : ℝ) = (x : ℝ) * (1 / 2 : ℝ) ^ n := by
      simp [ε, div_eq_mul_inv, inv_pow]
    have hpow : (ε n : ℝ) ^ β = (x : ℝ) ^ β * r ^ n := by
      rw [hεeq]
      exact (Real.mul_rpow (z := β) x.2
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n)).trans
          (congrArg (fun z : ℝ => (x : ℝ) ^ β * z)
            (Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2) β n).symm)
    rw [hcoef, hpow] at hb
    convert hb using 1
    congr 1
    ring

end BGW.StableTrees
