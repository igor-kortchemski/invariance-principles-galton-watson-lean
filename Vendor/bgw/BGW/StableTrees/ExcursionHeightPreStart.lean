/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightPreStartOccupation
import BGW.StableTrees.SupremumFactorizationCompensation

/-!
# Simultaneous vanishing of occupation at every jump start

The compensated dyadic left-slope event is interpolated pathwise on the common finite-passage
event. The occupation bound then gives full-filter vanishing at every excursion start.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- On finite passages the extended left quotient is the nonnegative real quotient. -/
theorem passagePast_leftSlope_eq_ofReal (f : DLoc)
    (hp : ∀ y : ℝ≥0, passagePast y f = (passageTimeMinus y f : ℝ≥0∞))
    (x ε : ℝ≥0) (hε : 0 < ε) :
    (passagePast x f - passagePast (x - ε) f) / (ε : ℝ≥0∞) =
      ENNReal.ofReal (((passageTimeMinus x f : ℝ) -
        (passageTimeMinus (x - ε) f : ℝ)) / (ε : ℝ)) := by
  rw [hp x, hp (x - ε), ENNReal.ofReal_div_of_pos (show (0 : ℝ) < ε from hε)]
  have he := ENNReal.ofReal_sub (passageTimeMinus x f : ℝ)
    (q := (passageTimeMinus (x - ε) f : ℝ)) (NNReal.coe_nonneg _)
  apply congrArg₂ (fun a b : ℝ≥0∞ => a / b)
  · simpa only [ENNReal.ofReal_coe_nnreal] using he.symm
  · simp only [ENNReal.ofReal_coe_nnreal]

/-- Outside the bad dyadic event, finite monotone left passages have zero full left slope. -/
theorem tendsto_passageTimeMinus_leftSlope_of_not_bad (f : DLoc)
    (hp : ∀ y : ℝ≥0, passagePast y f = (passageTimeMinus y f : ℝ≥0∞))
    (hm : Monotone (fun y => passageTimeMinus y f)) (x : ℝ≥0)
    (hx : (x, f) ∉ excursionHeightLeftSlopeBad) :
    Tendsto (fun ε : ℝ => ((passageTimeMinus x f : ℝ) -
      (passageTimeMinus (x - ε.toNNReal) f : ℝ)) / ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let U (ε : ℝ) : ℝ := (passageTimeMinus x f : ℝ) -
    (passageTimeMinus (x - ε.toNNReal) f : ℝ)
  have hmono : MonotoneOn U (Ioi 0) := by
    intro ε _ η _ hεη
    exact sub_le_sub_left (show (passageTimeMinus (x - η.toNNReal) f : ℝ) ≤
      passageTimeMinus (x - ε.toNNReal) f from hm
        (tsub_le_tsub_left (Real.toNNReal_mono hεη) x)) _
  have hnon (ε : ℝ) (_hε : 0 < ε) : 0 ≤ U ε :=
    sub_nonneg.mpr (show (passageTimeMinus (x - ε.toNNReal) f : ℝ) ≤
      passageTimeMinus x f from hm tsub_le_self)
  apply tendsto_div_zero_of_dyadic hmono hnon (by norm_num : (0 : ℝ) < 1)
  have hraw : Tendsto (fun n : ℕ =>
      (passagePast x f - passagePast (x - 1 / (2 : ℝ≥0) ^ n) f) /
        ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) := not_not.mp hx
  have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hraw
  have heq (n : ℕ) : (1 : ℝ) * (1 / 2 : ℝ) ^ n =
      ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by simp [div_eq_mul_inv, inv_pow]
  convert hreal using 1
  · funext n
    dsimp only [Function.comp_def]
    have hden : (0 : ℝ) < ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by positivity
    have hnn : 0 ≤ ((passageTimeMinus x f : ℝ) -
        (passageTimeMinus (x - 1 / (2 : ℝ≥0) ^ n) f : ℝ)) /
          ((1 / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
      apply div_nonneg _ hden.le
      simpa only [U, Real.toNNReal_coe] using hnon _ hden
    rw [passagePast_leftSlope_eq_ofReal f hp x (1 / (2 : ℝ≥0) ^ n) (by positivity),
      heq, ENNReal.toReal_ofReal hnn]
    simp only [Real.toNNReal_coe, U]
  · simp only [ENNReal.toReal_zero]

/-- **Pre-start vanishing**: almost surely, at every passage jump level `x`, the host
approximation at the excursion start `T(x-)` tends to `0` along the full filter `ε → 0⁺`. -/
theorem ae_tendsto_heightApprox_passageTimeMinus {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      Tendsto (fun ε : ℝ => heightApprox ε f (passageTimeMinus x f)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [ae_no_bad_leftSlope_at_jumps hθ,
    ae_passagePast_eq_passageTimeMinus hθ, ae_passageTimeMinus_order_bounds hθ,
    ae_passageTime_eq_firstPassageBelow hθ, ae_continuousAt_jumpStart hθ]
      with f hbad hp hm hf hs
  intro x hx
  have hfull := tendsto_passageTimeMinus_leftSlope_of_not_bad f hp hm.1 x (hbad x hx)
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ heightApprox ε f (passageTimeMinus x f) ∧
        heightApprox ε f (passageTimeMinus x f) ≤
          ((passageTimeMinus x f : ℝ) - (passageTimeMinus (x - ε.toNNReal) f : ℝ)) / ε := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < x from hx.1)] with ε hε
    exact heightApprox_passageTimeMinus_le f x hf.1 (hs x hx).2.1 hx.2 hm.2.1 hm.2.2
      hε.1 hε.2
  exact squeeze_zero' (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2) hfull

end BGW.StableTrees
