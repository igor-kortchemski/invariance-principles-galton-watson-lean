/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightContinuityTail
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

public import BGW.Probability.TailBounds

/-!
# Height increment moments

Normalize increments by their stable height scale and integrate the exponential tail.
Integrability is established before using the Bochner integral.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- **Increment moments** with one constant for all `t` and `s`:
`E|H_{t+s} - H_t|^p ≤ C s^(p (1 - 1/θ))`, the integrand being integrable. -/
theorem height_increment_moment_bound {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t s : ℝ≥0, 0 < s →
      Integrable (fun f : DLoc => |height θ f (t + s) - height θ f t| ^ p)
        (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, |height θ f (t + s) - height θ f t| ^ p ∂(stableLocalLaw θ : Measure DLoc) ≤
        C * (s : ℝ) ^ (p * (1 - 1 / θ)) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  refine ⟨2 * Real.exp 1 * p * Real.Gamma p, by positivity, ?_⟩
  intro t s hs
  let k : ℝ := (s : ℝ) ^ (1 - 1 / θ)
  have hk : 0 < k := Real.rpow_pos_of_pos hs _
  let F (f : DLoc) : ℝ := |height θ f (t + s) - height θ f t| / k
  have hm := measurable_height_fixed θ
  have hF : Measurable F := (continuous_abs.measurable.comp ((hm (t + s)).sub (hm t))).div_const k
  have ht (v : ℝ) (hv : 0 ≤ v) :
      (stableLocalLaw θ : Measure DLoc) {f | v < F f} ≤
        ENNReal.ofReal (2 * Real.exp 1 * Real.exp (-v)) := by
    have he : {f | v < F f} =
        {f : DLoc | v * k < |height θ f (t + s) - height θ f t|} := by
      ext f
      exact lt_div_iff₀ hk
    rw [he]
    have hb := measure_height_increment_gt_le_exp hθ t s hs (v * k) (mul_nonneg hv hk.le)
    have heval : v * k * (s : ℝ) ^ (-(1 - 1 / θ)) = v := by
      rw [mul_assoc, ← Real.rpow_add (show 0 < (s : ℝ) from hs)]
      simp
    simpa only [heval] using hb
  obtain ⟨hi, hb⟩ := integrable_rpow_of_exp_tail (stableLocalLaw θ : Measure DLoc) F hF
    (fun f => div_nonneg (abs_nonneg _) hk.le) (by positivity) hp0 ht
  have he (f : DLoc) : |height θ f (t + s) - height θ f t| ^ p = F f ^ p * k ^ p := by
    dsimp only [F]
    rw [Real.div_rpow (abs_nonneg _) hk.le, div_mul_cancel₀ _ (ne_of_gt
      (Real.rpow_pos_of_pos hk _))]
  have hscale : k ^ p = (s : ℝ) ^ (p * (1 - 1 / θ)) := by
    dsimp only [k]
    exact (Real.rpow_mul s.2 _ _).symm.trans (congrArg (fun r => (s : ℝ) ^ r)
      (mul_comm _ _))
  refine ⟨by simpa only [he] using hi.mul_const (k ^ p), ?_⟩
  simp_rw [he]
  rw [integral_mul_const]
  exact (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hk.le _)).trans_eq
    (by rw [hscale])

end BGW.StableTrees
