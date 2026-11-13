/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderTransformBasic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Elementary properties of the ladder Laplace functional

Measurability, bounds and bounded convergence for the ascending ladder pair.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem measurable_ladder_exp (θ q lam : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => Real.exp
      (-q * (supLadderTime θ p.1 p.2 : ℝ) - lam * supLadderHeight θ p.1 p.2)) := by
  exact ((measurable_const.mul (measurable_supLadder_uncurry θ).1.coe_nnreal_real).sub
    (measurable_const.mul (measurable_supLadder_uncurry θ).2)).exp

private theorem ae_ladder_exp_le_one {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam : ℝ} (hq : 0 ≤ q) (hlam : 0 ≤ lam) (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ‖Real.exp (-q * (supLadderTime θ z f : ℝ) - lam * supLadderHeight θ z f)‖ ≤ 1 := by
  filter_upwards [ae_supLadderPair_path hθ] with f hf
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
  have hA := (hf.1 z).1
  have hB := (hf.1 z).2
  change 0 ≤ (supLadderTime θ z f : ℝ) at hA
  change 0 ≤ supLadderHeight θ z f at hB
  nlinarith [mul_nonneg hq hA, mul_nonneg hlam hB]

private theorem integrable_ladder_exp {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam : ℝ} (hq : 0 ≤ q) (hlam : 0 ≤ lam) (z : ℝ≥0) :
    Integrable (fun f => Real.exp
      (-q * (supLadderTime θ z f : ℝ) - lam * supLadderHeight θ z f))
      (stableLocalLaw θ : Measure DLoc) :=
  Integrable.of_bound ((measurable_ladder_exp θ q lam).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    1 (ae_ladder_exp_le_one hθ hq hlam z)

/-- The ladder Laplace functional equals one at level zero. -/
theorem supLadderLaplace_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q lam : ℝ) :
    supLadderLaplace θ q lam 0 = 1 := by
  unfold supLadderLaplace
  have he : (fun f => Real.exp
      (-q * (supLadderTime θ 0 f : ℝ) - lam * supLadderHeight θ 0 f)) =ᵐ[
        (stableLocalLaw θ : Measure DLoc)] fun _ => (1 : ℝ) := by
    filter_upwards [ae_supLadderPair_zero hθ] with f hf
    have hA := congrArg Prod.fst hf
    have hB := congrArg Prod.snd hf
    change (supLadderTime θ 0 f : ℝ) = 0 at hA
    change supLadderHeight θ 0 f = 0 at hB
    simp only [hA, hB, mul_zero, sub_zero, Real.exp_zero]
  rw [integral_congr_ae he]
  simp

/-- The nonnegative-rate ladder Laplace functional lies between zero and one. -/
theorem supLadderLaplace_mem_Icc {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ} (hq : 0 ≤ q)
    (hlam : 0 ≤ lam) (z : ℝ≥0) : supLadderLaplace θ q lam z ∈ Icc (0 : ℝ) 1 := by
  unfold supLadderLaplace
  refine ⟨integral_nonneg (fun _ => (Real.exp_pos _).le), ?_⟩
  have he := integral_mono_ae (integrable_ladder_exp hθ hq hlam z)
    (integrable_const (1 : ℝ)) (ae_ladder_exp_le_one hθ hq hlam z |>.mono fun f hf => ?_)
  · simpa only [integral_const, probReal_univ, smul_eq_mul, mul_one] using he
  · exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hf)

/-- The ladder Laplace functional is measurable in the level.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem measurable_supLadderLaplace {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q lam : ℝ) :
    Measurable (supLadderLaplace θ q lam) := by
  -- `hθ` is part of the stated interface; measurability holds at every index.
  have _hθ := hθ
  exact (measurable_ladder_exp θ q lam).stronglyMeasurable.integral_prod_right'.measurable

/-- Bounded convergence in `q ↓ 0` at fixed level (`A_z < ∞` a.s.). -/
theorem tendsto_supLadderLaplace_zero_rate {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {lam : ℝ}
    (hlam : 0 ≤ lam) (z : ℝ≥0) :
    Tendsto (fun q : ℝ => supLadderLaplace θ q lam z) (𝓝[>] 0)
      (𝓝 (supLadderLaplace θ 0 lam z)) := by
  have hb : ∀ᶠ q : ℝ in 𝓝[>] 0, ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ‖Real.exp (-q * (supLadderTime θ z f : ℝ) - lam * supLadderHeight θ z f)‖ ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact ae_ladder_exp_le_one hθ hq.le hlam z
  have hl : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      Tendsto (fun q : ℝ => Real.exp
        (-q * (supLadderTime θ z f : ℝ) - lam * supLadderHeight θ z f))
        (𝓝[>] 0) (𝓝 (Real.exp (-0 * (supLadderTime θ z f : ℝ) -
          lam * supLadderHeight θ z f))) := by
    exact ae_of_all _ fun f =>
      (Real.continuous_exp.comp
        ((continuous_neg.mul continuous_const).sub continuous_const)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
    (Eventually.of_forall fun q =>
      ((measurable_ladder_exp θ q lam).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    hb (integrable_const _) hl

/-- Start at the origin: `A_0 = 0 = B_0` almost surely. -/
theorem ae_supLadder_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      supLadderTime θ 0 f = 0 ∧ supLadderHeight θ 0 f = 0 := by
  filter_upwards [ae_supLadderPair_zero hθ] with f hf
  have hA := congrArg Prod.fst hf
  have hB := congrArg Prod.snd hf
  exact ⟨NNReal.coe_eq_zero.mp hA, hB⟩

end BGW.StableTrees
