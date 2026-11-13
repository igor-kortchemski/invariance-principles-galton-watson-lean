/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderTransformLaplace
import Mathlib.Probability.Independence.Integration

/-!
# The ladder Laplace semigroup

Stationary independent increments give multiplicativity of the ladder Laplace functional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Multiplicativity**: `φ(y + z) = φ(y) φ(z)` (restart at `A_y`, independent stationary
increments, `BGW.StableTrees.SupremumLadderRestart`).

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem supLadderLaplace_add {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ} (hq : 0 ≤ q)
    (hlam : 0 ≤ lam) (y z : ℝ≥0) :
    supLadderLaplace θ q lam (y + z) = supLadderLaplace θ q lam y * supLadderLaplace θ q lam z :=
  by
  -- `hq` and `hlam` are part of the stated interface; the restart argument does not use them.
  have _hq := hq
  have _hlam := hlam
  let P : Measure DLoc := stableLocalLaw θ
  let E : ℝ × ℝ → ℝ := fun p => Real.exp (-q * p.1 - lam * p.2)
  have hE : Measurable E := by fun_prop
  let levels : Fin 3 → ℝ≥0 := ![0, y, y + z]
  have hlevels : Monotone levels := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i <;> simp [levels]
  have hi := (iIndepFun_supLadderIncrement hθ 2 levels hlevels).indepFun
    (show (0 : Fin 2) ≠ 1 by decide)
  change IndepFun (supLadderIncrement θ 0 y) (supLadderIncrement θ y (y + z)) P at hi
  have he0 : supLadderIncrement θ 0 y =ᵐ[P] supLadderPair θ y := by
    filter_upwards [ae_supLadderPair_zero hθ] with f hf
    have hA := congrArg Prod.fst hf
    have hB := congrArg Prod.snd hf
    change (supLadderTime θ 0 f : ℝ) = 0 at hA
    change supLadderHeight θ 0 f = 0 at hB
    simp only [supLadderIncrement, hA, hB, sub_zero, supLadderPair]
  have hind : IndepFun (supLadderPair θ y) (supLadderIncrement θ y (y + z)) P :=
    hi.congr he0 Filter.EventuallyEq.rfl
  have hstation : (∫ f, E (supLadderIncrement θ y (y + z) f) ∂P) =
      supLadderLaplace θ q lam z := by
    rw [← integral_map (measurable_supLadderIncrement θ y (y + z)).aemeasurable
      hE.aestronglyMeasurable,
      map_supLadderIncrement hθ (le_add_of_nonneg_right (show 0 ≤ z from zero_le)),
      integral_map (measurable_supLadderPair θ ((y + z) - y)).aemeasurable
        hE.aestronglyMeasurable]
    simp only [add_tsub_cancel_left]
    rfl
  have hadd : (fun f => E (supLadderPair θ (y + z) f)) =ᵐ[P]
      fun f => E (supLadderPair θ y f) * E (supLadderIncrement θ y (y + z) f) := by
    filter_upwards with f
    dsimp only [E, supLadderPair, supLadderIncrement]
    rw [← Real.exp_add]
    congr 1
    ring
  change (∫ f, E (supLadderPair θ (y + z) f) ∂P) = _
  rw [integral_congr_ae hadd,
    hind.integral_fun_comp_mul_comp (measurable_supLadderPair θ y).aemeasurable
      (measurable_supLadderIncrement θ y (y + z)).aemeasurable
      hE.aestronglyMeasurable hE.aestronglyMeasurable, hstation]
  rfl

/-- Right continuity at `0` (right continuity of `(A,B)` and bounded convergence). -/
theorem tendsto_supLadderLaplace_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ} (hq : 0 ≤ q)
    (hlam : 0 ≤ lam) :
    Tendsto (supLadderLaplace θ q lam) (𝓝[>] 0) (𝓝 1) := by
  have hm (z : ℝ≥0) : Measurable (fun f : DLoc => Real.exp
      (-q * (supLadderTime θ z f : ℝ) - lam * supLadderHeight θ z f)) := by
    exact ((measurable_const.mul (measurable_supLadderPair θ z).fst).sub
      (measurable_const.mul (measurable_supLadderPair θ z).snd)).exp
  have hb (z : ℝ≥0) : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ‖Real.exp (-q * (supLadderTime θ z f : ℝ) - lam * supLadderHeight θ z f)‖ ≤ 1 := by
    filter_upwards [ae_supLadderPair_path hθ] with f hf
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    have hA := (hf.1 z).1
    have hB := (hf.1 z).2
    change 0 ≤ (supLadderTime θ z f : ℝ) at hA
    change 0 ≤ supLadderHeight θ z f at hB
    nlinarith [mul_nonneg hq hA, mul_nonneg hlam hB]
  have hl : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      Tendsto (fun z : ℝ≥0 => Real.exp
        (-q * (supLadderTime θ z f : ℝ) - lam * supLadderHeight θ z f))
        (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    filter_upwards [ae_supLadderPair_path hθ, ae_supLadderPair_zero hθ] with f hf h0
    have hp := (hf.2.2.2 0).mono (show Ioi (0 : ℝ≥0) ⊆ Ici 0 from Ioi_subset_Ici_self)
    have he := Real.continuous_exp.continuousAt.comp_continuousWithinAt
      ((hp.fst.const_mul (-q)).sub (hp.snd.const_mul lam))
    have ht : Tendsto (fun z => Real.exp (-q * (supLadderPair θ z f).1 -
        lam * (supLadderPair θ z f).2)) (𝓝[>] 0)
        (𝓝 (Real.exp (-q * (supLadderPair θ 0 f).1 - lam * (supLadderPair θ 0 f).2))) := he
    rw [h0] at ht
    simpa only [supLadderPair, Prod.fst_zero, Prod.snd_zero, mul_zero, sub_zero,
      Real.exp_zero] using ht
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := (stableLocalLaw θ : Measure DLoc)) (fun _ => (1 : ℝ))
    (Eventually.of_forall fun z => (hm z).aestronglyMeasurable)
    (Eventually.of_forall hb) (integrable_const _) hl
  change Tendsto (fun z => ∫ f, Real.exp
    (-q * (supLadderTime θ z f : ℝ) - lam * supLadderHeight θ z f)
      ∂(stableLocalLaw θ : Measure DLoc)) (𝓝[>] 0) (𝓝 1)
  simpa only [integral_const, probReal_univ, smul_eq_mul, mul_one] using ht

end BGW.StableTrees
