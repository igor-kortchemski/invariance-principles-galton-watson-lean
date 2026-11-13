/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderTransformSubstitution
public import BGW.StableTrees.SupremumLadderTransformLaplace

/-!
# Measurability and Tonelli for ladder potentials

Inverse substitution gives measurability of the pathwise boundary integral, without a
measurability assertion about the totalized random Stieltjes measure.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem measurable_ladderExp (θ q lam : ℝ) :
    Measurable (fun p : ℝ × DLoc => Real.exp
      (-q * (supLadderTime θ p.1.toNNReal p.2 : ℝ) -
        lam * supLadderHeight θ p.1.toNNReal p.2)) := by
  have hA := (measurable_supLadder_uncurry θ).1.comp
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hB := (measurable_supLadder_uncurry θ).2.comp
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  exact ((measurable_const.mul hA.coe_nnreal_real).sub (measurable_const.mul hB)).exp

/-- The extended boundary potential is almost everywhere measurable at nonnegative rates.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem aemeasurable_supBoundaryPotential {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam : ℝ} (hq : 0 ≤ q) (hlam : 0 ≤ lam) :
    AEMeasurable (supBoundaryPotential θ q lam) (stableLocalLaw θ : Measure DLoc) := by
  have hm := (measurable_ladderExp θ q lam).ennreal_ofReal.lintegral_prod_left'
    (μ := volume.restrict (Ioi (0 : ℝ)))
  exact hm.aemeasurable.congr
    (ae_lintegral_supLadder_eq_supBoundaryPotential hθ hq hlam)

/-- The ladder exponential is integrable at nonnegative rates.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem integrable_exp_neg_supLadder {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam : ℝ} (hq : 0 ≤ q) (hlam : 0 ≤ lam) (z : ℝ≥0) :
    Integrable (fun f => Real.exp
      (-q * (supLadderTime θ z f : ℝ) - lam * supLadderHeight θ z f))
      (stableLocalLaw θ : Measure DLoc) := by
  have hm := (measurable_ladderExp θ q lam).comp
    ((measurable_const : Measurable (fun _ : DLoc => (z : ℝ))).prodMk measurable_id)
  apply Integrable.of_bound
    (by simpa only [Function.comp_def, id_eq, Real.toNNReal_coe]
      using hm.aestronglyMeasurable) 1
  filter_upwards [ae_supLadderPair_path hθ] with f hf
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
  have hA := (hf.1 z).1
  have hB := (hf.1 z).2
  change 0 ≤ (supLadderTime θ z f : ℝ) at hA
  change 0 ≤ supLadderHeight θ z f at hB
  nlinarith [mul_nonneg hq hA, mul_nonneg hlam hB]

/-- Tonelli: `∫_0^∞ φ(z) dz = E ∫_0^∞ e^{-qA_z - λB_z} dz = E ∫ e^{-qt-λS_t} dM_t`. -/
theorem lintegral_supLadderLaplace_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q lam : ℝ}
    (hq : 0 ≤ q) (hlam : 0 ≤ lam) :
    ∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (supLadderLaplace θ q lam z.toNNReal) =
      ∫⁻ f, supBoundaryPotential θ q lam f ∂(stableLocalLaw θ : Measure DLoc) := by
  calc
    _ = ∫⁻ z in Ioi (0 : ℝ), ∫⁻ f,
        ENNReal.ofReal (Real.exp (-q * (supLadderTime θ z.toNNReal f : ℝ) -
          lam * supLadderHeight θ z.toNNReal f)) ∂(stableLocalLaw θ : Measure DLoc) := by
      apply lintegral_congr
      intro z
      exact ofReal_integral_eq_lintegral_ofReal
        (integrable_exp_neg_supLadder hθ hq hlam z.toNNReal)
        (ae_of_all _ fun f => (Real.exp_pos _).le)
    _ = ∫⁻ f, (∫⁻ z in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-q * (supLadderTime θ z.toNNReal f : ℝ) -
          lam * supLadderHeight θ z.toNNReal f))) ∂(stableLocalLaw θ : Measure DLoc) :=
      lintegral_lintegral_swap (measurable_ladderExp θ q lam).ennreal_ofReal.aemeasurable
    _ = _ := lintegral_congr_ae
      (ae_lintegral_supLadder_eq_supBoundaryPotential hθ hq hlam)

end BGW.StableTrees
