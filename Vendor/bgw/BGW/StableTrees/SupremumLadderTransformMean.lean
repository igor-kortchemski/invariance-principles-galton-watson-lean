/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderTransformApproximation

/-!
# Mean convergence of weighted boundary potentials

Compact square-mean occupation errors and the half-rate potential bound control the
weighted cumulative error before identifying the exact mean potential.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The boundary potential has a finite cumulative representative bounded by the
half-rate auxiliary potential.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem ae_supBoundaryPotential_cumulative {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam : ℝ} (hq : 0 < q) (hlam : 0 ≤ lam) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      let J := ∫ s in Ioi (0 : ℝ), supAuxLocalTime θ f s.toNNReal
        ∂(supWeightStieltjes q lam hq.le hlam f).measure
      supBoundaryPotential θ q lam f = ENNReal.ofReal J ∧
        (supBoundaryPotential θ q lam f).toReal = J ∧
        J ≤ supAuxDiscountedTail θ (q / 2) 0 f := by
  filter_upwards [ae_supLocalTime_eq_aux hθ, ae_supAuxLocalTime_continuous hθ,
    ae_eval_zero_stableLocalLaw hθ, ae_integrable_aux_clock_exp hθ (half_pos hq)]
      with f he hm hf hi
  dsimp only
  have hJ := integrable_clock_and_integral_tail_le ⟨hm.2.1, hm.2.2⟩ hm.1
    (supWeightStieltjes q lam hq.le hlam f).measure hq
    (fun t ht => supWeightStieltjes_measure_Ioi_le hq hlam hf ht) hi
  have hn (s : ℝ) : 0 ≤ supAuxLocalTime θ f s.toNNReal := by
    simpa only [hm.1] using hm.2.1 (zero_le : 0 ≤ s.toNNReal)
  have hrep : supBoundaryPotential θ q lam f = ENNReal.ofReal
      (∫ s in Ioi (0 : ℝ), supAuxLocalTime θ f s.toNNReal
        ∂(supWeightStieltjes q lam hq.le hlam f).measure) := by
    unfold supBoundaryPotential
    rw [supLocalTimeStieltjes_eq_aux he]
    change (∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-q * t - lam * supRunning f t.toNNReal))
        ∂(pathStieltjes (supAuxLocalTime θ f)).measure) = _
    rw [pathStieltjes_lintegral_supWeight hq hlam hf ⟨hm.2.1, hm.2.2⟩ hm.1]
    exact (ofReal_integral_eq_lintegral_ofReal hJ.1 (ae_of_all _ hn)).symm
  refine ⟨hrep, ?_, ?_⟩
  · rw [hrep, ENNReal.toReal_ofReal (integral_nonneg hn)]
  · simpa only [supAuxDiscountedTail, supAuxStieltjes,
      NNReal.coe_zero, mul_zero, Real.exp_zero, one_mul] using hJ.2 0

/-- The real boundary potential is integrable at positive time rate.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem integrable_supBoundaryPotential_toReal {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam : ℝ} (hq : 0 < q) (hlam : 0 ≤ lam) :
    Integrable (fun f => (supBoundaryPotential θ q lam f).toReal)
      (stableLocalLaw θ : Measure DLoc) := by
  apply (integrable_supAuxDiscountedTail hθ (half_pos hq) 0).mono'
    (aemeasurable_supBoundaryPotential hθ hq.le hlam).ennreal_toReal.aestronglyMeasurable
  filter_upwards [ae_supBoundaryPotential_cumulative hθ hq hlam] with f hf
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg, hf.2.1]
  exact hf.2.2

end BGW.StableTrees
