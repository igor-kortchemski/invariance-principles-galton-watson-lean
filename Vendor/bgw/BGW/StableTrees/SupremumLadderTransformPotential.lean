/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderTransformBasic

/-!
# The time marginal of the boundary potential

The public Stieltjes clock inherits the normalized mean potential of the auxiliary clock.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Zero-order case `λ = 0`: `E ∫_0^∞ e^{-qt} dM_t = Φ/q = q^{1/θ - 1}` (`= 1` at `q = 1`). -/
theorem lintegral_supBoundaryPotential_zero_right {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) :
    ∫⁻ f, supBoundaryPotential θ q 0 f ∂(stableLocalLaw θ : Measure DLoc) =
      ENNReal.ofReal (q ^ (1 / θ) / q) := by
  have he : (fun f => supBoundaryPotential θ q 0 f) =ᵐ[
      (stableLocalLaw θ : Measure DLoc)]
        fun f => ENNReal.ofReal (supAuxDiscountedTail θ q 0 f) := by
    filter_upwards [ae_supLocalTime_eq_aux hθ, ae_supAuxLocalTime_continuous hθ,
      (integrable_exp_supAuxIncrement_prod hθ hq 0).prod_left_ae] with f hf hm hi
    have hinner := (pathStieltjes_integral_exp ⟨hm.2.1, hm.2.2⟩ hq 0 hi).1
    simp only [supBoundaryPotential, zero_mul, sub_zero, supLocalTimeStieltjes_eq_aux hf]
    exact (ofReal_integral_eq_lintegral_ofReal hinner
      (ae_of_all _ fun t => (Real.exp_pos _).le)).symm
  rw [lintegral_congr_ae he, ← ofReal_integral_eq_lintegral_ofReal
    (integrable_supAuxDiscountedTail hθ hq 0)
    (ae_of_all _ fun f => integral_nonneg fun t => (Real.exp_pos _).le),
    integral_supAuxDiscountedTail_zero hθ hq, supPotential_zero hθ hq]

end BGW.StableTrees
