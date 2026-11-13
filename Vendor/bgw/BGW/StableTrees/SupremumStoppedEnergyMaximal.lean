/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumStoppedEnergyBounded
public import BGW.StableTrees.SupremumStoppedEnergyDoob

/-!
# Maximal bounded stopped energy

Doob's inequality is applied with the almost sure right-continuity event of the error.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Doob `L²` maximal inequality for the stopped `D`**:
`E sup_{s ≤ t}|D_{s∧τ_n}|² ≤ 4 E D_{t∧τ_n}² ≤ 4 (4 z V + 12 V²)`. -/
theorem integral_sq_sup_errorMartingale_stopped_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ}
    (hε : 0 < ε) (z : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    Integrable (fun f => (⨆ s : Set.Iic t,
          |errorMartingale θ ε (errStopTime n (supHitting θ z) s f) f|) ^ 2)
        (stableLocalLaw θ : Measure DLoc) ∧
      ∫ f, (⨆ s : Set.Iic t, |errorMartingale θ ε (errStopTime n (supHitting θ z) s f) f|) ^ 2
          ∂(stableLocalLaw θ : Measure DLoc) ≤
        4 * (4 * (z : ℝ) * supCorrectionBound θ ε + 12 * supCorrectionBound θ ε ^ 2) := by
  have hσ := isStoppingTime_supHitting θ z
  have he := integral_sq_errorMartingale_stopped_le hθ hε z n t
  have hrc : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s : ℝ≥0,
      ContinuousWithinAt
        (fun u => errorMartingale θ ε (errStopTime n (supHitting θ z) u f) f) (Ici s) s := by
    filter_upwards [ae_rightContinuous_errorMartingale hθ hε] with f hf
    intro s
    exact ContinuousWithinAt.comp
      (f := fun u : ℝ≥0 => errStopTime n (supHitting θ z) u f)
      (g := fun u : ℝ≥0 => errorMartingale θ ε u f) (s := Ici s)
      (hf (errStopTime n (supHitting θ z) s f))
      (continuous_errStopTime n (supHitting θ z) f).continuousWithinAt
      (fun u hu => monotone_errStopTime n (supHitting θ z) f hu)
  obtain ⟨hi, hb⟩ := integral_sq_sup_Iic_le_four_mul_of_ae_rightContinuous
    (martingale_errorMartingale_stopped hθ hε n hσ) hrc t he.1
  exact ⟨hi, hb.trans (mul_le_mul_of_nonneg_left he.2 (by norm_num))⟩

end BGW.StableTrees
