/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Nonnegative limits with uniform real-integral bounds

The explicit integrability conclusion prevents default-zero real integrals from
standing in for moment bounds when the localization is removed.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace BGW.StableTrees

/-- Fatou transfers a uniform integral bound to a nonnegative almost sure limit,
including integrability of that limit. -/
theorem integrable_limit_of_nonneg_integral_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F : ℕ → Ω → ℝ} {f : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hi : ∀ n, Integrable (F n) μ) (hn : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ F n ω)
    (hl : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (f ω)))
    (hb : ∀ n, ∫ ω, F n ω ∂μ ≤ K) :
    Integrable f μ ∧ ∫ ω, f ω ∂μ ≤ K := by
  have hm := aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hi n).aestronglyMeasurable) hl
  have hnonneg : ∀ᵐ ω ∂μ, 0 ≤ f ω := by
    filter_upwards [hl, ae_all_iff.mpr hn] with ω hω hpos
    exact ge_of_tendsto hω (Eventually.of_forall hpos)
  have hfatou := lintegral_liminf_le' (μ := μ) (u := atTop)
    (fun n => (hi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have he : (fun ω => liminf (fun n => ENNReal.ofReal (F n ω)) atTop) =ᵐ[μ]
      (fun ω => ENNReal.ofReal (f ω)) := by
    filter_upwards [hl] with ω hω
    exact (ENNReal.tendsto_ofReal hω).liminf_eq
  rw [lintegral_congr_ae he] at hfatou
  have hbound : (∫⁻ ω, ENNReal.ofReal (f ω) ∂μ) ≤ ENNReal.ofReal K := by
    apply hfatou.trans
    apply (liminf_le_limsup : _ ≤ _).trans
    refine limsup_le_of_le (h := ?_)
    exact Eventually.of_forall fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (hn n)]
      exact ENNReal.ofReal_le_ofReal (hb n)
  have hfi : Integrable f μ := ⟨hm,
    (hasFiniteIntegral_iff_ofReal hnonneg).mpr
      (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hfi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hnonneg] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff hK).mp hbound

end BGW.StableTrees
