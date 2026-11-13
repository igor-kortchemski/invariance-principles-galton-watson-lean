/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridgesDepthTail
public import BGW.StableTrees.SupremumLocalTimePublic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Independent depth and full ladder bound

Conditioning on the full stable ladder height leaves an independent infimum depth. Its
exponential tail integrates exactly by the ladder-height Laplace transform.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- An independent fresh infimum dominates a full ladder height with an exponential bound. -/
theorem measure_supLadderHeight_le_independent_depth {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (r v : ℝ≥0) {q : ℝ} (hq : 0 ≤ q) :
    ((stableLocalLaw θ : Measure DLoc).prod (stableLocalLaw θ : Measure DLoc))
      {p | supLadderHeight θ v p.1 ≤ -runningInfLoc p.2 r} ≤
      ENNReal.ofReal (Real.exp (q * r - (v : ℝ) * (q ^ (1 / θ)) ^ (θ - 1))) := by
  let P : Measure DLoc := stableLocalLaw θ
  let lam := q ^ (1 / θ)
  have hlam : 0 ≤ lam := Real.rpow_nonneg hq _
  have hB : Measurable (supLadderHeight θ v) :=
    Measurable.comp (g := fun p : ℝ≥0 × DLoc => supLadderHeight θ p.1 p.2)
      (f := fun f : DLoc => (v, f)) (measurable_supLadder_uncurry θ).2
      (measurable_const.prodMk measurable_id)
  have hI : Measurable (fun g : DLoc => -runningInfLoc g r) :=
    (measurable_runningInfLoc_uncurry.comp (measurable_const.prodMk measurable_id)).neg
  have hE : MeasurableSet {p : DLoc × DLoc |
      supLadderHeight θ v p.1 ≤ -runningInfLoc p.2 r} :=
    measurableSet_le (hB.comp measurable_fst) (hI.comp measurable_snd)
  have hbound : (P.prod P) {p | supLadderHeight θ v p.1 ≤ -runningInfLoc p.2 r} ≤
      ∫⁻ f, ENNReal.ofReal (Real.exp (q * r - supLadderHeight θ v f * lam)) ∂P := by
    rw [Measure.prod_apply hE]
    apply lintegral_mono_ae
    filter_upwards [ae_supLadderPair_path hθ] with f hf
    have hb : 0 ≤ supLadderHeight θ v f := (hf.1 v).2
    simpa only [P, lam, Set.preimage_ofPred_eq, Real.coe_toNNReal _ hb] using
      measure_depth_ge_le_exp hθ r (supLadderHeight θ v f).toNNReal hq
  have hi : Integrable (fun f => Real.exp (-lam * supLadderHeight θ v f)) P := by
    simpa only [neg_zero, zero_mul, zero_sub, ← neg_mul] using
      integrable_exp_neg_supLadder hθ (q := 0) (le_refl 0) hlam v
  calc
    _ ≤ ∫⁻ f, ENNReal.ofReal (Real.exp (q * r - supLadderHeight θ v f * lam)) ∂P := hbound
    _ = ENNReal.ofReal (Real.exp (q * r)) *
        ∫⁻ f, ENNReal.ofReal (Real.exp (-lam * supLadderHeight θ v f)) ∂P := by
      have he (f : DLoc) : q * r - supLadderHeight θ v f * lam =
          q * r + (-lam * supLadderHeight θ v f) := by ring
      simp_rw [he, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.exp (q * r - (v : ℝ) * lam ^ (θ - 1))) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall fun _ => Real.exp_nonneg _),
        (integral_exp_neg_supLadder hθ v (q := 0) (le_refl 0) hlam).2.2,
        ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring

end BGW.StableTrees
