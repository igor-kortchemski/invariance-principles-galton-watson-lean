/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCorrectionBasic

/-!
# Integration by parts for the discounted auxiliary clock

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- On one full-measure event the head and future tail split the entire discounted clock. -/
theorem ae_supAuxDiscountedHead_add_tail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q : ℝ} (hq : 0 < q) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      supAuxDiscountedHead θ q t f + supAuxDiscountedTail θ q t f =
        supAuxDiscountedTail θ q 0 f := by
  filter_upwards [ae_supAuxLocalTime_continuous hθ,
    (integrable_exp_supAuxLocalTime_prod hθ hq 0).prod_left_ae] with f hf hi
  change IntegrableOn (fun s : ℝ => Real.exp (-q * s) * supAuxLocalTime θ f s.toNNReal)
    (Ioi (0 : ℝ)) at hi
  have hzero := pathStieltjes_integral_exp ⟨hf.2.1, hf.2.2⟩ hq 0
    (by simpa only [hf.1, sub_zero, NNReal.coe_zero] using hi)
  simp only [NNReal.coe_zero, hf.1, sub_zero] at hzero
  intro t
  have hit := hi.mono_set (Ioi_subset_Ioi t.coe_nonneg)
  have hdiff : IntegrableOn (fun s : ℝ => Real.exp (-q * s) *
      (supAuxLocalTime θ f s.toNNReal - supAuxLocalTime θ f t)) (Ioi (t : ℝ)) := by
    have hd := hit.sub
      ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hq) (t : ℝ)).mul_const
        (supAuxLocalTime θ f t))
    change IntegrableOn (fun s => Real.exp (-q * s) * supAuxLocalTime θ f s.toNNReal -
      Real.exp (-q * s) * supAuxLocalTime θ f t) (Ioi (t : ℝ)) at hd
    simpa only [mul_sub] using hd
  have ht := (pathStieltjes_integral_exp ⟨hf.2.1, hf.2.2⟩ hq t hdiff).2
  have hp := discounted_cumulative_eq_primitive hq (t : ℝ)
    (supAuxLocalTime θ f t) hit
  have hs := setIntegral_union (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := (t : ℝ)))
    measurableSet_Ioi
    (hi.mono_set Ioc_subset_Ioi_self) hit
  rw [Ioc_union_Ioi_eq_Ioi t.coe_nonneg] at hs
  change supAuxDiscountedHead θ q t f +
    (∫ s in Ioi (t : ℝ), Real.exp (-q * s) ∂(pathStieltjes (supAuxLocalTime θ f)).measure) =
    (∫ s in Ioi (0 : ℝ), Real.exp (-q * s) ∂(pathStieltjes (supAuxLocalTime θ f)).measure)
  rw [ht, hp, hzero.2]
  unfold supAuxDiscountedHead
  rw [hs]
  ring

/-- Almost surely the integration-by-parts head equals the Stieltjes head at all times. -/
theorem ae_supAuxDiscountedHead_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      supAuxDiscountedHead θ q t f =
        ∫ s in Ioc (0 : ℝ) t, Real.exp (-q * s) ∂(supAuxStieltjes θ f).measure := by
  filter_upwards [ae_supAuxDiscountedHead_add_tail hθ hq,
    ae_supAuxLocalTime_continuous hθ,
    (integrable_exp_supAuxLocalTime_prod hθ hq 0).prod_left_ae] with f hsplit hf hi
  change IntegrableOn (fun s : ℝ => Real.exp (-q * s) * supAuxLocalTime θ f s.toNNReal)
    (Ioi (0 : ℝ)) at hi
  have hzero := pathStieltjes_integral_exp ⟨hf.2.1, hf.2.2⟩ hq 0
    (by simpa only [hf.1, sub_zero, NNReal.coe_zero] using hi)
  have hz : IntegrableOn (fun s => Real.exp (-q * s)) (Ioi (0 : ℝ))
      (supAuxStieltjes θ f).measure := hzero.1
  intro t
  have hs := setIntegral_union (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := (t : ℝ)))
    measurableSet_Ioi
    (hz.mono_set Ioc_subset_Ioi_self) (hz.mono_set (Ioi_subset_Ioi t.coe_nonneg))
  rw [Ioc_union_Ioi_eq_Ioi t.coe_nonneg] at hs
  have hst := hsplit t
  unfold supAuxDiscountedTail at hst
  simp only [NNReal.coe_zero] at hst
  linarith only [hs, hst]

end BGW.StableTrees
