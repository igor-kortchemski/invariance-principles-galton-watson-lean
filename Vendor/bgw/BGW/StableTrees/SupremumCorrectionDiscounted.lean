/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCorrectionPath

/-!
# Progressive discounted heads for the raw auxiliary clock

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- A progressive real process has a progressive bounded-time integral. The integral is
read as a totalized Bochner integral on every path. -/
theorem isStronglyProgressive_integral_head {F : ℝ≥0 → DLoc → ℝ}
    (hF : IsStronglyProgressive DLoc.filtration F) {w : ℝ → ℝ} (hw : Measurable w) :
    IsStronglyProgressive DLoc.filtration
      (fun t f => ∫ s in Ioc (0 : ℝ) t, w s * F s.toNNReal f) := by
  intro T
  let : MeasurableSpace DLoc := DLoc.filtration T
  let G : (Iic T × DLoc) × ℝ → ℝ := fun p =>
    {p : (Iic T × DLoc) × ℝ | 0 < p.2 ∧ p.2 ≤ (p.1.1 : ℝ)}.indicator
      (fun p => w p.2 * F (min p.2.toNNReal T) p.1.2) p
  have hm : Measurable G := by
    apply Measurable.indicator
    · have ht : Measurable (fun p : (Iic T × DLoc) × ℝ =>
          (⟨min p.2.toNNReal T, min_le_right _ _⟩ : Iic T)) :=
        ((measurable_real_toNNReal.comp measurable_snd).min measurable_const).subtype_mk
      exact (hw.comp measurable_snd).mul ((hF T).measurable.comp
        (ht.prodMk (measurable_snd.comp measurable_fst)))
    · exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_subtype_coe.coe_nnreal_real.comp
          (measurable_fst.comp measurable_fst)))
  have he (p : Iic T × DLoc) : (∫ s, G (p, s)) =
      ∫ s in Ioc (0 : ℝ) p.1, w s * F s.toNNReal p.2 := by
    change (∫ s, (Ioc (0 : ℝ) p.1).indicator
      (fun s => w s * F (min s.toNNReal T) p.2) s) = _
    rw [integral_indicator measurableSet_Ioc]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    have hsT : s.toNNReal ≤ T :=
      (Real.toNNReal_le_iff_le_coe).mpr (hs.2.trans (NNReal.coe_le_coe.mpr p.1.2))
    dsimp only
    rw [min_eq_left hsT]
  simpa only [he] using hm.stronglyMeasurable.integral_prod_right' (ν := volume)

private theorem progressive_exp (q : ℝ) :
    IsStronglyProgressive DLoc.filtration (fun t _ => Real.exp (-q * (t : ℝ))) := by
  intro T
  exact (Real.measurable_exp.comp (measurable_const.mul
    (measurable_subtype_coe.coe_nnreal_real.comp measurable_fst))).stronglyMeasurable

/-- The positive-rate error is progressive with the raw integration-by-parts head. -/
theorem isStronglyProgressive_discountedErrorMartingale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    IsStronglyProgressive DLoc.filtration (fun t f => discountedErrorMartingale θ q ε t f) := by
  have he := progressive_exp q
  have hk : IsStronglyProgressive DLoc.filtration
      (fun t f => supOccKernel ε (supReflectedFrom 0 f t)) := by
    intro T
    exact ((measurable_supOccKernel ε).comp
      (isStronglyProgressive_supReflectedFrom 0 T).measurable).stronglyMeasurable
  have hw : Measurable (fun s : ℝ => Real.exp (-q * s)) := by fun_prop
  have hO := isStronglyProgressive_integral_head hk hw
  have hM := isStronglyProgressive_supAuxLocalTime hθ
  have hI := isStronglyProgressive_integral_head hM hw
  have hhead : IsStronglyProgressive DLoc.filtration
      (fun t f => supAuxDiscountedHead θ q t f) :=
    (he.mul hM).add ((isStronglyProgressive_const _ q).mul hI)
  have hu : IsStronglyProgressive DLoc.filtration
      (fun t f => supOccupationResolvent θ q ε (supReflectedFrom 0 f t)) := by
    intro T
    exact ((measurable_reflectedResolvent hθ q (measurable_supOccKernel ε)
      ⟨ε⁻¹, fun r => by
        rw [abs_of_nonneg (supOccKernel_mem_Icc hε r).1]
        exact (supOccKernel_mem_Icc hε r).2⟩).comp
      (isStronglyProgressive_supReflectedFrom 0 T).measurable).stronglyMeasurable
  have hv : IsStronglyProgressive DLoc.filtration
      (fun t f => supPotential θ q (supReflectedFrom 0 f t)) := by
    intro T
    exact ((continuous_supPotential hθ hq).measurable.comp
      (isStronglyProgressive_supReflectedFrom 0 T).measurable).stronglyMeasurable
  exact (hO.sub hhead).add (he.mul (hu.sub hv))

end BGW.StableTrees
