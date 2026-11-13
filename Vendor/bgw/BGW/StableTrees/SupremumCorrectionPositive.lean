/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCorrectionDiscounted
public import BGW.StableTrees.SupremumCorrectionStieltjes

/-!
# The positive-rate error martingale

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem martingale_head_of_condExp_tail {P : Measure DLoc} [IsProbabilityMeasure P]
    {H G : ℝ≥0 → DLoc → ℝ} {B : DLoc → ℝ} {A : ℝ≥0 → DLoc → ℝ}
    (hH : StronglyAdapted DLoc.filtration H) (hG : StronglyAdapted DLoc.filtration G)
    (hB : Integrable B P) (hA : ∀ t, Integrable (A t) P)
    (hsplit : ∀ t, (fun f => H t f + A t f) =ᵐ[P] B)
    (hcond : ∀ t, P[A t | DLoc.filtration t] =ᵐ[P] G t) :
    Martingale (fun t f => H t f + G t f) DLoc.filtration P := by
  have hHi (t : ℝ≥0) : Integrable (H t) P := by
    apply (hB.sub (hA t)).congr
    filter_upwards [hsplit t] with f hf
    change B f - A t f = H t f
    linarith only [hf]
  have hc (t : ℝ≥0) : P[B | DLoc.filtration t] =ᵐ[P] fun f => H t f + G t f := by
    calc
      _ =ᵐ[P] P[(fun f => H t f + A t f) | DLoc.filtration t] :=
        condExp_congr_ae (hsplit t).symm
      _ =ᵐ[P] P[H t | DLoc.filtration t] + P[A t | DLoc.filtration t] :=
        condExp_add (hHi t) (hA t) _
      _ =ᵐ[P] _ := by
        filter_upwards [hcond t] with f hf
        simp only [Pi.add_apply, condExp_of_stronglyMeasurable
          (DLoc.filtration.le t) (hH t) (hHi t), hf]
  exact (martingale_condExp B DLoc.filtration P).congr
    (fun t => (hH t).add (hG t)) hc

/-- Conditional occupation and clock potentials give the positive-rate error martingale. -/
theorem martingale_discountedErrorMartingale {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    Martingale (fun t f => discountedErrorMartingale θ q ε t f) DLoc.filtration
      (stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  have hw : Measurable (fun s : ℝ => Real.exp (-q * s)) := by fun_prop
  have he : IsStronglyProgressive DLoc.filtration
      (fun t _ => Real.exp (-q * (t : ℝ))) := by
    intro T
    exact (Real.measurable_exp.comp (measurable_const.mul
      (measurable_subtype_coe.coe_nnreal_real.comp measurable_fst))).stronglyMeasurable
  have hk : IsStronglyProgressive DLoc.filtration
      (fun t f => supOccKernel ε (supReflectedFrom 0 f t)) := by
    intro T
    exact ((measurable_supOccKernel ε).comp
      (isStronglyProgressive_supReflectedFrom 0 T).measurable).stronglyMeasurable
  have hO : StronglyAdapted DLoc.filtration
      (fun t f => supOccupationDiscountedHead q ε t f) :=
    (isStronglyProgressive_integral_head hk hw).stronglyAdapted
  have hM := isStronglyProgressive_supAuxLocalTime hθ
  have hMh : StronglyAdapted DLoc.filtration (fun t f => supAuxDiscountedHead θ q t f) :=
    ((he.mul hM).add ((isStronglyProgressive_const _ q).mul
      (isStronglyProgressive_integral_head hM hw))).stronglyAdapted
  have hkb : ∃ C, ∀ r, |supOccKernel ε r| ≤ C :=
    ⟨ε⁻¹, fun r => by
      rw [abs_of_nonneg (supOccKernel_mem_Icc hε r).1]
      exact (supOccKernel_mem_Icc hε r).2⟩
  have hU : StronglyAdapted DLoc.filtration
      (fun t f => Real.exp (-q * t) * supOccupationResolvent θ q ε (supReflectedFrom 0 f t)) := by
    intro t
    have hm := (measurable_reflectedResolvent hθ q (measurable_supOccKernel ε) hkb).comp
      ((isStronglyProgressive_supReflectedFrom 0).stronglyAdapted t).measurable
    exact (he.stronglyAdapted t).mul hm.stronglyMeasurable
  have hV : StronglyAdapted DLoc.filtration
      (fun t f => Real.exp (-q * t) * supPotential θ q (supReflectedFrom 0 f t)) := by
    intro t
    exact (he.stronglyAdapted t).mul
      ((continuous_supPotential hθ hq).comp_stronglyMeasurable
        ((isStronglyProgressive_supReflectedFrom 0).stronglyAdapted t))
  have hsplitO (t : ℝ≥0) :
      (fun f => supOccupationDiscountedHead q ε t f + supAuxOccupationTail q ε t f) =ᵐ[P]
        supAuxOccupationTail q ε 0 := by
    apply ae_of_all
    intro f
    have hi := integrableOn_supAuxKernel_exp hq hε (0 : ℝ≥0) f
    have hs := setIntegral_union (Ioc_disjoint_Ioi_same (a := (0 : ℝ)) (b := (t : ℝ)))
      measurableSet_Ioi (hi.mono_set Ioc_subset_Ioi_self)
      (hi.mono_set (Ioi_subset_Ioi t.coe_nonneg))
    rw [Ioc_union_Ioi_eq_Ioi t.coe_nonneg] at hs
    exact hs.symm
  have hmartO := martingale_head_of_condExp_tail hO hU
    (integrable_supAuxOccupationTail θ hq hε 0)
    (fun t => integrable_supAuxOccupationTail θ hq hε t) hsplitO
    (fun t => condExp_reflectedResolvent_tail hθ hq 0 t (measurable_supOccKernel ε) hkb)
  have hmartM := martingale_head_of_condExp_tail hMh hV
    (integrable_supAuxDiscountedTail hθ hq 0)
    (fun t => integrable_supAuxDiscountedTail hθ hq t)
    (fun t => (ae_supAuxDiscountedHead_add_tail hθ hq).mono (fun _ hf => hf t))
    (fun t => condExp_supAuxDiscountedTail hθ hq t)
  apply (hmartO.sub hmartM).congr
    (isStronglyProgressive_discountedErrorMartingale hθ hq hε).stronglyAdapted
  intro t
  apply ae_of_all
  intro f
  change _ = discountedErrorMartingale θ q ε t f
  unfold discountedErrorMartingale
  simp only [Pi.sub_apply]
  ring

end BGW.StableTrees
