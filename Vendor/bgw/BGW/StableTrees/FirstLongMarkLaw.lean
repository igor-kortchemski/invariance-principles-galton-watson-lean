/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.FirstLongMarkCompensation
public import BGW.StableTrees.FirstLongMarkDensity

/-!
# Joint law of the first long label and excursion

Predictable compensation identifies the joint density. The label density is exponential and
the excursion factor is the normalized restriction to lifetimes greater than one.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

variable {θ : ℝ}

private theorem lintegral_tailLaw (hθ : 1 < θ ∧ θ ≤ 2) (G : Excursion → ℝ≥0∞) :
    (∫⁻ e, G e ∂(tailExcursionLaw θ : Measure Excursion)) =
      ENNReal.ofReal (Real.Gamma (1 - 1 / θ)) *
        (∫⁻ e in {e : Excursion | 1 < e.lifetime}, G e ∂excursionMeasure θ) := by
  have hset : {e : Excursion | (1 : ℝ) < (e.lifetime : ℝ)} =
      {e : Excursion | (1 : ℝ≥0) < e.lifetime} := by
    ext e
    exact_mod_cast (Iff.rfl : (1 : ℝ≥0) < e.lifetime ↔ (1 : ℝ≥0) < e.lifetime)
  rw [coe_tailExcursionLaw hθ, tailExcursionMeasure, lintegral_smul_measure, smul_eq_mul,
    excursionTail, hset]

/-- **Exponential/product law**: the first long label is `Exp(r_θ)`, the first long mark has
law `tailExcursionLaw θ`, and they are independent. -/
theorem map_firstLongLabel_firstLongMark (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLocalLaw θ : Measure DLoc).map (fun f => (firstLongLabel f, firstLongMark f)) =
      (firstLongLabelLaw θ).prod (tailExcursionLaw θ : Measure Excursion) := by
  have := isProbabilityMeasure_firstLongLabelLaw hθ
  have hpair : AEMeasurable (fun f : DLoc => (firstLongLabel f, firstLongMark f))
      (stableLocalLaw θ : Measure DLoc) :=
    (aemeasurable_firstLongLabel hθ).prodMk (aemeasurable_firstLongMark hθ)
  have htest (F : ℝ≥0 × Excursion → ℝ≥0∞) (hF : Measurable F) :
      (∫⁻ p, F p ∂(stableLocalLaw θ : Measure DLoc).map
        (fun f => (firstLongLabel f, firstLongMark f))) =
      ∫⁻ p, F p ∂(firstLongLabelLaw θ).prod (tailExcursionLaw θ : Measure Excursion) := by
    rw [lintegral_map' hF.aemeasurable hpair, lintegral_firstLong_pair hθ hF,
      lintegral_prod F hF.aemeasurable]
    have hK : Measurable (fun x : ℝ≥0 =>
        ∫⁻ e, F (x, e) ∂(tailExcursionLaw θ : Measure Excursion)) :=
      hF.lintegral_prod_right'
    rw [lintegral_firstLongLabelLaw hθ hK]
    apply lintegral_congr
    intro x
    rw [lintegral_tailLaw hθ]
    symm
    calc
      _ = (ENNReal.ofReal (longRate θ) * ENNReal.ofReal (Real.Gamma (1 - 1 / θ))) *
          (ENNReal.ofReal (Real.exp (-((x : ℝ) * longRate θ))) *
            (∫⁻ e in {e : Excursion | 1 < e.lifetime}, F (x, e) ∂excursionMeasure θ)) := by
        ac_rfl
      _ = _ := by rw [longRate_mul_gamma hθ, one_mul]
  apply Measure.ext
  intro A hA
  calc
    _ = ∫⁻ p, A.indicator 1 p ∂(stableLocalLaw θ : Measure DLoc).map
        (fun f => (firstLongLabel f, firstLongMark f)) := (lintegral_indicator_one hA).symm
    _ = ∫⁻ p, A.indicator 1 p
        ∂(firstLongLabelLaw θ).prod (tailExcursionLaw θ : Measure Excursion) :=
      htest (A.indicator 1) (measurable_const.indicator hA)
    _ = _ := lintegral_indicator_one hA

/-- Identification of the selected mark with `tailExcursionLaw θ` (a corollary of the product
law; no extraction convergence is assumed). -/
theorem map_firstLongMark (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLocalLaw θ : Measure DLoc).map firstLongMark =
      (tailExcursionLaw θ : Measure Excursion) := by
  have hpair : AEMeasurable (fun f : DLoc => (firstLongLabel f, firstLongMark f))
      (stableLocalLaw θ : Measure DLoc) :=
    (aemeasurable_firstLongLabel hθ).prodMk (aemeasurable_firstLongMark hθ)
  have := isProbabilityMeasure_firstLongLabelLaw hθ
  calc
    _ = ((stableLocalLaw θ : Measure DLoc).map
        (fun f => (firstLongLabel f, firstLongMark f))).map Prod.snd :=
      (AEMeasurable.map_map_of_aemeasurable
        (f := fun f : DLoc => (firstLongLabel f, firstLongMark f))
        (g := Prod.snd) measurable_snd.aemeasurable hpair).symm
    _ = _ := by rw [map_firstLongLabel_firstLongMark hθ, Measure.map_snd_prod,
      measure_univ, one_smul]

/-- Marginal of the first label: `Exp(r_θ)`. -/
theorem map_firstLongLabel (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableLocalLaw θ : Measure DLoc).map firstLongLabel = firstLongLabelLaw θ := by
  have hpair : AEMeasurable (fun f : DLoc => (firstLongLabel f, firstLongMark f))
      (stableLocalLaw θ : Measure DLoc) :=
    (aemeasurable_firstLongLabel hθ).prodMk (aemeasurable_firstLongMark hθ)
  calc
    _ = ((stableLocalLaw θ : Measure DLoc).map
        (fun f => (firstLongLabel f, firstLongMark f))).map Prod.fst :=
      (AEMeasurable.map_map_of_aemeasurable
        (f := fun f : DLoc => (firstLongLabel f, firstLongMark f))
        (g := Prod.fst) measurable_fst.aemeasurable hpair).symm
    _ = _ := by rw [map_firstLongLabel_firstLongMark hθ, Measure.map_fst_prod,
      measure_univ, one_smul]

end BGW.StableTrees
