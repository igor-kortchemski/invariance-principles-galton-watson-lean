/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.FirstLongMarkSelection

/-!
# Exponential density for the first long label

The nonnegative label law has density `r exp(-rx)` relative to local-time Lebesgue measure.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

variable {θ : ℝ}

/-- The first-label exponential law integrates against its usual density on nonnegative labels. -/
theorem lintegral_firstLongLabelLaw (hθ : 1 < θ ∧ θ ≤ 2)
    {F : ℝ≥0 → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, F x ∂firstLongLabelLaw θ) =
      ∫⁻ x, ENNReal.ofReal (longRate θ) *
        ENNReal.ofReal (Real.exp (-((x : ℝ) * longRate θ))) * F x ∂lebNN := by
  have hnn : Measurable (Real.toNNReal : ℝ → ℝ≥0) := measurable_id.real_toNNReal
  rw [firstLongLabelLaw, lintegral_map hF hnn, expMeasure, gammaMeasure]
  have hdensity : Measurable (gammaPDF 1 (longRate θ)) :=
    (measurable_gammaPDFReal 1 (longRate θ)).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul (volume : Measure ℝ) hdensity
    (g := fun x : ℝ => F x.toNNReal) (hF.comp hnn)]
  change (∫⁻ x : ℝ, gammaPDF 1 (longRate θ) x * F x.toNNReal) = _
  have hrestrict : (∫⁻ x : ℝ, gammaPDF 1 (longRate θ) x * F x.toNNReal) =
      ∫⁻ x in Ici (0 : ℝ), gammaPDF 1 (longRate θ) x * F x.toNNReal := by
    rw [← lintegral_indicator measurableSet_Ici]
    apply lintegral_congr
    intro x
    by_cases hx : 0 ≤ x
    · rw [Set.indicator_of_mem (show x ∈ Ici (0 : ℝ) from hx)]
    · rw [Set.indicator_of_notMem (show x ∉ Ici (0 : ℝ) from hx),
        gammaPDF_of_neg (lt_of_not_ge hx), zero_mul]
  rw [hrestrict]
  have he := lintegral_subtype_comap (μ := (volume : Measure ℝ))
    (s := Ici (0 : ℝ)) measurableSet_Ici
    (fun x : ℝ => gammaPDF 1 (longRate θ) x * F x.toNNReal)
  change (∫⁻ x : ℝ≥0, gammaPDF 1 (longRate θ) x * F (x : ℝ).toNNReal ∂lebNN) = _ at he
  rw [← he]
  apply lintegral_congr
  intro x
  rw [Real.toNNReal_coe]
  have hpdf : gammaPDF 1 (longRate θ) (x : ℝ) =
      ENNReal.ofReal (longRate θ) *
        ENNReal.ofReal (Real.exp (-((x : ℝ) * longRate θ))) := by
    change exponentialPDF (longRate θ) x = _
    calc
      _ = ENNReal.ofReal (longRate θ * Real.exp (-(longRate θ * (x : ℝ)))) :=
        exponentialPDF_of_nonneg (r := longRate θ) (x := (x : ℝ)) x.2
      _ = _ := by rw [ENNReal.ofReal_mul (longRate_pos hθ).le,
        mul_comm (longRate θ) (x : ℝ)]
  rw [hpdf]

/-- The exponential first-label law has total mass one. -/
theorem isProbabilityMeasure_firstLongLabelLaw (hθ : 1 < θ ∧ θ ≤ 2) :
    IsProbabilityMeasure (firstLongLabelLaw θ) := by
  have := isProbabilityMeasure_expMeasure (longRate_pos hθ)
  change IsProbabilityMeasure ((expMeasure (longRate θ)).map Real.toNNReal)
  infer_instance

/-- The long-mark rate cancels the tail-law normalization. -/
theorem longRate_mul_gamma (hθ : 1 < θ ∧ θ ≤ 2) :
    ENNReal.ofReal (longRate θ) * ENNReal.ofReal (Real.Gamma (1 - 1 / θ)) = 1 := by
  rw [← ENNReal.ofReal_mul (longRate_pos hθ).le, longRate,
    one_div_mul_cancel (ne_of_gt (Real.Gamma_pos_of_pos
      (sub_pos.mpr ((div_lt_one (by linarith)).mpr hθ.1)))), ENNReal.ofReal_one]

end BGW.StableTrees
