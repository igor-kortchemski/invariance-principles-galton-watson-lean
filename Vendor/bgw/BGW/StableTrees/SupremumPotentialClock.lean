/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialResolvent

/-!
# Exponential-clock representation of reflected resolvents

Bounded Borel functions can be evaluated at the independent clock before computing
their reflected resolvent.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Integration against an exponential law is its positive-half-line density integral. -/
theorem integral_expMeasure_eq {q : ℝ} (hq : 0 < q) (F : ℝ → ℝ) :
    (∫ t, F t ∂expMeasure q) = q * ∫ t in Ioi 0, Real.exp (-q * t) * F t := by
  change (∫ t, F t ∂volume.withDensity (exponentialPDF q)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (f := exponentialPDF q)
    (measurable_exponentialPDFReal q).ennreal_ofReal (by simp [exponentialPDF])]
  have he : (fun t => (exponentialPDF q t).toReal • F t) =
      (Ici 0).indicator (fun t => q * (Real.exp (-q * t) * F t)) := by
    funext t
    by_cases ht : 0 ≤ t
    · rw [exponentialPDF_of_nonneg ht, ENNReal.toReal_ofReal (by positivity),
        indicator_of_mem (s := Ici (0 : ℝ)) ht]
      simp only [smul_eq_mul, neg_mul]
      ring
    · rw [exponentialPDF_of_neg (not_le.mp ht), ENNReal.toReal_zero, zero_smul,
        indicator_of_notMem (s := Ici (0 : ℝ)) ht]
  rw [he, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul]

/-- A bounded measurable function of the path and clock has the discounted-time expectation. -/
theorem integral_expClockLaw_eq {θ q : ℝ} (hq : 0 < q) {H : DLoc × ℝ → ℝ}
    (hH : Measurable H) (hb : ∃ C, ∀ p, |H p| ≤ C) :
    (∫ p, H p ∂expClockLaw θ q) = q * ∫ f,
      (∫ t in Ioi 0, Real.exp (-q * t) * H (f, t)) ∂(stableLocalLaw θ : Measure DLoc) := by
  let := isProbabilityMeasure_expClockLaw θ hq
  let := isProbabilityMeasure_expMeasure hq
  obtain ⟨C, hC⟩ := hb
  have hi : Integrable H (expClockLaw θ q) := Integrable.of_bound hH.aestronglyMeasurable C
    (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hC p))
  rw [expClockLaw, integral_prod H hi]
  simp_rw [integral_expMeasure_eq hq]
  rw [integral_const_mul]

/-- Positive-rate reflected resolvents are expectations at the independent exponential clock. -/
theorem reflectedResolvent_eq_expClockLaw {θ q : ℝ} (hq : 0 < q) {k : ℝ → ℝ}
    (hk : Measurable k) (hb : ∃ C, ∀ r, |k r| ≤ C) (y : ℝ) :
    reflectedResolvent θ q k y = q⁻¹ * ∫ p : DLoc × ℝ,
      k (supReflectedFrom y.toNNReal p.1 p.2.toNNReal) ∂expClockLaw θ q := by
  have hm : Measurable (fun p : DLoc × ℝ => k (supReflectedFrom y.toNNReal p.1 p.2.toNNReal)) :=
    hk.comp (measurable_supReflectedFrom_uncurry.comp
      (measurable_const.prodMk (measurable_fst.prodMk
        (measurable_real_toNNReal.comp measurable_snd))))
  have he := integral_expClockLaw_eq (θ := θ) hq hm
    (by obtain ⟨C, hC⟩ := hb; exact ⟨C, fun p => hC _⟩)
  change (∫ p : DLoc × ℝ, k (supReflectedFrom y.toNNReal p.1 p.2.toNNReal) ∂expClockLaw θ q) =
    q * reflectedResolvent θ q k y at he
  rw [he]
  field_simp

end BGW.StableTrees
