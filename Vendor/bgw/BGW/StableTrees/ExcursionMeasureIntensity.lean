/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureWindow

/-! Identification of the mean excursion point measure with the product intensity.

See Bertoin, *Lévy Processes*, Chapter IV.
-/

@[expose] public section

open MeasureTheory MeasurableSpace Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The local-time Lebesgue measure has no mass at the origin. -/
theorem lebNN_singleton_zero : lebNN {0} = 0 := by
  have he : MeasurableEmbedding ((↑) : ℝ≥0 → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ici
  rw [lebNN, he.comap_apply]
  simp

/-- The local-time Lebesgue measure of an initial closed interval. -/
theorem lebNN_Iic (a : ℝ≥0) : lebNN (Iic a) = (a : ℝ≥0∞) := by
  have hs : Iic a = ({0} : Set ℝ≥0) ∪ Ioc 0 a := by
    ext x
    simp only [mem_Iic, mem_union, mem_singleton_iff, mem_Ioc]
    constructor
    · intro hx
      exact (eq_or_lt_of_le ((show 0 ≤ x from bot_le))).elim (fun h => Or.inl h.symm)
        (fun h => Or.inr ⟨h, hx⟩)
    · rintro (rfl | hx)
      · exact (show 0 ≤ a from bot_le)
      · exact hx.2
  rw [hs, measure_union, lebNN_singleton_zero, lebNN_Ioc]
  · simp
  · exact disjoint_singleton_left.mpr (by simp)
  · exact measurableSet_Ioc

private def lebNN_spanning : lebNN.FiniteSpanningSetsIn (range (Iic : ℝ≥0 → Set ℝ≥0)) where
  set n := Iic (n : ℝ≥0)
  set_mem n := mem_range.mpr ⟨n, rfl⟩
  finite n := by rw [lebNN_Iic]; exact ENNReal.coe_lt_top
  spanning := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt x
    exact mem_iUnion.mpr ⟨n, hn.le⟩

/-- The local-time Lebesgue measure is sigma finite. -/
theorem sigmaFinite_lebNN : SigmaFinite lebNN := lebNN_spanning.sigmaFinite

private theorem lintegral_initialMark_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure)
    (a : ℝ≥0) {A : Set Excursion} (hA : MeasurableSet A) :
    (∫⁻ f, ξ f (Iic a ×ˢ A) ∂(stableLocalLaw θ : Measure DLoc)) =
      (a : ℝ≥0∞) * excursionMeasure θ A := by
  have hzero := (isTimeSimpleLevy_of_ae_eq_excursionPointMeasure hθ hξ hae).1.atZero
  calc
    _ = ∫⁻ f, ξ f (Ioc 0 a ×ˢ A) ∂(stableLocalLaw θ : Measure DLoc) := by
      apply lintegral_congr_ae
      filter_upwards [hzero] with f hf
      apply measure_congr
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hf] with p hp
      have hp0 : p.1 ≠ 0 := by simpa using hp
      simp [mem_prod, pos_iff_ne_zero.mpr hp0]
    _ = _ := by simpa using lintegral_windowMark_eq hθ hξ hae ((show 0 ≤ a from bot_le)) hA

/-- **Intensity measure** is `Leb ⊗ N`: `E ξ(B) = (lebNN.prod N)(B)` for measurable `B`. -/
theorem lintegral_pointMeasure_eq_prod {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure)
    {B : Set (ℝ≥0 × Excursion)} (hB : MeasurableSet B) :
    ∫⁻ f, ξ f B ∂(stableLocalLaw θ : Measure DLoc) =
      (lebNN.prod (excursionMeasure θ)) B := by
  let := sigmaFinite_excursionMeasure hθ
  let ν := Measure.join ((stableLocalLaw θ : Measure DLoc).map ξ)
  have hν {S : Set (ℝ≥0 × Excursion)} (hS : MeasurableSet S) :
      ν S = ∫⁻ f, ξ f S ∂(stableLocalLaw θ : Measure DLoc) := by
    change Measure.join _ S = _
    rw [Measure.join_apply hS, lintegral_map (Measure.measurable_coe hS) hξ]
  have heq : lebNN.prod (excursionMeasure θ) = ν := by
    apply Measure.prod_eq_generateFrom
      (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic ℝ≥0)).symm
      generateFrom_measurableSet isPiSystem_Iic isPiSystem_measurableSet
      lebNN_spanning (excursionMeasure θ).toFiniteSpanningSetsIn
    rintro S ⟨a, rfl⟩ A hA
    rw [hν (measurableSet_Iic.prod hA), lintegral_initialMark_eq hθ hξ hae a hA,
      lebNN_Iic]
  rw [heq, hν hB]

end BGW.StableTrees
