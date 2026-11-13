/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumReflectedFamilyBasic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Markov identities for reflection at the supremum

The joint law of a past-measurable state and an independent future gives the reflected
transition kernel, including on finite stopped events.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters III, IV and VI.
* A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed., Springer, 2014,
  Chapters 3 and 6.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Conditional expectation of the reflected future at a deterministic time. -/
theorem condExp_supReflectedFromLoc_markov {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x s : ℝ≥0)
    {G : DLoc → ℝ} (hG : Measurable G) (hGb : ∃ C : ℝ, ∀ p, |G p| ≤ C) :
    (stableLocalLaw θ : Measure DLoc)[fun f =>
        G (supReflectedFromLoc (supReflectedFrom x f s).toNNReal (DLoc.shift s f)) |
        DLoc.filtration s] =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      fun f => ∫ g, G (supReflectedFromLoc (supReflectedFrom x f s).toNNReal g)
        ∂(stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  let Y : DLoc → ℝ≥0 := fun f => (supReflectedFrom x f s).toNNReal
  let H : ℝ≥0 × DLoc → ℝ := fun p => G (supReflectedFromLoc p.1 p.2)
  have hY : Measurable[DLoc.filtration s] Y :=
    ((measurable_rawFiltration_supReflectedFrom x s).mono
      (DLoc.rawFiltration.le_rightCont s) le_rfl).real_toNNReal
  have hH : Measurable H := hG.comp measurable_supReflectedFromLoc
  obtain ⟨C, hC⟩ := hGb
  have hHb : ∀ p, |H p| ≤ C := fun p => hC _
  have hK : StronglyMeasurable (fun y => ∫ g, H (y, g) ∂P) :=
    hH.stronglyMeasurable.integral_prod_right'
  have hKb : ∀ y, ‖∫ g, H (y, g) ∂P‖ ≤ C := by
    intro y
    simpa using (norm_integral_le_of_norm_le_const (μ := P)
      (Eventually.of_forall fun g => (show ‖H (y, g)‖ ≤ C by
        simpa only [Real.norm_eq_abs] using hHb (y, g))))
  have hi : Integrable (fun f => H (Y f, DLoc.shift s f)) P :=
    Integrable.of_bound (hH.comp ((hY.mono (DLoc.filtration.le s) le_rfl).prodMk
      (DLoc.measurable_shift_fixed s))).aestronglyMeasurable C
      (Eventually.of_forall fun f => by simpa only [Real.norm_eq_abs] using hHb _)
  have hki : Integrable (fun f => ∫ g, H (Y f, g) ∂P) P :=
    Integrable.of_bound (hK.comp_measurable
      (hY.mono (DLoc.filtration.le s) le_rfl)).aestronglyMeasurable C
      (Eventually.of_forall fun f => hKb _)
  apply (ae_eq_condExp_of_forall_setIntegral_eq (DLoc.filtration.le s) hi
    (fun _ _ _ => hki.integrableOn) _
    (hK.comp_measurable hY).aestronglyMeasurable).symm
  intro A hA _
  symm
  apply integral_freeze_shiftAt P P (DLoc.measurable_shift_fixed s) hH ⟨C, hHb⟩
    (m := DLoc.filtration s) (DLoc.filtration.le s) hY hA
  intro B hB _ D hD
  have hi := (Indep_iff _ _ _).mp (indep_filtration_shift_stableLocalLaw hθ s)
    B (DLoc.shift s ⁻¹' D) hB ⟨D, hD, rfl⟩
  have hlaw : P (DLoc.shift s ⁻¹' D) = P D := by
    rw [← Measure.map_apply (DLoc.measurable_shift_fixed s) hD,
      map_shift_stableLocalLaw hθ]
  exact hi.trans (congrArg (fun v => P B * v) hlaw)

/-- **Strong Markov property at a stopping time** of the right-continuous filtration, in product
form over events `A` of the stopped σ-algebra contained in `{τ < ⊤}`. -/
theorem integral_supReflectedFromLoc_strongMarkov {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ)
    {A : Set DLoc} (hA : MeasurableSet[hτ.measurableSpace] A) (hAτ : A ⊆ {f | τ f < ⊤})
    {G : DLoc → ℝ} (hG : Measurable G) (hGb : ∃ C : ℝ, ∀ p, |G p| ≤ C) :
    ∫ f in A, G (supReflectedFromLoc (supReflectedFrom x f (τ f).toNNReal).toNNReal
        (DLoc.shiftAt τ f)) ∂(stableLocalLaw θ : Measure DLoc) =
      ∫ f in A, (∫ g, G (supReflectedFromLoc (supReflectedFrom x f (τ f).toNNReal).toNNReal g)
        ∂(stableLocalLaw θ : Measure DLoc)) ∂(stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  let Y : DLoc → ℝ≥0 := fun f =>
    (stoppedValue (fun t f => supReflectedFrom x f t) τ f).toNNReal
  let H : ℝ≥0 × DLoc → ℝ := fun p => G (supReflectedFromLoc p.1 p.2)
  have hY : Measurable[hτ.measurableSpace] Y :=
    (measurable_stoppedValue (isStronglyProgressive_supReflectedFrom x) hτ).real_toNNReal
  have he : ∀ f ∈ A, Y f = (supReflectedFrom x f (τ f).toNNReal).toNNReal := by
    intro f hf
    have hfin : τ f < ⊤ := hAτ hf
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hfin)
    simp only [Y, stoppedValue, ← ht]
    rfl
  have hH : Measurable H := hG.comp measurable_supReflectedFromLoc
  have hHb : ∃ C : ℝ, ∀ p, |H p| ≤ C := by
    obtain ⟨C, hC⟩ := hGb
    exact ⟨C, fun p => hC _⟩
  have hAg : MeasurableSet A := hτ.measurableSpace_le _ hA
  calc
    _ = ∫ f in A, H (Y f, DLoc.shiftAt τ f) ∂P := by
      apply setIntegral_congr_fun hAg
      intro f hf
      dsimp [H]
      rw [he f hf]
    _ = ∫ f in A, (∫ g, H (Y f, g) ∂P) ∂P := by
      apply integral_freeze_shiftAt P P (DLoc.measurable_shiftAt hτ) hH hHb
        (m := hτ.measurableSpace) hτ.measurableSpace_le hY hA
      intro B hB hBA C hC
      exact measure_inter_preimage_shiftAt hθ hτ hB (hBA.trans hAτ) hC
    _ = _ := by
      apply setIntegral_congr_fun hAg
      intro f hf
      dsimp [H]
      rw [he f hf]


end BGW.StableTrees
