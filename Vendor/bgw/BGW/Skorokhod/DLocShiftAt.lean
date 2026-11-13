/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.DLocBasic
public import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Random-time shifts of local càdlàg paths

This file defines the centered shift of a local càdlàg path at an extended nonnegative random
time and records its basic measurability properties, including measurability of the stopped
coordinates (O. Kallenberg, *Foundations of Modern Probability*, 2nd ed., Springer, 2002,
Chapter 7).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.Skorokhod.DLoc

/-- **Post-`τ` centered shift.** `shiftAt τ f = (u ↦ f (τ f + u) - f (τ f))` when `τ f < ⊤`;
junk value `shift 0 f` when `τ f = ⊤`. -/
noncomputable def shiftAt (τ : DLoc → ℝ≥0∞) (f : DLoc) : DLoc :=
  DLoc.shift (τ f).toNNReal f

/-- Evaluation of the post-`τ` shift on `{τ < ⊤}`. -/
theorem eval_shiftAt (τ : DLoc → ℝ≥0∞) (u : ℝ≥0) {f : DLoc} (hf : τ f < ⊤) :
    DLoc.eval u (shiftAt τ f) = DLoc.eval ((τ f).toNNReal + u) f - DLoc.eval (τ f).toNNReal f := by
  -- `hf` is part of the stated interface; the evaluation formula holds definitionally.
  have _hf := hf
  rfl

/-- `shiftAt` at a constant time is the deterministic shift. -/
theorem shiftAt_const (s : ℝ≥0) : shiftAt (fun _ => (s : ℝ≥0∞)) = DLoc.shift s := by
  rfl

/-- A stopping time of the right-continuous filtration is Borel measurable, hence so is
`shiftAt τ` on all of `DLoc` (the junk branch on `{τ = ⊤}` is measurable too); in particular its
restriction to `{τ < ⊤}` is measurable. -/
theorem measurable_shiftAt {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ) :
    Measurable (shiftAt τ) := by
  exact measurable_shift.comp (hτ.measurable'.ennreal_toNNReal.prodMk measurable_id)

/-- `{τ < ⊤}` is an event of the stopped σ-algebra. -/
theorem measurableSet_lt_top_stopped {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ) :
    MeasurableSet[hτ.measurableSpace] {f | τ f < ⊤} := by
  exact hτ.measurable measurableSet_Iio

/-- **Stopped coordinate, everywhere form.** Mathlib's `stoppedValue` (junk value on `{τ = ⊤}`)
of the coordinate process is measurable for the stopped σ-algebra. -/
theorem measurable_stoppedValue_eval {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ) :
    Measurable[hτ.measurableSpace] (stoppedValue (fun t (f : DLoc) => DLoc.eval t f) τ) := by
  exact measurable_stoppedValue isStronglyProgressive_eval hτ

/-- **Stopped coordinate**, for `τ < ⊤` everywhere: `f ↦ f (τ f)` is `hτ.measurableSpace`-
measurable. -/
theorem measurable_eval_toNNReal_stopped {τ : DLoc → ℝ≥0∞}
    (hτ : IsStoppingTime DLoc.filtration τ) (hfin : ∀ f, τ f < ⊤) :
    Measurable[hτ.measurableSpace] (fun f : DLoc => DLoc.eval (τ f).toNNReal f) := by
  have heq : (fun f : DLoc => DLoc.eval (τ f).toNNReal f) =
      stoppedValue (fun t (f : DLoc) => DLoc.eval t f) τ := by
    funext f
    simp only [stoppedValue]
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt (hfin f))
    rw [← ht]
    rfl
  rw [heq]
  exact measurable_stoppedValue_eval hτ

end BGW.Skorokhod.DLoc

namespace BGW.Skorokhod

/-- Freezing a stopped-state coordinate turns integration of a bounded measurable functional
of an independent future into an iterated integral. -/
theorem integral_freeze_shiftAt (P : Measure DLoc) [IsFiniteMeasure P]
    (Q : Measure DLoc) [IsFiniteMeasure Q]
    {Y : DLoc → ℝ≥0} {Z : DLoc → DLoc} (hZ : Measurable Z)
    {A : Set DLoc} {H : ℝ≥0 × DLoc → ℝ} (hH : Measurable H)
    (hHb : ∃ C : ℝ, ∀ p, |H p| ≤ C) {m : MeasurableSpace DLoc}
    (hm : m ≤ DLoc.instMeasurableSpace) (hY : Measurable[m] Y)
    (hA : MeasurableSet[m] A)
    (hfact : ∀ B, MeasurableSet[m] B → B ⊆ A →
      ∀ C, MeasurableSet[DLoc.instMeasurableSpace] C →
        P (B ∩ Z ⁻¹' C) = P B * Q C) :
    ∫ f in A, H (Y f, Z f) ∂P = ∫ f in A, (∫ g, H (Y f, g) ∂Q) ∂P := by
  let : MeasurableSpace DLoc := DLoc.instMeasurableSpace
  have hYg : Measurable Y := hY.mono hm le_rfl
  have hj : (P.restrict A).map (fun f => (Y f, Z f)) =
      ((P.restrict A).map Y).prod Q := by
    apply Measure.ext_prod
    intro B C hB hC
    rw [Measure.map_apply (hYg.prodMk hZ) (hB.prod hC),
      Measure.prod_prod, Measure.map_apply hYg hB]
    rw [Measure.restrict_apply ((hYg.prodMk hZ) (hB.prod hC)),
      Measure.restrict_apply (hYg hB)]
    have heq : (fun f => (Y f, Z f)) ⁻¹' (B ×ˢ C) ∩ A =
        (Y ⁻¹' B ∩ A) ∩ Z ⁻¹' C := by
      ext f
      simp only [mem_inter_iff, mem_preimage, mem_prod]
      tauto
    rw [heq]
    exact hfact _ ((hY hB).inter hA) inter_subset_right _ hC
  obtain ⟨C, hC⟩ := hHb
  have hi : Integrable H (((P.restrict A).map Y).prod Q) :=
    Integrable.of_bound hH.aestronglyMeasurable C (Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs] using hC p)
  calc
    _ = ∫ p, H p ∂((P.restrict A).map (fun f => (Y f, Z f))) :=
      (integral_map (hYg.prodMk hZ).aemeasurable hH.aestronglyMeasurable).symm
    _ = ∫ p, H p ∂(((P.restrict A).map Y).prod Q) := by rw [hj]
    _ = ∫ y, (∫ g, H (y, g) ∂Q) ∂((P.restrict A).map Y) := integral_prod H hi
    _ = _ := integral_map hYg.aemeasurable
      hH.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable

end BGW.Skorokhod
