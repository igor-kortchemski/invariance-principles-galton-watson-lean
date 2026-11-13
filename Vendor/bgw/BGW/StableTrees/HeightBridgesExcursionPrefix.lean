/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridgesExcursionBasic

/-!
# Absolute continuity of excursion increment windows

The forward Markov property at a positive deterministic age transfers stable null sets
to centered excursion increments on an interior window. Killing agrees with the full path
on survival, and no restart at the random excursion start is used.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Centering an unkilled initial window of a killed path recovers the stable prefix. -/
theorem restrict_center_killedPath {f : DLoc} {y r τ : ℝ≥0}
    (hT : firstPassageBelow y f = (τ : WithTop ℝ≥0)) (hr : r < τ) (hf : f.1 0 = 0) :
    DLoc.restrict r (DLoc.shift 0 (killedPath y f)) = DLoc.restrict r f := by
  apply BGW.Skorokhod.ext
  intro u
  let v : ℝ≥0 := ⟨u, u.2.1⟩
  have hv : v ≤ r := u.2.2
  change (killedPath y f).1 (0 + v) - (killedPath y f).1 0 = f.1 v
  rw [zero_add, killedPath_apply_of_lt_top hT, killedPath_apply_of_lt_top hT,
    min_eq_left (hv.trans hr.le), min_eq_left (show (0 : ℝ≥0) ≤ τ from zero_le), hf]
  ring

/-- Centered increments of a future excursion path are its ordinary centered shift. -/
theorem shift_zero_futureFrom (s : ℝ≥0) (e : Excursion) :
    DLoc.shift 0 (futureFrom s e) = DLoc.shift s e.path := by
  apply Subtype.ext
  funext u
  change (futureFrom s e).1 (0 + u) - (futureFrom s e).1 0 = _
  rw [futureFrom_apply, futureFrom_apply, zero_add, add_zero]
  rfl

/-- A null stable prefix event remains null for surviving centered killed paths. -/
theorem killedStableKernel_center_prefix_null {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (r y : ℝ≥0) {A : Set (D (r : ℝ) ℝ)} (hA : MeasurableSet A)
    (hnull : ((stableLocalLaw θ : Measure DLoc).map (DLoc.restrict r)) A = 0) :
    killedStableKernel θ y
      {g | 0 < g.1 r ∧ DLoc.restrict r (DLoc.shift 0 g) ∈ A} = 0 := by
  have hB : MeasurableSet
      {g : DLoc | 0 < g.1 r ∧ DLoc.restrict r (DLoc.shift 0 g) ∈ A} :=
    (measurableSet_lt measurable_const (DLoc.measurable_eval r)).inter
      (((DLoc.measurable_restrict r).comp (DLoc.measurable_shift_fixed 0)) hA)
  by_cases hy : y = 0
  · subst y
    rw [killedStableKernel_zero hθ, Measure.dirac_apply' _ hB,
      Set.indicator_of_notMem (show zeroLoc ∉
        {g : DLoc | 0 < g.1 r ∧ DLoc.restrict r (DLoc.shift 0 g) ∈ A} by
          rintro ⟨h, _⟩
          exact (lt_irrefl (0 : ℝ)) h)]
  have hkill : Measurable (killedPath y) :=
    measurable_killedPath_uncurry.comp (measurable_const.prodMk measurable_id)
  rw [killedStableKernel_apply, Measure.map_apply hkill hB]
  rw [Measure.map_apply (DLoc.measurable_restrict r) hA] at hnull
  apply le_antisymm _ zero_le
  apply le_trans (measure_mono_ae ?_) hnull.le
  filter_upwards [ae_killedPath_spec hθ y (pos_iff_ne_zero.mpr hy),
    ae_passageTime_eq_firstPassageBelow hθ, ae_eval_zero_stableLocalLaw hθ]
      with f hf hT hf0
  rintro ⟨hpos, hmem⟩
  have hbefore : r < passageTime y f := by
    by_contra hn
    have hz := hf.2.2.2 r (by rw [hT.1 y, WithTop.coe_le_coe]; exact not_lt.mp hn)
    exact hpos.ne' hz
  rwa [restrict_center_killedPath (hT.1 y) hbefore hf0] at hmem

/-- Centered excursion increments strictly after the start have an absolutely continuous
prefix law on survival to the end of their window. -/
theorem excursion_shift_prefix_absolutelyContinuous {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (s r : ℝ≥0) (hs : 0 < s) :
    (((excursionMeasure θ).restrict {e : Excursion | s + r < e.lifetime}).map
      (fun e => DLoc.restrict r (DLoc.shift s e.path))) ≪
        (stableLocalLaw θ : Measure DLoc).map (DLoc.restrict r) := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hnull
  let B : Set DLoc := {g | 0 < g.1 r ∧ DLoc.restrict r (DLoc.shift 0 g) ∈ A}
  have hB : MeasurableSet B :=
    (measurableSet_lt measurable_const (DLoc.measurable_eval r)).inter
      (((DLoc.measurable_restrict r).comp (DLoc.measurable_shift_fixed 0)) hA)
  have hmap : Measurable (fun e : Excursion => DLoc.restrict r (DLoc.shift s e.path)) :=
    (DLoc.measurable_restrict r).comp
      ((DLoc.measurable_shift_fixed s).comp measurable_excursion_path)
  rw [Measure.map_apply hmap hA, Measure.restrict_apply (hmap hA)]
  have hmarkov := excursion_markov_lintegral hθ s hs (fun _ => 1) measurable_const
    (B.indicator (fun _ => 1)) (measurable_const.indicator hB)
  simp only [one_mul] at hmarkov
  have hzero : (∫⁻ e in {e : Excursion | s < e.lifetime},
      ∫⁻ f, B.indicator (fun _ => 1) f ∂killedStableKernel θ (e.valueNN s)
        ∂excursionMeasure θ) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards with e
    exact (lintegral_indicator_one hB).trans
      (killedStableKernel_center_prefix_null hθ r _ hA hnull)
  have hmarkovzero := hmarkov.trans hzero
  have hpre : MeasurableSet {e : Excursion | futureFrom s e ∈ B} :=
    (measurable_futureFrom s) hB
  change (∫⁻ e in {e : Excursion | s < e.lifetime},
    {e : Excursion | futureFrom s e ∈ B}.indicator (fun _ => 1) e
      ∂excursionMeasure θ) = 0 at hmarkovzero
  have hmass : ((excursionMeasure θ).restrict {e : Excursion | s < e.lifetime})
      {e | futureFrom s e ∈ B} = 0 :=
    (lintegral_indicator_one hpre).symm.trans hmarkovzero
  rw [Measure.restrict_apply hpre] at hmass
  apply le_antisymm _ zero_le
  apply le_trans (measure_mono_ae ?_) hmass.le
  filter_upwards [ae_excursionMeasure_support hθ] with e he
  rintro ⟨hmem, htime⟩
  have hsr : s ≤ s + r := le_add_of_nonneg_right (show 0 ≤ r from zero_le)
  exact ⟨⟨by
    rw [futureFrom_apply]
    exact he.1 (s + r) (hs.trans_le hsr) htime, by
    rwa [shift_zero_futureFrom]⟩, hsr.trans_lt htime⟩

end BGW.StableTrees
