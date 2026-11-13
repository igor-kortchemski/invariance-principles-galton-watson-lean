/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridgesExcursionBasic

/-!
# Excursion small-depth estimate

The forward excursion Markov property bounds the small future-infimum depth at a
positive age. The coefficient is the finite excursion survival mass at that age.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- A small future-infimum depth under the excursion measure has a linear cutoff bound. -/
theorem exists_excursion_small_depth_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s r : ℝ≥0) (ε : ℝ), 0 < s → 0 < r → 0 < ε →
      (excursionMeasure θ).restrict {e : Excursion | s + r < e.lifetime}
        {e | e.path.1 s < futureInf e.path (s + r) s + ε} ≤
      excursionMeasure θ {e : Excursion | s < e.lifetime} *
        ENNReal.ofReal (C * ε * (r : ℝ) ^ (-1 / θ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_killedStableKernel_small_depth_le hθ
  refine ⟨C, hC, fun s r ε hs hr hε => ?_⟩
  let A : Set DLoc := {g | 0 < g.1 r ∧ g.1 0 < futureInf g r 0 + ε}
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const (DLoc.measurable_eval r)).inter
      (measurableSet_lt (DLoc.measurable_eval 0)
        ((measurable_futureInf_uncurry.comp
          ((measurable_const.prodMk measurable_const).prodMk measurable_id)).add
            measurable_const))
  have hsurv : MeasurableSet {e : Excursion | s < e.lifetime} :=
    measurableSet_lt measurable_const measurable_excursion_lifetime
  have hmargin : MeasurableSet
      {e : Excursion | e.path.1 s < futureInf e.path (s + r) s + ε} :=
    measurableSet_lt (measurable_excursion_eval s)
      ((measurable_futureInf_uncurry.comp
        ((measurable_const.prodMk measurable_const).prodMk measurable_excursion_path)).add
          measurable_const)
  have hmarkov := excursion_markov_lintegral hθ s hs (fun _ => 1) measurable_const
    (A.indicator (fun _ => 1)) (measurable_const.indicator hA)
  simp only [one_mul] at hmarkov
  have hpre : MeasurableSet {e : Excursion | futureFrom s e ∈ A} :=
    (measurable_futureFrom s) hA
  have hleft : (∫⁻ e in {e : Excursion | s < e.lifetime},
      A.indicator (fun _ => 1) (futureFrom s e) ∂excursionMeasure θ) =
      (excursionMeasure θ).restrict {e : Excursion | s < e.lifetime}
        {e | futureFrom s e ∈ A} := by
    change (∫⁻ e in {e : Excursion | s < e.lifetime},
      {e : Excursion | futureFrom s e ∈ A}.indicator (fun _ => 1) e
        ∂excursionMeasure θ) = _
    exact lintegral_indicator_one hpre
  rw [hleft] at hmarkov
  calc
    _ ≤ (excursionMeasure θ).restrict {e : Excursion | s < e.lifetime}
        {e | futureFrom s e ∈ A} := by
      rw [Measure.restrict_apply hmargin, Measure.restrict_apply hpre]
      apply measure_mono_ae
      filter_upwards [ae_excursionMeasure_support hθ] with e he
      rintro ⟨hdepth, htime⟩
      have hi : futureInf e.path (s + r) s ≤ futureInf (futureFrom s e) r 0 := by
        let : Nonempty (Icc (min (0 : ℝ≥0) r) r) := ⟨⟨r, min_le_right _ _, le_rfl⟩⟩
        unfold futureInf
        apply le_ciInf
        intro u
        rw [futureFrom_apply]
        exact futureInf_le_eval e.path (s + r) s (s + u)
          ⟨by simp, add_le_add le_rfl u.2.2⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [futureFrom_apply]
        exact he.1 (s + r) (by positivity) htime
      · rw [futureFrom_apply, add_zero]
        exact hdepth.trans_le (add_le_add hi le_rfl)
      · exact (lt_add_of_pos_right s hr).trans htime
    _ = ∫⁻ e in {e : Excursion | s < e.lifetime},
        killedStableKernel θ (e.valueNN s) A ∂excursionMeasure θ :=
      hmarkov.trans (lintegral_congr fun _ => lintegral_indicator_one hA)
    _ ≤ ∫⁻ _e in {e : Excursion | s < e.lifetime},
        ENNReal.ofReal (C * ε * (r : ℝ) ^ (-1 / θ)) ∂excursionMeasure θ :=
      lintegral_mono fun e => hbound r (e.valueNN s) ε hr hε
    _ = _ := by simp [lintegral_const, mul_comm]

end BGW.StableTrees
