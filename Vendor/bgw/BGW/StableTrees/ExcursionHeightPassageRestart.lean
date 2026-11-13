/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightRestart
import BGW.StableTrees.StableStrongMarkov
import BGW.StableTrees.StableRegularity
import BGW.StableTrees.StableExcursionSupportPath

/-!
# Height zeros at fixed passage levels

Strong Markov at strict passage gives a fresh stable path. Regularity below zero empties the
old occupation, and continuous restart identifies the height at passage with the fresh zero.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The post-passage centered path has the full local stable law at each fixed level. -/
theorem map_shiftAt_firstPassageBelow {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc).map (DLoc.shiftAt (firstPassageBelow x)) =
      (stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  have hfin : ∀ᵐ f ∂P, (firstPassageBelow x f : ℝ≥0∞) < ⊤ := by
    filter_upwards [ae_passageTime_eq_firstPassageBelow hθ] with f hf
    rw [hf.1 x]
    exact ENNReal.coe_lt_top
  have hr : P.restrict {f | (firstPassageBelow x f : ℝ≥0∞) < ⊤} = P :=
    Measure.restrict_eq_self_of_ae_mem hfin
  have hm : P {f | (firstPassageBelow x f : ℝ≥0∞) < ⊤} = 1 := by
    have hh := congrArg (fun μ : Measure DLoc => μ univ) hr
    simpa only [Measure.restrict_apply_univ, measure_univ] using hh
  have hh := map_shiftAt_restrict_stableLocalLaw hθ (isStoppingTime_firstPassageBelow x)
  change (P.restrict {f | (firstPassageBelow x f : ℝ≥0∞) < ⊤}).map
    (DLoc.shiftAt (firstPassageBelow x)) =
      P {f | (firstPassageBelow x f : ℝ≥0∞) < ⊤} • P at hh
  rw [hr, hm, one_smul] at hh
  exact hh

/-- Regularity below zero implies a negative future infimum at every positive age. -/
theorem futureInf_neg_of_regularBelowAtZero {g : DLoc} (hg : DLoc.RegularBelowAtZero g)
    {u : ℝ≥0} (hu : 0 < u) : futureInf g u 0 < 0 := by
  obtain ⟨v, hv0, hvu, hv⟩ := hg u hu
  exact (futureInf_le_eval g u 0 v ⟨by simp, hvu.le⟩).trans_lt hv

/-- At every fixed passage level the continuous host height is zero almost surely. -/
theorem ae_heightLoc_passageTime_fixed {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), heightLoc θ f (passageTime x f) = 0 := by
  have hgood : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (∀ᵐ s : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
        heightLoc θ (DLoc.shiftAt (firstPassageBelow x) f) s.toNNReal =
          heightUniv θ (DLoc.shiftAt (firstPassageBelow x) f) s.toNNReal) ∧
        DLoc.RegularBelowAtZero (DLoc.shiftAt (firstPassageBelow x) f) := by
    apply ae_of_ae_map (μ := (stableLocalLaw θ : Measure DLoc))
      (p := fun g => (∀ᵐ s : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
        heightLoc θ g s.toNNReal = heightUniv θ g s.toNNReal) ∧ DLoc.RegularBelowAtZero g)
      (DLoc.measurable_shiftAt (isStoppingTime_firstPassageBelow x)).aemeasurable
    rw [map_shiftAt_firstPassageBelow hθ x]
    exact (ae_heightLoc_eq_heightUniv_ae hθ).and (ae_regularBelowAtZero_stableLocalLaw hθ)
  filter_upwards [ae_heightLoc_eq_heightUniv_ae hθ, hgood,
    ae_passageTime_eq_firstPassageBelow hθ, ae_creeping_passageTime hθ]
      with f hf hg hfin hcreep
  have hshift : DLoc.shiftAt (firstPassageBelow x) f = DLoc.shift (passageTime x f) f := by
    unfold DLoc.shiftAt
    rw [hfin.1 x]
    rfl
  rw [hshift] at hg
  apply heightLoc_zero_of_raw_restart θ f (passageTime x f) hf hg.1
  intro u hu
  apply heightUniv_eq_shift_of_past_min θ f (passageTime x f) u
  · intro s hs
    rcases hs.eq_or_lt with rfl | hs
    · exact le_rfl
    · rw [hcreep x]
      apply le_eval_of_lt_strictPassageBelow
      change (s : WithTop ℝ≥0) < firstPassageBelow x f
      rw [hfin.1 x]
      exact_mod_cast hs
  · exact futureInf_neg_of_regularBelowAtZero hg.2 hu

end BGW.StableTrees
