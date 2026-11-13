/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarkedExcursionsBasic

/-!
# Support and lifetime of marked excursions

The simultaneous support theorem identifies the marked cuts with the reflected path.

(J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.)
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Lifetime identity and cut validity** (a.s., all jump levels at once; uses the excursion
support theorem): the cut of `(T_{x-}, T_x)` is valid, its tag is the true lifetime `T_x -
T_{x-}`, and its path is the reflected path run from `T_{x-}` and stopped at `T_x`. -/
theorem ae_jumpExcursion_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      cutValid (passageTimeMinus x f) (passageTime x f) f ∧
        (jumpExcursion x f).lifetime = passageTime x f - passageTimeMinus x f ∧
        ∀ t : ℝ≥0, (jumpExcursion x f).path.1 t =
          (reflectedFrom 0 f).1 (min (passageTimeMinus x f + t) (passageTime x f))  := by
  filter_upwards [ae_continuousAt_jumpStart hθ, ae_creeping_passageTime hθ,
    ae_localTime_passageTime hθ, ae_eval_zero_stableLocalLaw hθ] with f hs hd hL h0
  intro x hx
  have hI (t : ℝ≥0) (hgt : passageTimeMinus x f ≤ t) (htd : t ≤ passageTime x f) :
      runningInfLoc f t = -(x : ℝ) := by
    have hg := (hL x).2
    have hd := (hL x).1
    have hlow := runningInfLoc_antitone f htd
    have hupp := runningInfLoc_antitone f hgt
    dsimp [localTime] at hg hd
    linarith
  have hc : cutValid (passageTimeMinus x f) (passageTime x f) f := by
    refine ⟨hx.2, (hd x).trans (hs x hx).2.1.symm, ?_⟩
    intro t hgt htd
    rw [(hs x hx).2.1, ← hI t hgt htd]
    exact runningInfLoc_le_eval f t ⟨t, le_rfl⟩
  refine ⟨hc, excursionCut_lifetime hc, ?_⟩
  intro t
  rw [jumpExcursion, excursionCut_eval hc, reflectedFrom_zero_apply h0,
    (hs x hx).2.1, hI _ (le_min (by simp) hx.2.le) (min_le_right _ _)]

/-- **Support properties of the excursions**: a.s., for every jump level `x`, the excursion is
positive on `(0, ζ)`, its tag is the actual lifetime `sup {t | 0 < e t}`, it starts at `0` with the
reflected path continuous at `T_{x-}` (no jump start), and its left limit at `ζ` is `0`. -/
theorem ae_jumpExcursion_support {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      (∀ t : ℝ≥0, 0 < t → t < (jumpExcursion x f).lifetime → 0 < (jumpExcursion x f).path.1 t) ∧
        (jumpExcursion x f).lifetime = sSup {t : ℝ≥0 | 0 < (jumpExcursion x f).path.1 t} ∧
        (jumpExcursion x f).path.1 0 = 0 ∧
        ContinuousAt (reflectedFrom 0 f).1 (passageTimeMinus x f) ∧
        Tendsto (jumpExcursion x f).path.1 (𝓝[<] (jumpExcursion x f).lifetime) (𝓝 0)  := by
  filter_upwards [ae_jumpExcursion_spec hθ, ae_isExcursionInterval_of_jump hθ,
    ae_continuousAt_jumpStart hθ, ae_leftLim_le_stableLocalLaw hθ] with f hs hi hc hn
  intro x hx
  obtain ⟨hvalid, hlife, heval⟩ := hs x hx
  have hpos (t : ℝ≥0) (ht : 0 < t) (htl : t < (jumpExcursion x f).lifetime) :
      0 < (jumpExcursion x f).path.1 t := by
    have htd : passageTimeMinus x f + t < passageTime x f := by
      rw [hlife] at htl
      exact (lt_tsub_iff_left_of_le hx.2.le).mp htl
    rw [heval t, min_eq_left htd.le]
    exact (hi x hx).2.1 _ (lt_add_of_pos_right _ ht) htd
  refine ⟨hpos, ?_, ?_, ?_, ?_⟩
  · have hset : {t : ℝ≥0 | 0 < (jumpExcursion x f).path.1 t} =
        Ioo 0 (jumpExcursion x f).lifetime := by
      ext t
      change (0 < (jumpExcursion x f).path.1 t) ↔ _
      constructor
      · intro ht
        have ht0 : 0 < t := by
          by_contra h
          have ht' : t = 0 := le_antisymm (le_of_not_gt h) (show 0 ≤ t from t.2)
          have hz : (jumpExcursion x f).path.1 0 = 0 := (jumpExcursion x f).2.1
          rw [ht', hz] at ht
          exact lt_irrefl 0 ht
        refine ⟨ht0, ?_⟩
        by_contra h
        have hz : (jumpExcursion x f).path.1 t = 0 :=
          (jumpExcursion x f).2.2.2 t (le_of_not_gt h)
        rw [hz] at ht
        exact lt_irrefl 0 ht
      · exact fun ht => hpos t ht.1 ht.2
    rw [hset, csSup_Ioo (Excursion.lifetime_pos _)]
  · exact (jumpExcursion x f).2.1
  · have hstart := (hc x hx).1
    have hI : ContinuousAt (runningInfLoc f) (passageTimeMinus x f) :=
      (runningInfLoc_continuous hn).continuousAt
    have hmin : ContinuousAt (fun t => min (0 : ℝ) (runningInfLoc f t))
        (passageTimeMinus x f) := continuousAt_const.min hI
    simpa only [reflectedFrom, NNReal.coe_zero, zero_add, Pi.sub_def] using hstart.sub hmin
  · have hd0 := (hi x hx).2.2.2.2
    have hlim := (reflectedFrom 0 f).2.tendsto_nhdsLT_leftLim (passageTime x f)
    rw [leftLim_reflectedFrom_eq_zero_of_noNegJumps hn hd0] at hlim
    have hmap : Tendsto (fun t : ℝ≥0 => passageTimeMinus x f + t)
        (𝓝[<] (jumpExcursion x f).lifetime) (𝓝[<] (passageTime x f)) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have hcont : Continuous (fun t : ℝ≥0 => passageTimeMinus x f + t) :=
          continuous_const.add continuous_id
        have heq : passageTimeMinus x f + (jumpExcursion x f).lifetime =
            passageTime x f := by rw [hlife, add_tsub_cancel_of_le hx.2.le]
        rw [← heq]
        exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        change passageTimeMinus x f + t < passageTime x f
        rw [hlife] at ht
        exact (lt_tsub_iff_left_of_le hx.2.le).mp ht
    apply (hlim.comp hmap).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hlife] at ht
    rw [heval t, min_eq_left ((lt_tsub_iff_left_of_le hx.2.le).mp ht).le]
    rfl

end BGW.StableTrees
