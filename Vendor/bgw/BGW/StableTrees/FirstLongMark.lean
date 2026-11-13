/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.FirstLongMarkLaw
public import BGW.StableTrees.FirstLongMarkRegular

/-!
# The first long excursion under the stable law

Lifetime atomlessness, existence and measurability, the exponential/product law of the selected
label and mark, regular geometry at passage jumps, and the localized good-path suppliers.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

variable {θ : ℝ}

/-- **Finite end**: the selected end `T_L` is finite a.s. and `P(T_L < M) → 1` as `M → ∞`. -/
theorem tendsto_measure_firstLongEnd_lt (hθ : 1 < θ ∧ θ ≤ 2) :
    Tendsto (fun M : ℝ≥0 =>
      (stableLocalLaw θ : Measure DLoc) {f | passageTime (firstLongLabel f) f < M})
      atTop (𝓝 1) := by
  have hlim := tendsto_measure_iUnion_atTop (μ := (stableLocalLaw θ : Measure DLoc))
    (s := fun M : ℝ≥0 => {f | passageTime (firstLongLabel f) f < M})
    (fun a b hab f hf => hf.trans_le hab)
  have hfull : (stableLocalLaw θ : Measure DLoc)
      (⋃ M : ℝ≥0, {f | passageTime (firstLongLabel f) f < M}) = 1 := by
    rw [← measure_univ (μ := (stableLocalLaw θ : Measure DLoc))]
    apply measure_congr
    filter_upwards [ae_passageTime_eq_firstPassageBelow hθ] with f hf
    obtain ⟨t, ht⟩ : ∃ t : ℝ≥0,
        firstPassageBelow (firstLongLabel f) f = (t : WithTop ℝ≥0) :=
      ⟨_, hf.1 _⟩
    have heq : passageTime (firstLongLabel f) f = t :=
      WithTop.coe_injective ((hf.1 _).symm.trans ht)
    have hmem : f ∈ ⋃ M : ℝ≥0, {f | passageTime (firstLongLabel f) f < M} := by
      refine mem_iUnion.mpr ⟨t + 1, ?_⟩
      change passageTime (firstLongLabel f) f < t + 1
      rw [heq]
      exact lt_add_one t
    exact propext (iff_true_intro hmem)
  simpa only [Function.comp_def, hfull] using hlim

/-- **`ae_goodLongExtractionPath`, localized by `d < M`**: a.s., if the first long excursion
ends before `M`, the path is good on `[0, M]`. -/
theorem ae_goodLongExtractionPath (hθ : 1 < θ ∧ θ ≤ 2) (M : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      passageTime (firstLongLabel f) f < M → GoodLongExtractionPath M f := by
  filter_upwards [ae_eval_zero_stableLocalLaw hθ, ae_leftLim_le_stableLocalLaw hθ,
    ae_passageTime_eq_firstPassageBelow hθ, ae_creeping_passageTime hθ,
    ae_isRegularExcursionLevel hθ, ae_jump_lifetime_ne hθ 1,
    ae_exists_longLabel hθ] with f hzero hneg hT hcreep hregular hlife hlong
  intro hend
  exact {
    zero := hzero
    passageZero := hT.2
    noNegJumps := hneg
    infContinuous := runningInfLoc_continuous hneg
    finitePassage := hT.1
    creeping := hcreep
    strictMono := strictMono_passageTime_of_creeping hT.1 hcreep
    regular := hregular
    noLifetimeOne := hlife
    hasLongLabel := hlong
    end_lt := hend }

/-- The cut version, for every positive cutoff `T` (continuity of the selected cut at `T`). -/
theorem ae_goodLongExtractionCutPath (hθ : 1 < θ ∧ θ ≤ 2) (M T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      passageTime (firstLongLabel f) f < M → GoodLongExtractionCutPath M T f := by
  have hcont : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ContinuousAt (firstLongMark f).path.1 T := by
    have he := ae_continuousAt_tailExcursion_path hθ T hT
    rw [← map_firstLongMark hθ] at he
    exact ae_of_ae_map (f := firstLongMark) (aemeasurable_firstLongMark hθ) he
  filter_upwards [ae_goodLongExtractionPath hθ M, hcont] with f hf hc
  exact fun hend => ⟨hf hend, hc⟩

end BGW.StableTrees
