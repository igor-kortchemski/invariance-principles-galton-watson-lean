/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.TailPairCoupling
public import BGW.StableTrees.TailPairSelection

/-!
# Identification and convergence of the localized selected pair

The limit height is the common continuous host height cut at the first long excursion.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees BGW.Probability.RealWalk

namespace BGW.StableTrees.TailPair

open BGW.StableTrees.DiscreteForest BGW.StableTrees.PathTail

/-- At the first long mark the centered host-height cut is the excursion height. -/
theorem ae_cutHeightPath_firstLongMark {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (M T : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), (firstLongEnds f).2 ≤ M →
      cutHeightPath M T (heightPrefix θ M (DLoc.restrict M f))
        (firstLongEnds f).1 (firstLongEnds f).2 = (excursionPair θ T (firstLongMark f)).2 := by
  filter_upwards [ae_heightPrefix_restrict_all hθ, ae_excursionHeight_firstLongMark hθ,
    ae_heightLoc_passageEndpoints hθ, ae_firstLongLabel_mem hθ, ae_jumpExcursion_spec hθ]
      with f hp hl hz hm hs
  intro hdM
  have hg : 0 ≤ (firstLongEnds f).1 := (passageTimeMinus (firstLongLabel f) f).2
  have hgd : (firstLongEnds f).1 ≤ (firstLongEnds f).2 := by
    exact_mod_cast (hs (firstLongLabel f) hm.1).1.1.le
  have hd : heightPrefix θ M (DLoc.restrict M f)
      ⟨(firstLongEnds f).2, hg.trans hgd, hdM⟩ = 0 := by
    rw [hp]
    exact (hz (firstLongLabel f) hm.1).2
  apply ContinuousMap.ext
  intro t
  rw [cutHeightPath_eq_extractedHeight M T _ hg hgd hdM hd]
  change _ = excursionHeight θ (firstLongMark f) ⟨t, t.property.1⟩
  refine Eq.trans ?_ (hl ⟨t, t.property.1⟩).symm
  change extractedHeight
      (fun s => heightPrefix θ M (DLoc.restrict M f) (projIcc 0 (M : ℝ) M.2 s))
      (firstLongEnds f).1 (firstLongEnds f).2 (t : ℝ) =
    extractedHeight (fun s => heightLoc θ f s.toNNReal)
      (firstLongEnds f).1 (firstLongEnds f).2 (t : ℝ)
  by_cases ht : (t : ℝ) ≤ (firstLongEnds f).2 - (firstLongEnds f).1
  · simp only [extractedHeight, ite_eq_left ht]
    have hst : (firstLongEnds f).1 + (t : ℝ) ∈ Icc (0 : ℝ) (M : ℝ) :=
      ⟨by linarith [t.property.1], by linarith⟩
    calc
      _ = heightPrefix θ M (DLoc.restrict M f) ⟨_, hst⟩ :=
        congrArg _ (projIcc_of_mem M.2 hst)
      _ = heightLoc θ f ⟨_, hst.1⟩ := hp M ⟨_, hst⟩
      _ = _ := congrArg (heightLoc θ f)
        (Subtype.ext (Real.coe_toNNReal _ hst.1).symm)
  · simp only [extractedHeight, ite_eq_right ht]

end BGW.StableTrees.TailPair
