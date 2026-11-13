/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.PathTailCoding
public import BGW.StableTrees.PathTailLimitMeasurable
import BGW.StableTrees.PathTailMeasurable
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Identifying discrete and limiting cut-path laws

K02 identifies the selected closed block with the tail-conditioned tree law. The limiting cut
is the first long mark, whose law is the independent tail excursion law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal Classical
open BGW.Skorokhod BGW.Probability.RealWalk
open BGW.StableTrees.DiscreteForest (tailTreeLaw)

namespace BGW.StableTrees.PathTail

/-- The path coordinate of the selected-block triple is the closed path of a tail-conditioned
BGW tree, by the exact K02/K04 coding adapter. -/
theorem map_selectedBlockCut_eq_closedTail {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (n : ℕ) (T : ℝ≥0) :
    (iidLaw (realOffspringStepLaw μ)).map (fun ω => (extractionTriple (B n) n T ω).2.2) =
      (tailTreeLaw μ n).map (fun τ =>
        realStepPath (T : ℝ) n (B n) (closedTreeIncrementSeq τ)) := by
  have hr : Measurable (fun ω : ℕ → ℕ => fun i => ((ω i : ℤ) - 1 : ℝ)) := by
    fun_prop
  have hc : Measurable (fun ω : ℕ → ℝ => (extractionTriple (B n) n T ω).2.2) :=
    (measurable_extractionTriple _ _ _).snd.snd
  have htree := congrArg ProbabilityMeasure.toMeasure
    (DiscreteForest.firstLongTree_law μ h.critical h.nondegenerate n)
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map _ (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)) =
    Measure.map _ (tailTreeLaw μ n : Measure BGW.LocallyFinite.Tree)
  rw [← DiscreteForest.map_offspringSeqLaw_realIncrements μ,
    Measure.map_map hc hr, ← htree]
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (measurable_closedTreePrefixPath B n T)
      (DiscreteForest.measurable_firstLongTree n)]
  apply Measure.map_congr
  filter_upwards [DiscreteForest.ae_ladderFinite μ h.critical h.nondegenerate] with ω hω
  change realStepPath (T : ℝ) n (B n)
      (blockIncrements (realForestIncrements ω)
        (firstLongIndex n (realForestIncrements ω))) =
    realStepPath (T : ℝ) n (B n) (closedTreeIncrementSeq (DiscreteForest.firstLongTree n ω))
  rw [closedTreeIncrementSeq_firstLongTree hω]

/-- Projecting the limiting endpoint/cut triple gives the sealed tail excursion path law. -/
theorem map_longCutTriple_path {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) :
    ((stableLocalLaw θ).map (longCutTriple T)).map
        (fun p : ℝ × ℝ × D (T : ℝ) ℝ => p.2.2) = tailLevyExcLaw θ T := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map _ (Measure.map _ (stableLocalLaw θ : Measure DLoc)) =
    Measure.map (excursionRestrict T) (tailExcursionLaw θ : Measure Excursion)
  rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (aemeasurable_longCutTriple hθ T),
    ← map_firstLongMark hθ,
    AEMeasurable.map_map_of_aemeasurable (measurable_excursionRestrict T).aemeasurable
      (aemeasurable_firstLongMark hθ)]
  rfl

end BGW.StableTrees.PathTail
