/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.TailPairExtraction
public import BGW.StableTrees.HeightTightness
import BGW.StableTrees.PathTailGoodEvent
public import BGW.StableTrees.PathTailRepresentation
public import BGW.StableTrees.PathTailReconstruction
import BGW.Skorokhod.PolishTightness
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Full-sequence coupling for localized long-block extraction

The compact-horizon FCLT is represented along the entire sequence. Graph disintegration lifts
the limit to the local stable law. Reconstructed mesh increments then satisfy the long-block
extraction convergence on the first-long-mark good event, with no subsequence change of the
mesh index.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal Classical
open BGW.Skorokhod BGW.Probability.RealWalk
open BGW.Probability

namespace BGW.StableTrees.TailPair

open BGW.StableTrees.PathTail BGW.StableTrees.DiscreteForest

/-- A full-sequence compact-path coupling with a local stable limit, reconstructed skip-free
increments, and long-block extraction convergence on the event that the limiting end precedes
`M`. -/
theorem exists_localized_pair_coupling {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (M T : ℝ≥0) (hM : 0 < M) (hT : 0 < T) :
    ∃ (η : ProbabilityMeasure (unitInterval × DLoc))
      (Y : ℕ → unitInterval × DLoc → D (M : ℝ) ℝ × C(Icc (0 : ℝ) (M : ℝ), ℝ)),
      (∀ n, Measurable (Y n)) ∧
      (∀ n, (η : Measure (unitInterval × DLoc)).map (Y n) =
        ((offspringSeqLaw μ).map (forestPairPath B n M) :
          Measure (D (M : ℝ) ℝ × C(Icc (0 : ℝ) (M : ℝ), ℝ)))) ∧
      (η : Measure (unitInterval × DLoc)).map Prod.snd = (stableLocalLaw θ : Measure DLoc) ∧
      ∀ᵐ p ∂(η : Measure (unitInterval × DLoc)),
        Tendsto (fun n => Y n p) atTop
          (𝓝 (DLoc.restrict M p.2, heightPrefix θ M (DLoc.restrict M p.2))) ∧
        (∀ n i, IsSkipFreeIncrement (reconstructIncrements M n (B n) (Y n p).1 i)) ∧
        (passageTime (firstLongLabel p.2) p.2 < M →
          Tendsto (fun n => extractionTriple (B n) n T
            (reconstructIncrements M n (B n) (Y n p).1)) atTop (𝓝 (longCutTriple T p.2)) ∧
          ∀ᶠ n in atTop,
            BGW.StableTrees.firstLongIndex n (reconstructIncrements M n (B n) (Y n p).1) ∈
              longBlockSet n (reconstructIncrements M n (B n) (Y n p).1) ∧
            BGW.StableTrees.ladderTime (reconstructIncrements M n (B n) (Y n p).1)
              (BGW.StableTrees.firstLongIndex n (reconstructIncrements M n (B n) (Y n p).1) + 1) ≤
                ⌊(n : ℝ) * M⌋₊) := by
  let graph (f : DLoc) := (DLoc.restrict M f,
    heightPrefix θ M (DLoc.restrict M f))
  have hm : Measurable graph := (DLoc.measurable_restrict M).prodMk
    ((measurable_heightPrefix θ M).comp (DLoc.measurable_restrict M))
  obtain ⟨η, Y, hYm, hYlaw, hFlaw, hconv⟩ := exists_representation_with_lift
    (fun n => (offspringSeqLaw μ).map (forestPairPath B n M)) (stableLocalLaw θ)
    graph hm (HeightTightness.tendsto_forestPairLaw h hM)
  have hsupport : ∀ᵐ p ∂(η : Measure (unitInterval × DLoc)), ∀ n,
      realStepPath (M : ℝ) n (B n) (reconstructIncrements M n (B n) (Y n p).1) =
          (Y n p).1 ∧
        ∀ i, IsSkipFreeIncrement (reconstructIncrements M n (B n) (Y n p).1 i) := by
    apply ae_all_iff.mpr
    intro n
    have hb : n ≠ 0 → B n ≠ 0 := fun hn => (h.pos n (by omega)).ne'
    have hs := ae_reconstructIncrements μ M n (B n) hb
    have hwlaw : (η : Measure (unitInterval × DLoc)).map (fun p => (Y n p).1) =
        (stepPathLaw (realOffspringStepLaw μ) M B n : Measure (D (M : ℝ) ℝ)) := by
      change Measure.map (Prod.fst ∘ Y n) _ = _
      rw [← Measure.map_map measurable_fst (hYm n), hYlaw n]
      exact forestPairLaw_fst μ B n M
    change ∀ᵐ y ∂(stepPathLaw (realOffspringStepLaw μ) M B n : Measure (D (M : ℝ) ℝ)),
      realStepPath (M : ℝ) n (B n) (reconstructIncrements M n (B n) y) = y ∧
        ∀ i, IsSkipFreeIncrement (reconstructIncrements M n (B n) y i) at hs
    rw [← hwlaw] at hs
    exact ae_of_ae_map (hYm n).fst.aemeasurable hs
  have hgood : ∀ᵐ p ∂(η : Measure (unitInterval × DLoc)),
      passageTime (firstLongLabel p.2) p.2 < M → GoodLongExtractionCutPath M T p.2 := by
    have hg := ae_goodLongExtractionCutPath h.alpha_mem M T hT
    rw [← hFlaw] at hg
    exact ae_of_ae_map measurable_snd.aemeasurable hg
  refine ⟨η, Y, hYm, hYlaw, hFlaw, ?_⟩
  filter_upwards [hconv, hsupport, hgood] with p hp hs hg
  have hskip : ∀ n i, IsSkipFreeIncrement (reconstructIncrements M n (B n) (Y n p).1 i) :=
    fun n => (hs n).2
  refine ⟨hp, hskip, fun hend => ?_⟩
  have hpath : Tendsto (fun n => realStepPath (M : ℝ) n (B n)
      (reconstructIncrements M n (B n) (Y n p).1)) atTop (𝓝 (DLoc.restrict M p.2)) := by
    simpa only [fun n => (hs n).1] using hp.fst_nhds
  have hB := h.isRealStableAttracted.tendsto_norming_atTop
  have hcut := tendsto_firstLongBlock_cut hB _ hskip (hg hend) hpath
  have hends := tendsto_firstLongBlock_endpoints hB _ hskip (hg hend).1 hpath
  have hnonempty := eventually_longBlockSet_nonempty hB _ hskip (hg hend).1 hpath
  refine ⟨hcut, ?_⟩
  have hupper := hends.snd_nhds.eventually_lt_const
    (show (firstLongEnds p.2).2 < (M : ℝ) from hend)
  filter_upwards [hnonempty, hupper, eventually_gt_atTop 0] with n hn hu hnpos
  refine ⟨Nat.sInf_mem hn, ?_⟩
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have ht : (BGW.StableTrees.ladderTime (reconstructIncrements M n (B n) (Y n p).1)
      (BGW.StableTrees.firstLongIndex n (reconstructIncrements M n (B n) (Y n p).1) + 1) : ℝ) ≤
        (n : ℝ) * M := by
    change _ / (n : ℝ) < (M : ℝ) at hu
    have hh := (div_lt_iff₀ hnreal).mp hu
    nlinarith
  exact Nat.le_floor ht

end BGW.StableTrees.TailPair
