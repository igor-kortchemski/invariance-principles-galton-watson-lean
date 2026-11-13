/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.TailPairExtraction
public import BGW.StableTrees.PathTailReconstruction
import BGW.StableTrees.PathTailLocalization
import BGW.StableTrees.PathTailMeasurable

/-!
# Reconstruction of the selected pair from a compact forest pair

The walk determines the selected endpoints and cut. The height uses those same endpoints in
the continuous host coordinate. No independent height or lifetime is introduced.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees BGW.Probability.RealWalk

namespace BGW.StableTrees.TailPair

open BGW.StableTrees.DiscreteForest BGW.StableTrees.PathTail

/-- The selected closed-walk and centered-height pair reconstructed from a compact forest pair. -/
noncomputable def extractedForestPair (M T : ℝ≥0) (b : ℝ) (n : ℕ)
    (z : D (M : ℝ) ℝ × C(Icc (0 : ℝ) (M : ℝ), ℝ)) :
    D (T : ℝ) ℝ × C(Icc (0 : ℝ) (T : ℝ), ℝ) :=
  let e := extractionTriple b n T (reconstructIncrements M n b z.1)
  (e.2.2, cutHeightPath M T z.2 e.1 e.2.1)

/-- Reconstructing the selected pair is measurable. -/
theorem measurable_extractedForestPair (M T : ℝ≥0) (b : ℝ) (n : ℕ) :
    Measurable (extractedForestPair M T b n) := by
  have he : Measurable (fun z : D (M : ℝ) ℝ × C(Icc (0 : ℝ) (M : ℝ), ℝ) =>
      extractionTriple b n T (reconstructIncrements M n b z.1)) :=
    (measurable_extractionTriple b n T).comp
    ((measurable_reconstructIncrements M n b).comp measurable_fst)
  exact he.snd.snd.prodMk ((continuous_cutHeightPath M T).measurable.comp
    (measurable_snd.prodMk (he.fst.prodMk he.snd.fst)))

/-- The observable event that the reconstructed selected block ends within the observed mesh. -/
def selectionLocalEvent (M : ℝ≥0) (b : ℝ) (n : ℕ) :
    Set (D (M : ℝ) ℝ × C(Icc (0 : ℝ) (M : ℝ), ℝ)) :=
  {z | BGW.StableTrees.firstLongIndex n (reconstructIncrements M n b z.1) ∈
      longBlockSet n (reconstructIncrements M n b z.1) ∧
    BGW.StableTrees.ladderTime (reconstructIncrements M n b z.1)
      (BGW.StableTrees.firstLongIndex n (reconstructIncrements M n b z.1) + 1) ≤
        ⌊(n : ℝ) * M⌋₊}

/-- The finite-mesh selection event is measurable. -/
theorem measurableSet_selectionLocalEvent (M : ℝ≥0) (b : ℝ) (n : ℕ) :
    MeasurableSet (selectionLocalEvent M b n) :=
  ((measurable_reconstructIncrements M n b).comp measurable_fst)
    (measurableSet_extractionLocalEvent ⌊(n : ℝ) * M⌋₊ n)

/-- The centered continuous cut of a forest block is exactly that block's tree height. -/
theorem cutHeightPath_forest_block (B : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (M T : ℝ≥0) {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ)
    (hdM : (DiscreteForest.ladderTime ω (r + 1) : ℝ) / n ≤ M) :
    cutHeightPath M T (forestHeightPath B n M ω)
      ((DiscreteForest.ladderTime ω r : ℝ) / n)
      ((DiscreteForest.ladderTime ω (r + 1) : ℝ) / n) =
        treeHeightPath B n T (blockLF ω r) := by
  let g := (DiscreteForest.ladderTime ω r : ℝ) / n
  let d := (DiscreteForest.ladderTime ω (r + 1) : ℝ) / n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hg : 0 ≤ g := div_nonneg (Nat.cast_nonneg _) hn'.le
  have hgd : g ≤ d := div_le_div_of_nonneg_right
    (by exact_mod_cast (DiscreteForest.ladderTime_lt_succ hω r).le) hn'.le
  have hz : forestHeight ω (DiscreteForest.ladderTime ω (r + 1)) = 0 := by
    have hh := ForestContour.forestHeight_ladderTime_add hω (r + 1)
      (i := 0) (Nat.zero_le _)
    have hroot := PlaneTree.heightSeq_le (blockTree ω (r + 1)) 0
    simp only [Nat.add_zero] at hh
    omega
  have hnd : (n : ℝ) * d = DiscreteForest.ladderTime ω (r + 1) := by
    dsimp [d]
    field_simp
  have hd : forestHeightPath B n M ω ⟨d, hg.trans hgd, hdM⟩ = 0 := by
    change B n / n * forestHeightLin ω ((n : ℝ) * d) = 0
    rw [hnd]
    simp [forestHeightLin, hz]
  apply ContinuousMap.ext
  intro t
  rw [cutHeightPath_eq_extractedHeight M T _ hg hgd hdM hd,
    treeHeightPath_blockLF B hn T hω r t]
  unfold extractedHeight
  split_ifs with ht
  · have hm : g + t ∈ Icc (0 : ℝ) (M : ℝ) :=
      ⟨by linarith [t.property.1], by linarith⟩
    have hp : (projIcc 0 (M : ℝ) M.2 (g + t) : ℝ) = g + t :=
      congrArg Subtype.val (projIcc_of_mem M.2 hm)
    change B n / n * forestHeightLin ω ((n : ℝ) *
      (projIcc 0 (M : ℝ) M.2 (g + t) : ℝ)) = _
    rw [hp]
  · rfl

/-- On a finite ladder forest whose reconstructed selection ends in the window, reconstruction
recovers the pair of its first long tree, with the walk closed at its terminal step. -/
theorem extractedForestPair_forestPairPath (B : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (hb : B n ≠ 0) (M T : ℝ≥0) {ω : ℕ → ℕ} (hω : LadderFinite ω)
    (hE : forestPairPath B n M ω ∈ selectionLocalEvent M (B n) n) :
    extractedForestPair M T (B n) n (forestPairPath B n M ω) =
      (realStepPath (T : ℝ) n (B n) (closedTreeIncrementSeq (firstLongTree n ω)),
        treeHeightPath B n T (firstLongTree n ω)) := by
  let ξ := reconstructIncrements M n (B n) (forestWalkPath B n M ω)
  have hp : ∀ i < ⌊(n : ℝ) * M⌋₊, ξ i = realForestIncrements ω i :=
    fun i hi => reconstructIncrements_stepPath hn hb (realForestIncrements ω) hi
  have he := extractionTriple_eq_of_prefix hp hE.1 hE.2 (B n) T
  have hdM : (extractionTriple (B n) n T (realForestIncrements ω)).2.1 ≤ M := by
    rw [he]
    change (BGW.StableTrees.ladderTime ξ (BGW.StableTrees.firstLongIndex n ξ + 1) : ℝ) / n ≤ M
    apply (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mpr
    have hh : (BGW.StableTrees.ladderTime ξ
        (BGW.StableTrees.firstLongIndex n ξ + 1) : ℝ) ≤ ⌊(n : ℝ) * M⌋₊ := by
      exact_mod_cast hE.2
    exact hh.trans (by simpa [mul_comm] using Nat.floor_le (by positivity : 0 ≤ (n : ℝ) * M))
  have hends : (extractionTriple (B n) n T (realForestIncrements ω)).1 =
      (DiscreteForest.ladderTime ω (DiscreteForest.firstLongIndex n ω) : ℝ) / n ∧
      (extractionTriple (B n) n T (realForestIncrements ω)).2.1 =
      (DiscreteForest.ladderTime ω (DiscreteForest.firstLongIndex n ω + 1) : ℝ) / n := by
    simp [extractionTriple, extractionEndpoints, PathTail.firstLongIndex_eq hω,
      PathTail.ladderTime_eq hω]
  change ((extractionTriple (B n) n T ξ).2.2,
    cutHeightPath M T (forestHeightPath B n M ω)
      (extractionTriple (B n) n T ξ).1 (extractionTriple (B n) n T ξ).2.1) = _
  rw [← he, hends.1, hends.2]
  apply Prod.ext
  · change realStepPath (T : ℝ) n (B n)
      (blockIncrements (realForestIncrements ω)
        (BGW.StableTrees.firstLongIndex n (realForestIncrements ω))) = _
    rw [closedTreeIncrementSeq_firstLongTree hω]
  · rw [hends.2] at hdM
    exact cutHeightPath_forest_block B hn M T hω _ hdM

end BGW.StableTrees.TailPair
