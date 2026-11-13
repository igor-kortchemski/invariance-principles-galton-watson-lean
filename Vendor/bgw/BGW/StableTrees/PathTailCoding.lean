/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.PathTailDefs

import Mathlib.Data.List.GetD

/-!
# The integer and real ladder-block coding adapter

Finite ladder times identify K02's equality hits and K04's weak real hits, their selected
indices, and the closed increments of the decoded first long tree.
-/

@[expose] public section

open MeasureTheory Set
open BGW BGW.Skorokhod BGW.Probability.RealWalk BGW.StableTrees
open scoped Classical NNReal

namespace BGW.StableTrees.PathTail

/-- Real offspring-minus-one increments, matching the sealed forest pushforward. -/
def realForestIncrements (ω : ℕ → ℕ) (i : ℕ) : ℝ := ((ω i : ℤ) - 1 : ℝ)

private theorem partialSum_realForestIncrements (ω : ℕ → ℕ) (k : ℕ) :
    partialSum (realForestIncrements ω) k = (DiscreteForest.walk ω k : ℝ) := by
  simp [partialSum, realForestIncrements, DiscreteForest.walk]

/-- The real walk's hitting time is the discrete ladder time on a finite ladder. -/
theorem hitTime_eq {ω : ℕ → ℕ} (hω : DiscreteForest.LadderFinite ω) (r : ℕ) :
    walkHitTime r (realForestIncrements ω) = (DiscreteForest.ladderTime ω r : ℕ∞) := by
  rw [walkHitTime, ← iInf_subtype'']
  apply ENat.iInf_eq_natCast_iff.mpr
  refine ⟨⟨⟨DiscreteForest.ladderTime ω r, ?_⟩, rfl⟩, ?_⟩
  · simp only [mem_ofPred_eq, partialSum_realForestIncrements, DiscreteForest.walk_ladderTime hω,
      Int.cast_neg, Int.cast_natCast, le_refl]
  · rintro ⟨k, hk⟩
    by_contra hn
    have hklt : k < DiscreteForest.ladderTime ω r := by
      exact_mod_cast (lt_of_not_ge hn)
    have hgt := DiscreteForest.walk_gt_of_lt_ladderTime hω hklt
    have hgt' : -(r : ℝ) < partialSum (realForestIncrements ω) k := by
      rw [partialSum_realForestIncrements]
      exact_mod_cast hgt
    exact hgt'.not_ge hk

/-- Real and discrete ladder times agree on a finite ladder. -/
theorem ladderTime_eq {ω : ℕ → ℕ} (hω : DiscreteForest.LadderFinite ω) (r : ℕ) :
    BGW.StableTrees.ladderTime (realForestIncrements ω) r = DiscreteForest.ladderTime ω r := by
  rw [BGW.StableTrees.ladderTime, hitTime_eq hω]
  simp

/-- Real and discrete first-long-block indices agree on a finite ladder. -/
theorem firstLongIndex_eq {ω : ℕ → ℕ} (hω : DiscreteForest.LadderFinite ω) (n : ℕ) :
    BGW.StableTrees.firstLongIndex n (realForestIncrements ω) =
      DiscreteForest.firstLongIndex n ω := by
  have heq : longBlockSet n (realForestIncrements ω) =
      {r | n ≤ DiscreteForest.ladderTime ω (r + 1) - DiscreteForest.ladderTime ω r} := by
    ext r
    simp [longBlockSet, hitTime_eq hω, ladderTime_eq hω]
  simp only [BGW.StableTrees.firstLongIndex, DiscreteForest.firstLongIndex, heq]

private theorem increments_blockLF {ω : ℕ → ℕ} (hω : DiscreteForest.LadderFinite ω) (r : ℕ) :
    treeIncrements (DiscreteForest.blockLF ω r) =
      (List.range (DiscreteForest.ladderTime ω (r + 1) - DiscreteForest.ladderTime ω r)).map
        (fun i => (ω (DiscreteForest.ladderTime ω r + i) : ℤ) - 1) := by
  have ht (t : PlaneTree) : treeIncrements t.toLocallyFinite = t.increments := by
    rw [treeIncrements, dite_eq_left t.finiteVertices_toLocallyFinite]
    change (PlaneTree.equivFiniteVertices.symm (PlaneTree.equivFiniteVertices t)).increments = _
    rw [Equiv.symm_apply_apply]
  rw [DiscreteForest.blockLF, ht, PlaneTree.increments, DiscreteForest.degrees_blockTree hω]
  simp only [DiscreteForest.blockDegrees, List.map_map, Function.comp_def]

/-- K02 first-long-tree closed increments agree exactly with K04 selected block increments. -/
theorem closedTreeIncrementSeq_firstLongTree {ω : ℕ → ℕ}
    (hω : DiscreteForest.LadderFinite ω) (n : ℕ) :
    closedTreeIncrementSeq (DiscreteForest.firstLongTree n ω) =
      blockIncrements (realForestIncrements ω)
        (BGW.StableTrees.firstLongIndex n (realForestIncrements ω)) := by
  funext i
  rw [DiscreteForest.firstLongTree, firstLongIndex_eq hω]
  simp only [closedTreeIncrementSeq, increments_blockLF hω, List.length_map, List.length_range,
    blockIncrements, ladderTime_eq hω]
  split_ifs with hi
  · rw [treeIncrementSeq, increments_blockLF hω,
      List.getD_eq_getElem _ _ (by simpa using (show i <
        DiscreteForest.ladderTime ω (DiscreteForest.firstLongIndex n ω + 1) -
          DiscreteForest.ladderTime ω (DiscreteForest.firstLongIndex n ω) by omega))]
    simp [realForestIncrements]
  · rfl

end BGW.StableTrees.PathTail
