/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactPrefixWeights
public import BGW.StableTrees.PathTail

/-!
# Exact-size tree prefixes and their path encoding

The finite tree correspondence identifies the vector path with the tree prefix on the
same sample-size time scale.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteBridge (offspringVec exactWalkLaw restrictLaw endValue)
open BGW.StableTrees.DiscreteForest (exactTreeLaw tailTreeLaw)
open BGW.StableTrees.PathTail (treeIncrements treeIncrementSeq treePrefixPath
  measurable_treePrefixPath tailWalkPrefixLaw tailPrefixLimit)

namespace BGW.StableTrees.ExactPrefix

open BGW BGW.Skorokhod BGW.Probability.RealWalk

/-- The shared offspring-vector measure is a probability measure. -/
instance (μ : PMF ℕ) (n : ℕ) : IsProbabilityMeasure (offspringVec μ n) := by
  unfold offspringVec
  infer_instance

/-- Partial sums of a padded integer list. -/
theorem sum_range_getD (l : List ℤ) (k : ℕ) :
    (∑ i ∈ Finset.range k, (l.getD i 0 : ℝ)) = ((l.take k).sum : ℝ) := by
  induction l generalizing k with
  | nil => simp
  | cons z l ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [Finset.sum_range_succ']
      simpa [add_comm] using congrArg (fun r : ℝ => r + z) (ih k)

/-- The tree increments of a finite tree are its plane-tree increments. -/
theorem treeIncrements_toLocallyFinite (t : PlaneTree) :
    treeIncrements t.toLocallyFinite = t.increments := by
  simp only [treeIncrements, dite_eq_left t.finiteVertices_toLocallyFinite]
  change (PlaneTree.equivFiniteVertices.symm (PlaneTree.equivFiniteVertices t)).increments = _
  rw [Equiv.symm_apply_apply]

/-- The law of the exact-size walk path on `[0,a]`. -/
noncomputable abbrev exactWalkPrefixLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (hn : Admissible μ n)
    (a : ℝ≥0) (ha : a ≤ 1) : ProbabilityMeasure (D (a : ℝ) ℝ) :=
  restrictLaw a ha (exactWalkLaw μ B n hn)

/-- The exact-size walk prefix is the prefix path of the exact-size BGW tree: one object. -/
theorem exactWalkPrefixLaw_eq_map_exactTreeLaw {μ : PMF ℕ} {B : ℕ → ℝ} {n : ℕ}
    (hn : Admissible μ n) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ((exactWalkPrefixLaw μ B n hn a ha.2.le : ProbabilityMeasure (D (a : ℝ) ℝ)) :
        Measure (D (a : ℝ) ℝ)) =
      ((exactTreeLaw μ n : ProbabilityMeasure BGW.LocallyFinite.Tree) :
        Measure BGW.LocallyFinite.Tree).map (treePrefixPath B n a) := by
  have hsize : ∀ᵐ τ ∂(exactTreeLaw μ n : Measure LocallyFinite.Tree),
      τ ∈ LocallyFinite.sizeEvent n := by
    rw [DiscreteForest.exactTreeLaw_toMeasure μ n hn]
    exact ae_cond_mem (LocallyFinite.measurableSet_sizeEvent n)
  change (exactWalkLaw μ B n hn : Measure (D 1 ℝ)).map
    (BGW.Skorokhod.restrict (show (a : ℝ) ≤ 1 by exact_mod_cast ha.2.le)) = _
  rw [← DiscreteBridge.map_treePath_exactTreeLaw hn,
    Measure.map_map (measurable_restrict _) (DiscreteBridge.measurable_treePath B n)]
  apply Measure.map_congr
  filter_upwards [hsize] with τ hτ
  obtain ⟨t, rfl⟩ := (LocallyFinite.exists_toLocallyFinite_iff τ).mpr hτ.1
  have ht : t.size = n := (LocallyFinite.toLocallyFinite_mem_sizeEvent_iff t n).mp hτ
  dsimp only [Function.comp_apply]
  rw [DiscreteBridge.treePath_toLocallyFinite]
  apply BGW.Skorokhod.ext
  intro u
  have hi := treeIncrements_toLocallyFinite t
  change (((t.increments.take ⌊(t.increments.length : ℝ) * (u : ℝ)⌋₊).sum : ℝ) / B n) =
    partialSum (treeIncrementSeq t.toLocallyFinite) ⌊(n : ℝ) * (u : ℝ)⌋₊ / B n
  simp only [PlaneTree.length_increments, ht]
  congr 1
  rw [partialSum]
  simp only [treeIncrementSeq, hi]
  exact (sum_range_getD _ _).symm

end BGW.StableTrees.ExactPrefix
