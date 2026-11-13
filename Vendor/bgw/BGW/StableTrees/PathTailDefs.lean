/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtraction
public import BGW.StableTrees.FirstLongMark
public import BGW.StableTrees.StableLocalLaw
public import BGW.StableTrees.UnitExcursionLaw
public import BGW.StableTrees.WalkPathTightness
public import BGW.StableTrees.RealAttraction
public import BGW.StableTrees.Attraction.Defs
public import BGW.ContinuumTrees.ExcursionCarrier
public import BGW.Skorokhod.ExitPartition
public import BGW.Skorokhod.MeasurableMaps
public import BGW.LocallyFinite.SizeConditioning
public import BGW.Tree.Decode
public import BGW.StableTrees.DiscreteForest

/-!
# Tail-conditioned tree walk paths

Tree path carriers and their terminal-step comparison for first-long-block extraction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest (tailTreeLaw)

namespace BGW.StableTrees.PathTail

open BGW BGW.Skorokhod BGW.Probability.RealWalk BGW.StableTrees

/-! ## 1. Shared carriers (K05b owns the path carriers; K02 copies are marked) -/

/-- The DFS increments `(d_i - 1)` of a finite tree (empty list for infinite trees). -/
noncomputable def treeIncrements (τ : BGW.LocallyFinite.Tree) : List ℤ :=
  if h : BGW.LocallyFinite.FiniteVertices τ then
    (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).increments
  else []

private theorem treeIncrements_toLocallyFinite (t : PlaneTree) :
    treeIncrements t.toLocallyFinite = t.increments := by
  rw [treeIncrements, dite_eq_left t.finiteVertices_toLocallyFinite]
  change (PlaneTree.equivFiniteVertices.symm (PlaneTree.equivFiniteVertices t)).increments = _
  rw [Equiv.symm_apply_apply]

/-- The discrete σ-algebra on integer words, used locally for countable sums. -/
local instance instMeasurableSpaceListInt : MeasurableSpace (List ℤ) := ⊤
local instance : MeasurableSingletonClass (List ℤ) := ⟨fun _ => trivial⟩

private theorem measurable_treeIncrements : Measurable treeIncrements := by
  apply measurable_to_countable'
  intro a
  have heq : treeIncrements ⁻¹' {a} =
      PlaneTree.toLocallyFinite '' {t | t.increments = a} ∪
        if a = [] then {τ | BGW.LocallyFinite.FiniteVertices τ}ᶜ else ∅ := by
    ext τ
    by_cases hτ : BGW.LocallyFinite.FiniteVertices τ
    · obtain ⟨t, rfl⟩ := (BGW.LocallyFinite.exists_toLocallyFinite_iff τ).mpr hτ
      simp [treeIncrements_toLocallyFinite, t.finiteVertices_toLocallyFinite,
        PlaneTree.toLocallyFinite_injective.eq_iff]
    · have himage : τ ∉ PlaneTree.toLocallyFinite '' {t | t.increments = a} := by
        rintro ⟨t, _, rfl⟩
        exact hτ t.finiteVertices_toLocallyFinite
      simp only [mem_preimage, mem_singleton_iff, treeIncrements, dite_eq_right hτ,
        mem_union, himage, false_or]
      by_cases ha : a = [] <;> simp [ha, hτ]
  rw [heq]
  apply ((Set.to_countable _).image _).measurableSet.union
  split_ifs
  · exact BGW.LocallyFinite.measurableSet_finiteVertices.compl
  · exact MeasurableSet.empty

/-- The increments of a tree as a real sequence, extended by `0` after the end of the tree. -/
noncomputable def treeIncrementSeq (τ : BGW.LocallyFinite.Tree) : ℕ → ℝ :=
  fun i => ((treeIncrements τ).getD i 0 : ℤ)

private theorem measurable_treeIncrementSeq : Measurable treeIncrementSeq := by
  apply Measurable.of_eval
  intro i
  exact (measurable_of_countable (fun a : List ℤ => (a.getD i 0 : ℝ))).comp
    measurable_treeIncrements

/-- The path `t ↦ W_{⌊n t⌋}/B n` of a tree on `[0,T]`, with the sample size `n` (not the
size of the tree) as time scale. -/
noncomputable def treePrefixPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0)
    (τ : BGW.LocallyFinite.Tree) :
    D (T : ℝ) ℝ :=
  realStepPath (T : ℝ) n (B n) (treeIncrementSeq τ)

/-- The prefix-path map is measurable. -/
theorem measurable_treePrefixPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (treePrefixPath B n T) := by
  exact (measurable_realStepPath (T : ℝ) n (B n)).comp measurable_treeIncrementSeq

/-- The tail walk law on `[0,a]`: the path of a BGW tree conditioned on size `≥ n`. -/
noncomputable def tailWalkPrefixLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) :
    ProbabilityMeasure (D (a : ℝ) ℝ) :=
  ProbabilityMeasure.map (tailTreeLaw μ n) (treePrefixPath B n a)

/-- The prefix on `[0,a]` of the excursion under `N(· | ζ > 1)` (limit of the tail walk). -/
noncomputable def tailPrefixLimit (θ : ℝ) (a : ℝ≥0) : ProbabilityMeasure (D (a : ℝ) ℝ) :=
  (tailExcursionLaw θ).map (excursionRestrict a)

/-- The tail walk law on `[0,T]` for all horizons. -/
noncomputable def tailWalkLaw (μ : PMF ℕ) (B : ℕ → ℝ)
    (n : ℕ) (T : ℝ≥0) : ProbabilityMeasure (D (T : ℝ) ℝ) :=
  (tailTreeLaw μ n).map (treePrefixPath B n T)

/-- The tail walk prefix law is the tail walk law (same map). -/
theorem tailWalkPrefixLaw_eq_tailWalkLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) :
    tailWalkPrefixLaw μ B n a = tailWalkLaw μ B n a := rfl

/-- The tail prefix limit is the sealed `tailLevyExcLaw` (same map). -/
theorem tailPrefixLimit_eq_tailLevyExcLaw (θ : ℝ) (a : ℝ≥0) :
    tailPrefixLimit θ a = tailLevyExcLaw θ a := rfl

/-! ## 2. Terminal convention: closed tree increments -/

/-- The tree increments with the terminal `-1` step replaced by `0` (the K04 `blockIncrements`
convention); `0` after the end of the tree. -/
noncomputable def closedTreeIncrementSeq (τ : BGW.LocallyFinite.Tree) : ℕ → ℝ :=
  fun i => if i + 1 < (treeIncrements τ).length then treeIncrementSeq τ i else 0


/-- The closed tree-path map is measurable. -/
theorem measurable_closedTreePrefixPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (fun τ => realStepPath (T : ℝ) n (B n) (closedTreeIncrementSeq τ)) := by
  apply (measurable_realStepPath (T : ℝ) n (B n)).comp
  apply Measurable.of_eval
  intro i
  have hm : Measurable (fun a : List ℤ =>
      if i + 1 < a.length then (a.getD i 0 : ℝ) else 0) := measurable_of_countable _
  exact hm.comp measurable_treeIncrements

end BGW.StableTrees.PathTail
