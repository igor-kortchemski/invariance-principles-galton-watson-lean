/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestMass
public import BGW.StableTrees.DiscreteForestCylinder
import BGW.StableTrees.CriticalSupport

/-!
# Conditioned tree laws and degree-prefix observables

Tree laws use the existing locally finite carrier. Null conditioning events
are totalized by a leaf, and finite DFS prefixes use the finite-tree equivalence.
Complete finite trees show that every size tail has positive mass in the critical
nondegenerate case.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical

namespace BGW.StableTrees.DiscreteForest

/-- The BGW law conditioned on size `≥ n` (including the null event of infinite trees);
the Dirac law at the leaf when the conditioning event has mass zero. -/
noncomputable def tailTreeLaw (μ : PMF ℕ) (n : ℕ) : ProbabilityMeasure BGW.LocallyFinite.Tree :=
  if h : BGW.LocallyFinite.bienaymeLaw μ.toMeasure (Attraction.sizeGeEvent n) ≠ 0 then
    ⟨(BGW.LocallyFinite.bienaymeLaw μ.toMeasure)[|Attraction.sizeGeEvent n],
      cond_isProbabilityMeasure h⟩
  else ⟨Measure.dirac BGW.LocallyFinite.leaf, inferInstance⟩

/-- The BGW law conditioned on size exactly `n`; the Dirac leaf if `n` is not admissible. -/
noncomputable def exactTreeLaw (μ : PMF ℕ) (n : ℕ) : ProbabilityMeasure BGW.LocallyFinite.Tree :=
  if h : Admissible μ n then
    ⟨(BGW.LocallyFinite.bienaymeLaw μ.toMeasure)[|BGW.LocallyFinite.sizeEvent n],
      BGW.LocallyFinite.isProbabilityMeasure_cond_sizeEvent μ.toMeasure h⟩
  else ⟨Measure.dirac BGW.LocallyFinite.leaf, inferInstance⟩

private def completeTree (j : ℕ) : ℕ → PlaneTree
  | 0 => PlaneTree.node []
  | n + 1 => PlaneTree.node (List.replicate j (completeTree j n))

private theorem size_completeTree (j n : ℕ) (hj : 1 ≤ j) : n ≤ (completeTree j n).size := by
  induction n with
  | zero => omega
  | succ n ih =>
    have hs : (completeTree j (n + 1)).size = 1 + j * (completeTree j n).size := by
      simp [completeTree, PlaneTree.size_node]
    rw [hs]
    nlinarith

private theorem weight_completeTree (μ : PMF ℕ) (j n : ℕ) (h0 : μ 0 ≠ 0)
    (hj : μ j ≠ 0) : PlaneTree.weight μ (completeTree j n) ≠ 0 := by
  induction n with
  | zero => simpa [completeTree, PlaneTree.weight_node] using h0
  | succ n ih =>
    simp only [completeTree, PlaneTree.weight_node, List.length_replicate,
      List.map_replicate, List.prod_replicate]
    exact mul_ne_zero hj (pow_ne_zero _ ih)

/-- Critical nondegenerate trees have arbitrarily large finite sizes: the tail mass is
positive for every `n`. -/
theorem bienaymeLaw_sizeGeEvent_ne_zero (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (n : ℕ) : BGW.LocallyFinite.bienaymeLaw μ.toMeasure (Attraction.sizeGeEvent n) ≠ 0 := by
  obtain ⟨j, hj, hμj⟩ := hc.exists_two_le_ne_zero hne
  let t := completeTree j n
  have hsize : n ≤ t.size := size_completeTree j n (by omega)
  have hw : PlaneTree.weight μ t ≠ 0 := weight_completeTree μ j n
    (hc.apply_zero_ne_zero hne) hμj
  have hatom : BGW.LocallyFinite.bienaymeLaw μ.toMeasure {t.toLocallyFinite} ≠ 0 := by
    rw [BGW.LocallyFinite.bienaymeLaw_toLocallyFinite]
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hw
  apply ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hatom) (measure_mono ?_))
  intro τ hτ
  obtain rfl := Set.mem_singleton_iff.mp hτ
  exact Or.inr (by rwa [BGW.LocallyFinite.ncard_present_toLocallyFinite])

/-- The first `m` DFS degrees of a finite tree (empty list for infinite trees). -/
noncomputable def treePrefix (m : ℕ) (τ : BGW.LocallyFinite.Tree) : List ℕ :=
  if h : BGW.LocallyFinite.FiniteVertices τ then
    ((PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).degrees).take m
  else []

/-- Finite trees whose first `m` DFS degrees are `a`. -/
def prefixCylinder (m : ℕ) (a : List ℕ) : Set BGW.LocallyFinite.Tree :=
  {τ | BGW.LocallyFinite.FiniteVertices τ ∧ treePrefix m τ = a}

/-- The prefix density, as a function of the first `m` degrees; `0` off surviving prefixes. -/
noncomputable def prefixDensity (μ : PMF ℕ) (n m : ℕ) (a : List ℕ) : ℝ≥0∞ :=
  if a.length = m ∧ IsSurvivingPrefix a then
    ENNReal.ofReal (exactPrefixWeight μ n m (prefixStack a))
  else 0

end BGW.StableTrees.DiscreteForest
