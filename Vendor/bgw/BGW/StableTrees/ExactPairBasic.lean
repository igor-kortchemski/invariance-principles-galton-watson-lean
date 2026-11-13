/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactPrefix
public import BGW.StableTrees.JointExcursion
public import BGW.StableTrees.TailPair

/-!
# Exact-size walk and height prefix laws

Both coordinates come from one tree, with the sealed terminal walk convention. The
restriction and marginal identities identify the law with the existing walk-prefix API.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees.ExactPair

open BGW.StableTrees.DiscreteForest BGW.StableTrees.PathTail BGW.StableTrees.TailPair
  BGW.StableTrees.ExactPrefix

/-- **The exact-size pair law on `[0,a]`**: the (walk, height) pair of ONE BGW tree conditioned
on size exactly `n` (sealed K02 `exactTreeLaw`, totalized), at scales `nt`, `1/B n`, `B n / n`. -/
noncomputable def exactPairLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (_hn : Admissible μ n)
    (a : ℝ≥0) : ProbabilityMeasure (D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a : ℝ), ℝ)) :=
  (exactTreeLaw μ n).map (treePairPath B n a)

/-- The walk marginal of the exact pair law is the sealed K07 exact walk prefix law. -/
theorem exactPairLaw_map_fst {μ : PMF ℕ} {B : ℕ → ℝ} {n : ℕ} (hn : Admissible μ n) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    (exactPairLaw μ B n hn a).map Prod.fst = exactWalkPrefixLaw μ B n hn a ha.2.le := by
  apply Subtype.ext
  change ((exactTreeLaw μ n : Measure BGW.LocallyFinite.Tree).map
    (treePairPath B n a)).map Prod.fst = (exactWalkPrefixLaw μ B n hn a ha.2.le : Measure _)
  rw [Measure.map_map measurable_fst (measurable_treePairPath B n a)]
  exact (exactWalkPrefixLaw_eq_map_exactTreeLaw hn a ha).symm

/-- The walk marginal of the target is the sealed K07 target (every `θ`). -/
theorem map_fst_restrictPair_excLaw (θ : ℝ) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ((excLaw θ).map (restrictPair ha.2.le)).map Prod.fst =
      (unitExcursionLaw θ).map (excursionRestrict a) := by
  apply Subtype.ext
  change (((unitExcursionLaw θ : Measure Excursion).map (excursionPair θ 1)).map
    (restrictPair ha.2.le)).map Prod.fst =
      (unitExcursionLaw θ : Measure Excursion).map (excursionRestrict a)
  rw [Measure.map_map measurable_fst (measurable_restrictPair ha.2.le),
    Measure.map_map (measurable_fst.comp (measurable_restrictPair ha.2.le))
      (measurable_excursionPair θ 1)]
  rfl

/-! ### Prefix-measurability repair -/

/-- **Projectivity** (deterministic): the pair path of horizon `a'` restricted to `[0,a]` is the
pair path of horizon `a`. -/
theorem restrictPair_treePairPath (B : ℕ → ℝ) (n : ℕ) {a a' : ℝ≥0} (h : a ≤ a')
    (τ : BGW.LocallyFinite.Tree) :
    restrictPair h (treePairPath B n a' τ) = treePairPath B n a τ := by
  apply Prod.ext
  · apply BGW.Skorokhod.ext
    intro t
    rfl
  · ext t
    simp only [restrictPair, treePairPath, treeHeightPath,
      dite_eq_left (continuous_treeHeightLin τ), ContinuousMap.comp_apply,
      ContinuousMap.coe_mk]

end BGW.StableTrees.ExactPair
