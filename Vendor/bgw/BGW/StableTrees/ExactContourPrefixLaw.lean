/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactPair
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Height prefix laws under exact-size conditioning

The height marginal of the sealed joint prefix theorem supplies tightness on every
strictly smaller time interval.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees.ExactContour

open BGW.StableTrees.DiscreteForest BGW.StableTrees.TailPair

/-- The exact-size height prefixes converge to the height marginal of the excursion prefix. -/
theorem tendsto_exactHeight_prefix {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    Tendsto (fun k => (exactTreeLaw μ (q k)).map (treeHeightPath B (q k) a)) atTop
      (𝓝 (((excLaw θ).map (restrictPair ha.2.le)).map Prod.snd)) := by
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (ExactPair.tendsto_exactPairLaw_prefix h hqtop hq a ha) continuous_snd
  convert ht using 1
  funext k
  apply Subtype.ext
  change (exactTreeLaw μ (q k)).toMeasure.map (treeHeightPath B (q k) a) =
    ((exactTreeLaw μ (q k)).toMeasure.map (treePairPath B (q k) a)).map Prod.snd
  rw [Measure.map_map measurable_snd (measurable_treePairPath B (q k) a)]
  rfl

/-- The entire sequence of height prefix laws is tight on each strict prefix. -/
theorem isTightMeasureSet_exactHeight_prefix {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    IsTightMeasureSet (Set.range fun k =>
      ((exactTreeLaw μ (q k)).map (treeHeightPath B (q k) a) :
        Measure C(Set.Icc (0 : ℝ) (a : ℝ), ℝ))) := by
  let P := fun k => (exactTreeLaw μ (q k)).map (treeHeightPath B (q k) a)
  let Q := ((excLaw θ).map (restrictPair ha.2.le)).map Prod.snd
  have hcompact : IsCompact (insert Q (range P)) :=
    (tendsto_exactHeight_prefix h hqtop hq a ha).isCompact_insert_range
  have ht := isTightMeasureSet_of_isCompact_closure
    (S := insert Q (range P)) (by rw [hcompact.isClosed.closure_eq]; exact hcompact)
  apply ht.subset
  rintro _ ⟨k, rfl⟩
  exact ⟨P k, mem_insert_of_mem _ (mem_range_self k), rfl⟩

end BGW.StableTrees.ExactContour
