module

public import BGWLeaves.GeneralAFunctional.TreeClocks
public import BGWLeaves.GeneralAFunctional.TreePrefixMeasure
public import BGW.StableTrees.TailPair
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! Joint tail paths augmented by the normalized revealed-mark count. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.TreeAugmented

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGW.StableTrees.TailPair BGW.Skorokhod
open BGWLeaves.StableAnalysis
open BGWLeaves.GeneralAFunctional.TreePrefix BGWLeaves.GeneralAFunctional.TreeMarkTail
open BGWLeaves.GeneralAFunctional.TreeClocks
open scoped ENNReal NNReal Topology

abbrev PairSpace (b : ℝ≥0) := D (b : ℝ) ℝ × C(Set.Icc (0 : ℝ) (b : ℝ), ℝ)

noncomputable def augmentedMap (A : Set ℕ) (B : ℕ → ℝ) (n r : ℕ) (b : ℝ≥0)
    (T : LocallyFinite.Tree) : PairSpace b × ℝ :=
  (treePairPath B r b T, (prefixMarks A (treePrefix (prefixLength b r) T) : ℝ) / n)

theorem measurable_augmentedMap (A : Set ℕ) (B : ℕ → ℝ) (n r : ℕ) (b : ℝ≥0) :
    Measurable (augmentedMap A B n r b) :=
  (measurable_treePairPath B r b).prodMk
    (((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (measurable_prefix_marks A (prefixLength b r))).div_const n)

noncomputable def augmentedTailLaw (μ : PMF ℕ) (A : Set ℕ) (B : ℕ → ℝ)
    (n : ℕ) (b : ℝ≥0) : ProbabilityMeasure (PairSpace b × ℝ) :=
  (tailTreeLaw μ (explorationIndex μ A n)).map
    (augmentedMap A B n (explorationIndex μ A n) b)

noncomputable def augmentedTailLimit (θ : ℝ) (b : ℝ≥0) : ProbabilityMeasure (PairSpace b × ℝ) :=
  (tailExcLaw θ b).map (fun z => (z, (b : ℝ)))

/-- B combined with the total-tail joint invariance principle. The augmentation
retains the mark count needed by the exact deterministic-prefix density. -/
theorem augmentedTailLaw_tendsto {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hap : Aperiodic μ) {A : Set ℕ}
    (hA : μ.toMeasure A ≠ 0) (hA1 : μ.toMeasure A ≠ 1)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) {b : ℝ≥0}
    (hb0 : 0 < b) (hb1 : b < 1) :
    Tendsto (fun k => augmentedTailLaw μ A B (q k) b) atTop
      (𝓝 (augmentedTailLimit θ b)) := by
  let r := fun k => explorationIndex μ A (q k)
  have hr : Tendsto r atTop atTop := (explorationIndex_atTop hA).comp hq
  have hb0R : 0 < (b : ℝ) := hb0
  have hm := (prefixLength_ratio b).comp hr
  have hmq := (prefixLength_exploration_ratio hA b).comp hq
  have hlt : ∀ᶠ k in atTop, prefixLength b (r k) < r k := by
    filter_upwards [hr.eventually_ge_atTop 1] with k hk
    exact prefixLength_lt hb1 (by omega)
  have hp : 0 < (μ.toMeasure A).toReal := ENNReal.toReal_pos hA (measure_ne_top _ _)
  have hconst : (μ.toMeasure A).toReal * ((b : ℝ) / (μ.toMeasure A).toReal) = b := by
    field_simp
  have hbase := (tendsto_tailPairLaw h hb0).comp hr
  have hlim := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hbase
    (continuous_id.prodMk continuous_const : Continuous (fun z : PairSpace b => (z, (b : ℝ))))
  have hG (k : ℕ) : ((tailPairLaw μ B (r k) b).map (fun z => (z, (b : ℝ)))) =
      (tailTreeLaw μ (r k)).map (fun T => (treePairPath B (r k) b T, (b : ℝ))) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact Measure.map_map (measurable_id.prodMk measurable_const) (measurable_treePairPath B (r k) b)
  apply BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability
    (fun k => tailTreeLaw μ (r k))
    (fun k => measurable_augmentedMap A B (q k) (r k) b)
    (fun k => (measurable_treePairPath B (r k) b).prodMk measurable_const) ?_
    (hlim.congr fun k => hG k)
  intro ε hε
  have ht := tail_prefix_marks_scaled h.critical h.nondegenerate hap ⟨B, h⟩
    hA hA1 hr hq hb0R hm hmq hlt hε
  rw [hconst] at ht
  simpa only [augmentedMap, dist_prod_same_left, Real.dist_eq] using ht

end BGWLeaves.GeneralAFunctional.TreeAugmented
