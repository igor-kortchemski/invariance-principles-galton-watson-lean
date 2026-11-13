/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactPairLocality

/-!
# The joint prefix density at a larger horizon

A smaller pair prefix is measurable in the larger degree prefix. The discrete prefix
Radon–Nikodym identity therefore transfers to the pair after restriction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees.ExactPair

open BGW.StableTrees.DiscreteForest BGW.StableTrees.PathTail BGW.StableTrees.TailPair
  BGW.StableTrees.ExactPrefix

private theorem prefixWalk_eq_sum (l : List ℕ) :
    DiscreteForest.prefixWalk l = (l.map (fun d : ℕ => (d : ℤ) - 1)).sum := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    change (j : ℤ) - 1 + DiscreteForest.prefixWalk l =
      (j : ℤ) - 1 + (l.map (fun d : ℕ => (d : ℤ) - 1)).sum
    rw [ih]

private theorem ae_tail_finite {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (n : ℕ) :
    ∀ᵐ τ ∂(tailTreeLaw μ n : Measure BGW.LocallyFinite.Tree),
      BGW.LocallyFinite.FiniteVertices τ := by
  rw [← BGW.StableTrees.DiscreteForest.firstLongTree_law μ h.critical h.nondegenerate n]
  change ∀ᵐ τ ∂((BGW.StableTrees.DiscreteForest.offspringSeqLaw μ).toMeasure.map
    (BGW.StableTrees.DiscreteForest.firstLongTree n)), _
  apply (ae_map_iff (BGW.StableTrees.DiscreteForest.measurable_firstLongTree n).aemeasurable
    BGW.LocallyFinite.measurableSet_finiteVertices).mpr
  exact ae_of_all _ fun ω =>
    (blockTree ω (DiscreteForest.firstLongIndex n ω)).finiteVertices_toLocallyFinite

private theorem ae_tail_good_prefix {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {n m : ℕ} (hmn : m < n) :
    ∀ᵐ τ ∂(tailTreeLaw μ n : Measure BGW.LocallyFinite.Tree),
      (treePrefix m τ).length = m ∧ IsSurvivingPrefix (treePrefix m τ) := by
  have hs : ∀ᵐ τ ∂(tailTreeLaw μ n : Measure BGW.LocallyFinite.Tree),
      τ ∈ Attraction.sizeGeEvent n := by
    rw [BGW.StableTrees.DiscreteForest.tailTreeLaw_toMeasure μ n
      (bienaymeLaw_sizeGeEvent_ne_zero μ h.critical h.nondegenerate n)]
    exact ae_cond_mem (BGW.StableTrees.DiscreteForest.measurableSet_sizeGeEvent n)
  filter_upwards [ae_tail_finite h n, hs] with τ hτ hsτ
  obtain ⟨t, rfl⟩ := (BGW.LocallyFinite.exists_toLocallyFinite_iff τ).mpr hτ
  have hnt : n ≤ t.size := by
    have hh := hsτ.resolve_left (not_not_intro t.finiteVertices_toLocallyFinite)
    simpa only [BGW.LocallyFinite.ncard_present_toLocallyFinite] using hh
  have hmt : m < t.size := hmn.trans_le hnt
  rw [BGW.StableTrees.DiscreteForest.treePrefix_toLocallyFinite]
  have hl : (t.degrees.take m).length = m := by simp [List.length_take, hmt.le]
  refine ⟨hl, ?_⟩
  intro i hi
  rw [hl] at hi
  rw [List.take_take, min_eq_left hi]
  have hh := BGW.PlaneTree.sum_take_increments_nonneg t (i := i) (by simpa using hi.trans_lt hmt)
  change 0 ≤ BGW.StableTrees.DiscreteForest.prefixWalk (t.degrees.take i)
  rw [prefixWalk_eq_sum]
  simpa only [BGW.PlaneTree.increments, ← List.map_take] using hh

/-- **Weighted identity at a larger horizon** (the repair): for `a ≤ a' < 1` with
`⌊an⌋ + 1 ≤ ⌊a'n⌋`, the exact pair law on `[0,a]` is the `[0,a]`-restriction of the tail pair law
on `[0,a']` weighted by the sealed walk weight at `a'` (a function of the walk value at `a'`). -/
theorem exactPairLaw_eq_map_withDensity {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {n : ℕ} (hn : Admissible μ n) {a a' : ℝ≥0} (haa' : a ≤ a')
    (ha' : a' ∈ Ioo (0 : ℝ≥0) 1) (hm : ⌊(a : ℝ) * n⌋₊ + 1 ≤ ⌊(a' : ℝ) * n⌋₊) :
    ((exactPairLaw μ B n hn a :
        ProbabilityMeasure (D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a : ℝ), ℝ))) :
        Measure (D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a : ℝ), ℝ))) =
      (((tailPairLaw μ B n a' :
          ProbabilityMeasure (D (a' : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a' : ℝ), ℝ))) :
          Measure (D (a' : ℝ) ℝ × C(Set.Icc (0 : ℝ) (a' : ℝ), ℝ))).withDensity
        (fun z => ENNReal.ofReal (prefixWeightFn μ B n a' z.1))).map (restrictPair haa') :=
  by
    have hnpos : 0 < n := by
      by_contra hh
      have hz : n = 0 := by omega
      subst n
      exact hn (by simp [BGW.LocallyFinite.sizeEvent_zero])
    have hmn : ⌊(a' : ℝ) * n⌋₊ < n := by
      apply (Nat.floor_lt (mul_nonneg a'.coe_nonneg (Nat.cast_nonneg n))).mpr
      exact mul_lt_of_lt_one_left (by exact_mod_cast hnpos) ha'.2
    let m := ⌊(a' : ℝ) * n⌋₊
    obtain ⟨g, hg⟩ := exists_treePairPath_eq_comp_treePrefix B n a hm
    let : MeasurableSpace (List ℕ) := ⊤
    let : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩
    have hgm : Measurable g := measurable_of_countable _
    let Q := (tailTreeLaw μ n : Measure BGW.LocallyFinite.Tree)
    let V := treePairPath B n a'
    let ρ := fun z : D (a' : ℝ) ℝ × C(Icc (0 : ℝ) (a' : ℝ), ℝ) =>
      ENNReal.ofReal (prefixWeightFn μ B n a' z.1)
    have hρ : Measurable ρ := ENNReal.measurable_ofReal.comp
      ((measurable_prefixWeightFn μ B n a').comp measurable_fst)
    have heq : ∀ᵐ τ ∂Q, prefixDensity μ n m (treePrefix m τ) = ρ (V τ) := by
      filter_upwards [ae_tail_good_prefix h hmn, ae_tail_finite h n] with τ hgood hfinite
      obtain ⟨t, rfl⟩ := (BGW.LocallyFinite.exists_toLocallyFinite_iff τ).mpr hfinite
      have hend : DiscreteBridge.endValue a' (treePrefixPath B n a' t.toLocallyFinite) =
          (DiscreteForest.prefixWalk (treePrefix m t.toLocallyFinite) : ℝ) / B n := by
        change BGW.Probability.RealWalk.partialSum (treeIncrementSeq t.toLocallyFinite)
          ⌊(n : ℝ) * (a' : ℝ)⌋₊ / B n = _
        simp only [BGW.Probability.RealWalk.partialSum, treeIncrementSeq,
          ExactPrefix.treeIncrements_toLocallyFinite, sum_range_getD,
          treePrefix_toLocallyFinite, prefixWalk_eq_sum,
          BGW.PlaneTree.increments, ← List.map_take, mul_comm (n : ℝ), m]
      change prefixDensity μ n m (treePrefix m t.toLocallyFinite) =
        ENNReal.ofReal (prefixWeightFn μ B n a' (treePrefixPath B n a' t.toLocallyFinite))
      rw [prefixDensity, ite_eq_left hgood, prefixWeightFn, ExactPrefix.prefixStack, hend,
        div_mul_cancel₀ _ (h.pos n hnpos).ne', round_intCast]
      rfl
    change (exactTreeLaw μ n : Measure BGW.LocallyFinite.Tree).map (treePairPath B n a) =
      ((Q.map V).withDensity ρ).map (restrictPair haa')
    ext A hA
    rw [Measure.map_apply (measurable_treePairPath B n a) hA,
      Measure.map_apply (measurable_restrictPair haa') hA,
      withDensity_apply _ ((measurable_restrictPair haa') hA),
      setLIntegral_map ((measurable_restrictPair haa') hA) hρ
        (measurable_treePairPath B n a')]
    have hset : V ⁻¹' (restrictPair haa' ⁻¹' A) = treePairPath B n a ⁻¹' A := by
      ext τ
      simp only [mem_preimage, V, restrictPair_treePairPath]
    rw [hset]
    have hf : treePairPath B n a ⁻¹' A = treePrefix m ⁻¹' (g ⁻¹' A) := by
      ext τ
      simp only [mem_preimage, hg, m]
    rw [hf, exactTreeLaw_prefix_eq_lintegral μ h.critical h.nondegenerate hn hmn]
    apply setLIntegral_congr_fun_ae ((measurable_treePrefix m) (hgm hA))
    exact heq.mono (fun _ hτ _ => hτ)

end BGW.StableTrees.ExactPair
