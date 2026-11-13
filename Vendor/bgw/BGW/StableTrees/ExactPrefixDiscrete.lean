/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactPrefixBasic
import BGW.StableTrees.DiscreteBridgeLocalLimit
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Finite degree-prefix observables

The path on a strict prefix depends only on the corresponding finite degree word.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical

namespace BGW.StableTrees.ExactPrefix

open BGW BGW.Skorokhod BGW.Probability.RealWalk
open DiscreteForest (treePrefix tailTreeLaw exactTreeLaw IsSurvivingPrefix)
open DiscreteBridge (exactWalkLaw endValue)
open PathTail (tailWalkPrefixLaw)
open PathTail (treePrefixPath treeIncrementSeq treeIncrements)

/-- The discrete σ-algebra on words of natural numbers, used locally for countable sums. -/
local instance instMeasurableSpaceListNat : MeasurableSpace (List ℕ) := ⊤
local instance : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

private theorem prefixWalk_eq_sum (l : List ℕ) :
    DiscreteForest.prefixWalk l = (l.map (fun d : ℕ => (d : ℤ) - 1)).sum := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    change (j : ℤ) - 1 + DiscreteForest.prefixWalk l =
      (j : ℤ) - 1 + (l.map (fun d : ℕ => (d : ℤ) - 1)).sum
    rw [ih]

private noncomputable def wordPrefixPath (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0)
    (l : List ℕ) : D (a : ℝ) ℝ :=
  realStepPath (a : ℝ) n (B n) (fun i => ((l.map (fun d : ℕ => (d : ℤ) - 1)).getD i 0 : ℝ))

private theorem treePrefixPath_factor (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0)
    (τ : LocallyFinite.Tree) :
    treePrefixPath B n a τ = wordPrefixPath B n a (treePrefix ⌊(a : ℝ) * n⌋₊ τ) := by
  by_cases hτ : LocallyFinite.FiniteVertices τ
  · obtain ⟨t, rfl⟩ := (LocallyFinite.exists_toLocallyFinite_iff τ).mpr hτ
    have hi := treeIncrements_toLocallyFinite t
    rw [DiscreteForest.treePrefix_toLocallyFinite]
    apply BGW.Skorokhod.ext
    intro u
    change partialSum (treeIncrementSeq t.toLocallyFinite) ⌊(n : ℝ) * (u : ℝ)⌋₊ / B n =
      partialSum (fun i => ((((t.degrees.take ⌊(a : ℝ) * n⌋₊).map
        (fun d : ℕ => (d : ℤ) - 1)).getD i 0 : ℤ) : ℝ)) ⌊(n : ℝ) * (u : ℝ)⌋₊ / B n
    congr 1
    unfold partialSum
    apply Finset.sum_congr rfl
    intro i hiu
    have hm : ⌊(n : ℝ) * (u : ℝ)⌋₊ ≤ ⌊(a : ℝ) * n⌋₊ := by
      apply Nat.floor_mono
      nlinarith [u.2.2, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have him : i < ⌊(a : ℝ) * n⌋₊ := (Finset.mem_range.mp hiu).trans_le hm
    simp only [treeIncrementSeq, hi]
    rw [List.map_take]
    change (t.increments.getD i 0 : ℝ) = ((t.increments.take ⌊(a : ℝ) * n⌋₊).getD i 0 : ℝ)
    simp [List.getD, him]
  · apply BGW.Skorokhod.ext
    intro u
    simp [treePrefixPath, wordPrefixPath, treePrefix, treeIncrementSeq, treeIncrements,
      hτ, realStepPath_apply, partialSum]

private theorem ae_tail_finite {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (n : ℕ) :
    ∀ᵐ τ ∂(tailTreeLaw μ n : Measure LocallyFinite.Tree), LocallyFinite.FiniteVertices τ := by
  rw [← DiscreteForest.firstLongTree_law μ h.critical h.nondegenerate n]
  change ∀ᵐ τ ∂((DiscreteForest.offspringSeqLaw μ).toMeasure.map
    (DiscreteForest.firstLongTree n)), _
  apply (ae_map_iff (DiscreteForest.measurable_firstLongTree n).aemeasurable
    LocallyFinite.measurableSet_finiteVertices).mpr
  exact ae_of_all _ fun ω =>
    (DiscreteForest.blockTree ω (DiscreteForest.firstLongIndex n ω)).finiteVertices_toLocallyFinite

private theorem ae_tail_good_prefix {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {n m : ℕ} (hmn : m < n) :
    ∀ᵐ τ ∂(tailTreeLaw μ n : Measure LocallyFinite.Tree),
      (treePrefix m τ).length = m ∧ IsSurvivingPrefix (treePrefix m τ) := by
  have hs : ∀ᵐ τ ∂(tailTreeLaw μ n : Measure LocallyFinite.Tree),
      τ ∈ Attraction.sizeGeEvent n := by
    rw [DiscreteForest.tailTreeLaw_toMeasure μ n
      (DiscreteForest.bienaymeLaw_sizeGeEvent_ne_zero μ h.critical h.nondegenerate n)]
    exact ae_cond_mem (DiscreteForest.measurableSet_sizeGeEvent n)
  filter_upwards [ae_tail_finite h n, hs] with τ hτ hsτ
  obtain ⟨t, rfl⟩ := (LocallyFinite.exists_toLocallyFinite_iff τ).mpr hτ
  have hnt : n ≤ t.size := by
    have hh := hsτ.resolve_left (not_not_intro t.finiteVertices_toLocallyFinite)
    simpa only [LocallyFinite.ncard_present_toLocallyFinite] using hh
  have hmt : m < t.size := hmn.trans_le hnt
  rw [DiscreteForest.treePrefix_toLocallyFinite]
  have hl : (t.degrees.take m).length = m := by simp [List.length_take, hmt.le]
  refine ⟨hl, ?_⟩
  intro i hi
  rw [hl] at hi
  rw [List.take_take, min_eq_left hi]
  have hh := PlaneTree.sum_take_increments_nonneg t (i := i) (by simpa using hi.trans_lt hmt)
  change 0 ≤ DiscreteForest.prefixWalk (t.degrees.take i)
  rw [prefixWalk_eq_sum]
  simpa only [PlaneTree.increments, ← List.map_take] using hh

private theorem endValue_wordPrefixPath (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0)
    (l : List ℕ) (hl : l.length = ⌊(a : ℝ) * n⌋₊) :
    DiscreteBridge.endValue a (wordPrefixPath B n a l) =
      (DiscreteForest.prefixWalk l : ℝ) / B n := by
  change (∑ i ∈ Finset.range ⌊(n : ℝ) * (a : ℝ)⌋₊,
    ((l.map (fun d : ℕ => (d : ℤ) - 1)).getD i 0 : ℝ)) / B n = _
  rw [mul_comm (n : ℝ), sum_range_getD]
  have ht : (l.map (fun d : ℕ => (d : ℤ) - 1)).take ⌊(a : ℝ) * n⌋₊ =
      l.map (fun d : ℕ => (d : ℤ) - 1) := by
    apply List.take_of_length_le
    simp only [List.length_map, hl, le_refl]
  rw [ht, prefixWalk_eq_sum]

private theorem stack_wordPrefixPath (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0)
    (hB : B n ≠ 0) (l : List ℕ) (hl : l.length = ⌊(a : ℝ) * n⌋₊) :
    prefixStack B n a (wordPrefixPath B n a l) = DiscreteForest.prefixStack l := by
  rw [prefixStack, endValue_wordPrefixPath B n a l hl, div_mul_cancel₀ _ hB, round_intCast]
  rfl

/-- The exact-prefix weight is nonnegative, including totalized zero denominators. -/
theorem prefixWeightFn_nonneg (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0)
    (x : D (a : ℝ) ℝ) : 0 ≤ prefixWeightFn μ B n a x := by
  have htail (j r : ℕ) : 0 ≤ forestTail μ j r := by
    apply tsum_nonneg
    intro k
    exact Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) _
  exact mul_nonneg (div_nonneg ENNReal.toReal_nonneg (htail _ _))
    (div_nonneg (htail _ _) ENNReal.toReal_nonneg)

/-- **Prefix RN identity** from the tail to the exact-size walk prefix law (K02
`exactTreeLaw_prefix_eq_lintegral` pushed through the prefix path). -/
theorem exactWalkPrefixLaw_eq_withDensity {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {n : ℕ} (hn : Admissible μ n) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ((exactWalkPrefixLaw μ B n hn a ha.2.le : ProbabilityMeasure (D (a : ℝ) ℝ)) :
        Measure (D (a : ℝ) ℝ)) =
      ((tailWalkPrefixLaw μ B n a : ProbabilityMeasure (D (a : ℝ) ℝ)) :
          Measure (D (a : ℝ) ℝ)).withDensity
        (fun x => ENNReal.ofReal (prefixWeightFn μ B n a x)) := by
  have hnpos : 0 < n := by
    by_contra hn0
    have hnzero : n = 0 := by omega
    subst n
    exact hn (by simp [LocallyFinite.sizeEvent_zero])
  have hmn : ⌊(a : ℝ) * n⌋₊ < n := by
    apply (Nat.floor_lt (mul_nonneg a.coe_nonneg (Nat.cast_nonneg n))).mpr
    exact mul_lt_of_lt_one_left (by exact_mod_cast hnpos) ha.2
  let m := ⌊(a : ℝ) * n⌋₊
  let g := wordPrefixPath B n a
  have hg : Measurable g := measurable_of_countable _
  have hd : Measurable (fun x => ENNReal.ofReal (prefixWeightFn μ B n a x)) :=
    ENNReal.measurable_ofReal.comp (measurable_prefixWeightFn μ B n a)
  have heq : ∀ᵐ τ ∂(tailTreeLaw μ n : Measure LocallyFinite.Tree),
      DiscreteForest.prefixDensity μ n m (treePrefix m τ) =
        ENNReal.ofReal (prefixWeightFn μ B n a (treePrefixPath B n a τ)) := by
    filter_upwards [ae_tail_good_prefix h hmn] with τ hτ
    rw [DiscreteForest.prefixDensity, ite_eq_left hτ, prefixWeightFn,
      treePrefixPath_factor, stack_wordPrefixPath B n a (h.pos n hnpos).ne' _ hτ.1]
  rw [exactWalkPrefixLaw_eq_map_exactTreeLaw hn a ha]
  change (exactTreeLaw μ n : Measure LocallyFinite.Tree).map (treePrefixPath B n a) =
    ((tailTreeLaw μ n : Measure LocallyFinite.Tree).map (treePrefixPath B n a)).withDensity _
  ext A hA
  rw [Measure.map_apply (PathTail.measurable_treePrefixPath B n a) hA,
    withDensity_apply _ hA,
    setLIntegral_map hA hd (PathTail.measurable_treePrefixPath B n a)]
  have hf : treePrefixPath B n a ⁻¹' A = treePrefix m ⁻¹' (g ⁻¹' A) := by
    ext τ
    simp only [mem_preimage]
    rw [treePrefixPath_factor]
  rw [hf, DiscreteForest.exactTreeLaw_prefix_eq_lintegral μ h.critical h.nondegenerate hn hmn]
  apply setLIntegral_congr_fun_ae ((DiscreteForest.measurable_treePrefix m) (hg hA))
  exact heq.mono (fun _ hτ _ => hτ)

private theorem prefix_sum_divisible {d : ℤ} (l : List ℕ)
    (hl : ∀ j ∈ l, d ∣ (j : ℤ)) :
    d ∣ DiscreteForest.prefixWalk l + (l.length : ℤ) := by
  induction l with
  | nil => simp [DiscreteForest.prefixWalk]
  | cons j l ih =>
    have hj := hl j (by simp)
    have ht := ih (fun i hi => hl i (by simp [hi]))
    convert dvd_add hj ht using 1
    simp only [prefixWalk_eq_sum, List.map_cons, List.sum_cons,
      List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

/-- Almost surely under the tail walk prefix law the path is lattice-good (`n` admissible). -/
theorem ae_latticeGood_tailWalkPrefixLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {n : ℕ} (hn : Admissible μ n) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ∀ᵐ x ∂(tailWalkPrefixLaw μ B n a : Measure (D (a : ℝ) ℝ)), LatticeGood μ B n a x := by
  have hnpos : 0 < n := by
    by_contra hh
    have hz : n = 0 := by omega
    subst n
    exact hn (by simp [LocallyFinite.sizeEvent_zero])
  have hmn : ⌊(a : ℝ) * n⌋₊ < n := by
    apply (Nat.floor_lt (mul_nonneg a.coe_nonneg (Nat.cast_nonneg n))).mpr
    exact mul_lt_of_lt_one_left (by exact_mod_cast hnpos) ha.2
  let m := ⌊(a : ℝ) * n⌋₊
  have hsupport : ∀ᵐ ω ∂(DiscreteForest.offspringSeqLaw μ : Measure (ℕ → ℕ)),
      ∀ i, μ (ω i) ≠ 0 := by
    apply ae_all_iff.mpr
    intro i
    have hs : ∀ᵐ j ∂μ.toMeasure, μ j ≠ 0 := by
      apply ae_iff_of_countable.mpr
      intro j hj
      simpa only [PMF.toMeasure_apply_singleton μ j (measurableSet_singleton j)] using hj
    have hs' : ∀ᵐ j ∂((DiscreteForest.offspringSeqLaw μ : Measure (ℕ → ℕ)).map
        (fun ω => ω i)), μ j ≠ 0 := by
      rw [show (DiscreteForest.offspringSeqLaw μ : Measure (ℕ → ℕ)) =
        Measure.infinitePi (fun _ : ℕ => μ.toMeasure) from rfl, Measure.infinitePi_map_eval]
      exact hs
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hs'
  have hdegrees : ∀ᵐ τ ∂(tailTreeLaw μ n : Measure LocallyFinite.Tree),
      ∀ j ∈ treePrefix m τ, (Scalar.latticeSpan μ : ℤ) ∣ (j : ℤ) := by
    rw [← DiscreteForest.firstLongTree_law μ h.critical h.nondegenerate n]
    change ∀ᵐ τ ∂((DiscreteForest.offspringSeqLaw μ : Measure (ℕ → ℕ)).map
      (DiscreteForest.firstLongTree n)), _
    apply (ae_map_iff (DiscreteForest.measurable_firstLongTree n).aemeasurable
      ((DiscreteForest.measurable_treePrefix m) (Set.to_countable
        {l : List ℕ | ∀ j ∈ l, (Scalar.latticeSpan μ : ℤ) ∣ (j : ℤ)}).measurableSet)).mpr
    filter_upwards [DiscreteForest.ae_ladderFinite μ h.critical h.nondegenerate, hsupport]
      with ω hω hs
    intro j hj
    change j ∈ treePrefix m
      (DiscreteForest.blockTree ω (DiscreteForest.firstLongIndex n ω)).toLocallyFinite at hj
    rw [DiscreteForest.treePrefix_toLocallyFinite, DiscreteForest.degrees_blockTree hω] at hj
    have hj' := List.mem_of_mem_take hj
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj'
    exact Scalar.latticeSpan_dvd_of_ne_zero h.critical h.nondegenerate (hs _)
  have hd : (Scalar.latticeSpan μ : ℤ) ∣ (n : ℤ) - 1 := by
    by_contra hnot
    have hh : ¬ (Scalar.latticeSpan μ : ℤ) ∣ (-1 : ℤ) + n := by
      simpa only [sub_eq_add_neg, add_comm] using hnot
    have hz := Scalar.walkProb_eq_zero_of_not_dvd h hh
    have hp := DiscreteBridge.walkProb_neg_one_pos hn
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  have hs := measurable_prefixStack B n a
  change ∀ᵐ x ∂((tailTreeLaw μ n : Measure LocallyFinite.Tree).map
    (treePrefixPath B n a)), _
  apply (ae_map_iff (PathTail.measurable_treePrefixPath B n a).aemeasurable
    (hs (Set.to_countable {j : ℕ | 1 ≤ j ∧
      (Scalar.latticeSpan μ : ℤ) ∣ (n : ℤ) - (m : ℕ) - (j : ℕ)}).measurableSet)).mpr
  filter_upwards [ae_tail_good_prefix h hmn, hdegrees] with τ hτ hdeg
  rw [treePrefixPath_factor,
    stack_wordPrefixPath B n a (h.pos n hnpos).ne' _ hτ.1]
  refine ⟨DiscreteForest.prefixStack_pos hτ.2, ?_⟩
  have hp := prefix_sum_divisible (treePrefix m τ) hdeg
  rw [hτ.1] at hp
  rw [DiscreteForest.prefixStack_cast hτ.2]
  convert dvd_sub hd hp using 1
  ring

end BGW.StableTrees.ExactPrefix
