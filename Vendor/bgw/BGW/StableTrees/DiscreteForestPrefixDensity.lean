/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestPrefixMass
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# The prefix Radon–Nikodym identity and its mass

On the countable space of degree words the atom identities determine the entire
prefix measure. Invalid prefixes have zero exact mass. Zero remaining-tail mass
also forces zero remaining exact mass, respecting totalized division.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Classical

namespace BGW.StableTrees.DiscreteForest

/-- A local discrete measurable structure for prefix-law comparison. -/
local instance prefixDensityWordMeasurable : MeasurableSpace (List ℕ) := ⊤
/-- Single words are measurable in the local prefix-law structure. -/
local instance prefixDensityWordSingleton : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

private theorem tree_good_prefix (t : PlaneTree) (m : ℕ) (hm : m < t.size) :
    (t.degrees.take m).length = m ∧ IsSurvivingPrefix (t.degrees.take m) := by
  have hl : (t.degrees.take m).length = m := by simp [List.length_take, hm.le]
  refine ⟨hl, ?_⟩
  intro i hi
  rw [hl] at hi
  change 0 ≤ prefixWalk ((t.degrees.take m).take i)
  rw [prefixWalk_eq_sum_steps, List.take_take, min_eq_left hi]
  have h := PlaneTree.sum_take_increments_nonneg t (i := i) (by simpa using (hi.trans_lt hm))
  simpa only [PlaneTree.increments, ← List.map_take] using h

private theorem ae_exact_sizeEvent (μ : PMF ℕ) {n : ℕ} (hn : Admissible μ n) :
    ∀ᵐ T ∂(exactTreeLaw μ n).toMeasure, T ∈ BGW.LocallyFinite.sizeEvent n := by
  apply (mem_ae_iff_prob_eq_one (BGW.LocallyFinite.measurableSet_sizeEvent n)).mpr
  rw [exactTreeLaw_toMeasure μ n hn]
  exact cond_apply_self hn (measure_ne_top _ _)

private theorem ae_exact_good_prefix (μ : PMF ℕ) {n m : ℕ} (hn : Admissible μ n)
    (hmn : m < n) : ∀ᵐ T ∂(exactTreeLaw μ n).toMeasure,
      (treePrefix m T).length = m ∧ IsSurvivingPrefix (treePrefix m T) := by
  filter_upwards [ae_exact_sizeEvent μ hn] with T hT
  obtain ⟨t, rfl⟩ := (BGW.LocallyFinite.exists_toLocallyFinite_iff T).mpr hT.1
  have hs : t.size = n := (BGW.LocallyFinite.toLocallyFinite_mem_sizeEvent_iff t n).mp hT
  rw [treePrefix_toLocallyFinite]
  exact tree_good_prefix t m (by omega)

private theorem ae_tail_finite (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    ∀ᵐ T ∂(tailTreeLaw μ n).toMeasure, BGW.LocallyFinite.FiniteVertices T := by
  have hm : BGW.LocallyFinite.bienaymeLaw μ.toMeasure
      {T | BGW.LocallyFinite.FiniteVertices T} = 1 := by
    rw [← first_block_law μ hc hne, Measure.map_apply (measurable_blockLF.eval)
      BGW.LocallyFinite.measurableSet_finiteVertices]
    have heq : (fun ω => blockLF ω 0) ⁻¹' {T | BGW.LocallyFinite.FiniteVertices T} = univ := by
      ext ω
      exact iff_true_intro (blockTree ω 0).finiteVertices_toLocallyFinite
    rw [heq, measure_univ]
  have ha := (mem_ae_iff_prob_eq_one BGW.LocallyFinite.measurableSet_finiteVertices).mpr hm
  rw [tailTreeLaw_toMeasure μ n (bienaymeLaw_sizeGeEvent_ne_zero μ hc hne n)]
  exact cond_absolutelyContinuous.ae_le ha

private theorem prefix_atom_eq_cylinder (P : Measure BGW.LocallyFinite.Tree)
    (hP : ∀ᵐ T ∂P, BGW.LocallyFinite.FiniteVertices T) (m : ℕ) (a : List ℕ) :
    P (treePrefix m ⁻¹' {a}) = P (prefixCylinder m a) := by
  apply measure_congr
  filter_upwards [hP] with T hT
  exact propext ⟨fun h => ⟨hT, h⟩, fun h => h.2⟩

private theorem forestTail_nonneg (μ : PMF ℕ) (j r : ℕ) : 0 ≤ forestTail μ j r := by
  apply tsum_nonneg
  intro k
  exact Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) _

private theorem forestMass_le_tail (μ : PMF ℕ) (j r : ℕ) :
    forestMass μ j r ≤ forestTail μ j r := by
  have h := ((summable_forestMass μ j).indicator (Ici r)).le_tsum r
    (fun k _ => Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) k)
  simpa only [forestTail, Set.indicator_of_mem (show r ∈ Ici r from by simp)] using h

private theorem prefixWeight_nonneg (μ : PMF ℕ) (n m j : ℕ) :
    0 ≤ exactPrefixWeight μ n m j := by
  apply mul_nonneg
  · exact div_nonneg ENNReal.toReal_nonneg (forestTail_nonneg μ j (n - m))
  · exact div_nonneg (forestTail_nonneg μ 1 n) ENNReal.toReal_nonneg

private theorem prefix_atom_real_ratio (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {n m : ℕ} {a : List ℕ} (hn : Admissible μ n) (ham : a.length = m) (hmn : m < n)
    (hs : IsSurvivingPrefix a) :
    (exactTreeLaw μ n).toMeasure.real (prefixCylinder m a) =
      exactPrefixWeight μ n m (prefixStack a) *
        (tailTreeLaw μ n).toMeasure.real (prefixCylinder m a) := by
  by_cases hG : 0 < forestTail μ (prefixStack a) (n - m)
  · exact exactPrefixMass_eq_prefixRN_mul μ hc hne hn ham hmn hs hG
  · have hG0 : forestTail μ (prefixStack a) (n - m) = 0 :=
      le_antisymm (not_lt.mp hG) (forestTail_nonneg μ _ _)
    have hf0 : forestMass μ (prefixStack a) (n - m) = 0 := by
      have h := forestMass_le_tail μ (prefixStack a) (n - m)
      rw [hG0] at h
      exact le_antisymm h ENNReal.toReal_nonneg
    rw [exactPrefixMass μ hc hne hn ham hmn hs, hf0, mul_zero, zero_div,
      exactPrefixWeight, hf0, zero_div, zero_mul, zero_mul]

private theorem prefix_atom_ratio (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {n m : ℕ} {a : List ℕ} (hn : Admissible μ n) (ham : a.length = m) (hmn : m < n)
    (hs : IsSurvivingPrefix a) :
    (exactTreeLaw μ n).toMeasure (prefixCylinder m a) =
      ENNReal.ofReal (exactPrefixWeight μ n m (prefixStack a)) *
        (tailTreeLaw μ n).toMeasure (prefixCylinder m a) := by
  have h := congrArg ENNReal.ofReal (prefix_atom_real_ratio μ hc hne hn ham hmn hs)
  simp only [measureReal_def, ENNReal.ofReal_mul (prefixWeight_nonneg μ n m (prefixStack a)),
    ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  exact h

private theorem prefix_map_withDensity (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {n m : ℕ} (hn : Admissible μ n) (hmn : m < n) :
    (exactTreeLaw μ n).toMeasure.map (treePrefix m) =
      ((tailTreeLaw μ n).toMeasure.map (treePrefix m)).withDensity (prefixDensity μ n m) := by
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_treePrefix m) (measurableSet_singleton _),
    withDensity_apply _ (measurableSet_singleton _), lintegral_singleton,
    Measure.map_apply (measurable_treePrefix m) (measurableSet_singleton _)]
  by_cases hg : a.length = m ∧ IsSurvivingPrefix a
  · rw [prefix_atom_eq_cylinder _ ((ae_exact_sizeEvent μ hn).mono (fun _ h => h.1)),
      prefix_atom_eq_cylinder _ (ae_tail_finite μ hc hne n), prefixDensity, ite_eq_left hg]
    exact prefix_atom_ratio μ hc hne hn hg.1 hmn hg.2
  · rw [prefixDensity, ite_eq_right hg, zero_mul]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ae_exact_good_prefix μ hn hmn] with T hT
    intro ha
    change treePrefix m T = a at ha
    exact hg (ha ▸ hT)

/-- Radon-Nikodym identity from the tail to the exact law on the first-`m`-degrees
sigma-field: for every set `S` of degree words,
`P_exact(prefix ∈ S) = ∫_{prefix ∈ S} prefixDensity d P_tail`. -/
theorem exactTreeLaw_prefix_eq_lintegral (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {n m : ℕ} (hn : Admissible μ n) (hmn : m < n) (S : Set (List ℕ)) :
    (exactTreeLaw μ n).toMeasure (treePrefix m ⁻¹' S) =
      ∫⁻ τ in treePrefix m ⁻¹' S, prefixDensity μ n m (treePrefix m τ)
        ∂((tailTreeLaw μ n).toMeasure) := by
  have hS : MeasurableSet S := (Set.to_countable _).measurableSet
  rw [← Measure.map_apply (measurable_treePrefix m) hS,
    prefix_map_withDensity μ hc hne hn hmn, withDensity_apply _ hS,
    setLIntegral_map hS (measurable_of_countable _) (measurable_treePrefix m)]

/-- The tail expectation of the RN density is one. -/
theorem lintegral_prefixDensity_tail (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {n m : ℕ} (hn : Admissible μ n) (hmn : m < n) :
    ∫⁻ τ, prefixDensity μ n m (treePrefix m τ) ∂((tailTreeLaw μ n).toMeasure) = 1 := by
  simpa only [preimage_univ, measure_univ, setLIntegral_univ] using
    (exactTreeLaw_prefix_eq_lintegral μ hc hne hn hmn univ).symm

end BGW.StableTrees.DiscreteForest
