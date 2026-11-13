/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestPrefixCoding

/-!
# Unconditioned masses of surviving prefixes

Completing a surviving initial word is first passage of the remaining forest.
The exact mass is a product, and summing over the size gives the inclusive tail.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Classical

namespace BGW.StableTrees.DiscreteForest

/-- The joint exact-size/prefix mass is the prefix weight times the remaining forest mass. -/
theorem sizeEvent_prefixCylinder_mass (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {n m : ℕ} {a : List ℕ} (ham : a.length = m) (hmn : m < n)
    (hs : IsSurvivingPrefix a) :
    BGW.LocallyFinite.bienaymeLaw μ.toMeasure
      (BGW.LocallyFinite.sizeEvent n ∩ prefixCylinder m a) =
        (a.map μ).prod * BGW.forestWeight μ (prefixStack a) (n - m) := by
  have heq : (fun ω => blockLF ω 0) ⁻¹'
      (BGW.LocallyFinite.sizeEvent n ∩ prefixCylinder m a) =ᵐ[(offspringSeqLaw μ).toMeasure]
      {ω | seqPrefix m ω = a} ∩ shiftSeq m ⁻¹' forestHit (prefixStack a) (n - m) := by
    filter_upwards [ae_ladderFinite μ hc hne] with ω hω
    apply propext
    have hsz : blockLF ω 0 ∈ BGW.LocallyFinite.sizeEvent n ↔ ladderTime ω 1 = n := by
      rw [blockLF, BGW.LocallyFinite.toLocallyFinite_mem_sizeEvent_iff, first_block_size hω]
    change (blockLF ω 0 ∈ BGW.LocallyFinite.sizeEvent n ∧
      BGW.LocallyFinite.FiniteVertices (blockLF ω 0) ∧ treePrefix m (blockLF ω 0) = a) ↔
      (seqPrefix m ω = a ∧ shiftSeq m ω ∈ forestHit (prefixStack a) (n - m))
    rw [← prefix_ladder_iff_forestHit hω ham hmn hs]
    constructor
    · rintro ⟨hn, _, hp⟩
      have hL := hsz.mp hn
      rw [treePrefix_first_block hω m (by omega)] at hp
      exact ⟨hp, hL⟩
    · rintro ⟨hp, hL⟩
      refine ⟨hsz.mpr hL, (blockTree ω 0).finiteVertices_toLocallyFinite, ?_⟩
      rw [treePrefix_first_block hω m (by omega)]
      exact hp
  rw [← first_block_law μ hc hne, Measure.map_apply (measurable_blockLF.eval)
    ((BGW.LocallyFinite.measurableSet_sizeEvent n).inter (measurableSet_prefixCylinder m a)),
    measure_congr heq]
  have h := seqPrefix_inter_shift_mass μ a (measurableSet_forestHit (prefixStack a) (n - m))
  rw [ham] at h
  rw [h, forestHit_mass μ (prefixStack_pos hs)]

/-- The real-valued exact joint mass. -/
theorem sizeEvent_prefixCylinder_real (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {n m : ℕ} {a : List ℕ} (ham : a.length = m) (hmn : m < n)
    (hs : IsSurvivingPrefix a) :
    (BGW.LocallyFinite.bienaymeLaw μ.toMeasure).real
      (BGW.LocallyFinite.sizeEvent n ∩ prefixCylinder m a) =
        degreeWeight μ a * forestMass μ (prefixStack a) (n - m) := by
  rw [measureReal_def, sizeEvent_prefixCylinder_mass μ hc hne ham hmn hs,
    ENNReal.toReal_mul]
  rfl

/-- The real joint inclusive-tail/prefix mass. -/
theorem sizeGeEvent_prefixCylinder_real (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {n m : ℕ} {a : List ℕ} (ham : a.length = m) (hmn : m < n)
    (hs : IsSurvivingPrefix a) :
    (BGW.LocallyFinite.bienaymeLaw μ.toMeasure).real
      (Attraction.sizeGeEvent n ∩ prefixCylinder m a) =
        degreeWeight μ a * forestTail μ (prefixStack a) (n - m) := by
  have heq : Attraction.sizeGeEvent n ∩ prefixCylinder m a =
      ⋃ k : ℕ, BGW.LocallyFinite.sizeEvent (n + k) ∩ prefixCylinder m a := by
    ext T
    change ((¬BGW.LocallyFinite.FiniteVertices T ∨
      n ≤ {u | BGW.LocallyFinite.Present T u}.ncard) ∧ T ∈ prefixCylinder m a) ↔ _
    constructor
    · rintro ⟨hn, hp⟩
      have hn' := hn.resolve_left (not_not_intro hp.1)
      exact mem_iUnion.mpr ⟨{u | BGW.LocallyFinite.Present T u}.ncard - n,
        ⟨⟨hp.1, by omega⟩, hp⟩⟩
    · intro h
      obtain ⟨k, hk, hp⟩ := mem_iUnion.mp h
      exact ⟨Or.inr (by rw [hk.2]; omega), hp⟩
  have hdis : Pairwise (fun i j : ℕ => Disjoint
      (BGW.LocallyFinite.sizeEvent (n + i) ∩ prefixCylinder m a)
      (BGW.LocallyFinite.sizeEvent (n + j) ∩ prefixCylinder m a)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro T hi hj
    have h := hi.1.2.symm.trans hj.1.2
    omega
  rw [measureReal_def, heq, measure_iUnion hdis (fun k =>
    (BGW.LocallyFinite.measurableSet_sizeEvent _).inter (measurableSet_prefixCylinder m a)),
    ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  have ht (k : ℕ) :
      (BGW.LocallyFinite.bienaymeLaw μ.toMeasure
        (BGW.LocallyFinite.sizeEvent (n + k) ∩ prefixCylinder m a)).toReal =
      degreeWeight μ a * forestMass μ (prefixStack a) ((n - m) + k) := by
    have h := sizeEvent_prefixCylinder_real μ hc hne ham (show m < n + k by omega) hs
    have he : n + k - m = n - m + k := by omega
    simpa only [measureReal_def, he] using h
  simp_rw [ht]
  rw [tsum_mul_left, forestTail_eq_tsum_shift μ (prefixStack a) (n - m)
    (summable_forestMass μ (prefixStack a))]

end BGW.StableTrees.DiscreteForest
