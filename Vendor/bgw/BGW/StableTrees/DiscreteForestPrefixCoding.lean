/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestBridge
public import BGW.StableTrees.DiscreteForestHitMass
public import BGW.StableTrees.DiscreteForestLongTree

/-!
# Surviving prefixes and the remaining forest

After a surviving prefix, the remaining pending subtrees are counted by the
prefix stack. First passage to minus that stack is exactly completion of the
first tree. This is a deterministic finite-word statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Classical

namespace BGW.StableTrees.DiscreteForest

/-- A local discrete structure for finite prefix words. -/
local instance prefixCodingWordMeasurable : MeasurableSpace (List ℕ) := ⊤
/-- Prefix-word singletons are measurable in the local structure. -/
local instance prefixCodingWordSingleton : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

/-- The finite-tree bridge preserves the DFS prefix observable. -/
theorem treePrefix_toLocallyFinite (m : ℕ) (t : PlaneTree) :
    treePrefix m t.toLocallyFinite = t.degrees.take m := by
  rw [treePrefix, dite_eq_left t.finiteVertices_toLocallyFinite]
  change (PlaneTree.equivFiniteVertices.symm (PlaneTree.equivFiniteVertices t)).degrees.take m = _
  rw [Equiv.symm_apply_apply]

/-- Prefix cylinders are countable images of finite trees. -/
theorem prefixCylinder_eq_image (m : ℕ) (a : List ℕ) :
    prefixCylinder m a = PlaneTree.toLocallyFinite '' {t | t.degrees.take m = a} := by
  ext T
  constructor
  · rintro ⟨hT, hpre⟩
    obtain ⟨t, rfl⟩ := (BGW.LocallyFinite.exists_toLocallyFinite_iff T).mpr hT
    exact ⟨t, by rwa [treePrefix_toLocallyFinite] at hpre, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t.finiteVertices_toLocallyFinite, by rwa [treePrefix_toLocallyFinite]⟩

/-- Every finite prefix cylinder is measurable. -/
theorem measurableSet_prefixCylinder (m : ℕ) (a : List ℕ) :
    MeasurableSet (prefixCylinder m a) := by
  rw [prefixCylinder_eq_image]
  exact ((Set.to_countable _).image _).measurableSet

/-- The totalized tree-prefix observable is measurable. -/
theorem measurable_treePrefix (m : ℕ) : Measurable (treePrefix m) := by
  apply measurable_to_countable'
  intro a
  have heq : treePrefix m ⁻¹' {a} = prefixCylinder m a ∪
      if a = [] then {T | BGW.LocallyFinite.FiniteVertices T}ᶜ else ∅ := by
    ext T
    by_cases hT : BGW.LocallyFinite.FiniteVertices T <;>
      simp [treePrefix, prefixCylinder, hT, eq_comm]
  rw [heq]
  apply (measurableSet_prefixCylinder m a).union
  split_ifs
  · exact BGW.LocallyFinite.measurableSet_finiteVertices.compl
  · exact MeasurableSet.empty

/-- The pending-stack integer of a surviving prefix is its walk value plus one. -/
theorem prefixStack_cast {a : List ℕ} (hs : IsSurvivingPrefix a) :
    (prefixStack a : ℤ) = prefixWalk a + 1 := by
  have hn : 0 ≤ prefixWalk a := by
    have h := hs a.length le_rfl
    simpa only [prefixWalk, List.take_length] using h
  change ((prefixWalk a + 1).toNat : ℤ) = prefixWalk a + 1
  exact Int.toNat_of_nonneg (by omega)

/-- A surviving prefix always leaves a positive number of pending subtrees. -/
theorem prefixStack_pos {a : List ℕ} (hs : IsSurvivingPrefix a) : 1 ≤ prefixStack a := by
  have hn : 0 ≤ prefixWalk a := by
    have h := hs a.length le_rfl
    simpa only [prefixWalk, List.take_length] using h
  have hc := prefixStack_cast hs
  omega

/-- Completing the first tree after a surviving prefix is first passage for its pending forest. -/
theorem prefix_ladder_iff_forestHit {ω : ℕ → ℕ} (hω : LadderFinite ω)
    {n m : ℕ} {a : List ℕ} (ham : a.length = m) (hmn : m < n)
    (hs : IsSurvivingPrefix a) :
    (seqPrefix m ω = a ∧ ladderTime ω 1 = n) ↔
      (seqPrefix m ω = a ∧ shiftSeq m ω ∈ forestHit (prefixStack a) (n - m)) := by
  have hj := prefixStack_cast hs
  have hw (ha : seqPrefix m ω = a) : walk ω m = prefixWalk a := by
    rw [← prefixWalk_seqPrefix, ha]
  constructor
  · rintro ⟨ha, hL⟩
    refine ⟨ha, ?_, ?_⟩
    · have hend := walk_ladderTime hω 1
      rw [hL] at hend
      rw [walk_shiftSeq, Nat.add_sub_of_le hmn.le, hend, hw ha]
      omega
    · intro i hi
      have hgt := walk_gt_of_lt_ladderTime hω (r := 1) (k := m + i) (by omega)
      rw [walk_shiftSeq, hw ha]
      omega
  · rintro ⟨ha, hend, hpre⟩
    have hn : walk ω n = -1 := by
      rw [walk_shiftSeq, Nat.add_sub_of_le hmn.le, hw ha] at hend
      omega
    have hnpre (i : ℕ) (hi : i < n) : 0 ≤ walk ω i := by
      by_cases him : i ≤ m
      · have h := hs i (by omega)
        change 0 ≤ prefixWalk (a.take i) at h
        rw [← ha, take_seqPrefix m i ω him, prefixWalk_seqPrefix] at h
        exact h
      · have h := hpre (i - m) (by omega)
        rw [walk_shiftSeq, Nat.add_sub_of_le (by omega : m ≤ i), hw ha] at h
        omega
    have hle : ladderTime ω 1 ≤ n := Nat.sInf_le hn
    have he : ladderTime ω 1 = n := by
      by_contra hne
      have hp := hnpre (ladderTime ω 1) (by omega)
      rw [walk_ladderTime hω 1] at hp
      omega
    exact ⟨ha, he⟩

/-- The first decoded block has length equal to its first ladder time. -/
theorem first_block_size {ω : ℕ → ℕ} (hω : LadderFinite ω) :
    (blockTree ω 0).size = ladderTime ω 1 := by
  rw [size_blockTree hω, ladderTime_zero]
  simp

/-- Prefixes within the first block are exactly initial offspring prefixes. -/
theorem treePrefix_first_block {ω : ℕ → ℕ} (hω : LadderFinite ω) (m : ℕ)
    (hm : m ≤ ladderTime ω 1) : treePrefix m (blockLF ω 0) = seqPrefix m ω := by
  rw [blockLF, treePrefix_toLocallyFinite, degrees_blockTree hω]
  simp only [blockDegrees, ladderTime_zero, Nat.sub_zero, zero_add]
  exact take_seqPrefix (ladderTime ω 1) m ω hm

/-- The first block has the unconditioned BGW law. -/
theorem first_block_law (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    (offspringSeqLaw μ).toMeasure.map (fun ω => blockLF ω 0) =
      BGW.LocallyFinite.bienaymeLaw μ.toMeasure := by
  have h := congrArg (fun M : Measure (ℕ → BGW.LocallyFinite.Tree) =>
    M.map (fun x => x 0)) (blockTrees_law μ hc hne)
  rw [Measure.map_map (measurable_pi_apply 0) measurable_blockLF,
    Measure.infinitePi_map_eval] at h
  exact h

end BGW.StableTrees.DiscreteForest
