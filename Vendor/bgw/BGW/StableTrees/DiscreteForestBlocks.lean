/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestHeight
public import BGW.Tree.Excursion
public import BGW.Tree.LocallyFinite

/-!
# Decoding finite ladder blocks

On paths reaching every negative integer level, consecutive first-passage times
cut out finite tree excursions. Their record counts agree with DFS heights.
Each block is also viewed as a point of the locally finite tree space.
-/

@[expose] public section

open scoped Classical

namespace BGW.StableTrees.DiscreteForest

/-- The degree sequence of the `r`-th block `ω_{L r}, ..., ω_{L(r+1)-1}`. -/
noncomputable def blockDegrees (ω : ℕ → ℕ) (r : ℕ) : List ℕ :=
  (List.range (ladderTime ω (r + 1) - ladderTime ω r)).map (fun i => ω (ladderTime ω r + i))

/-- The `r`-th block tree, with a leaf fallback when decoding `blockDegrees` fails. -/
noncomputable def blockTree (ω : ℕ → ℕ) (r : ℕ) : PlaneTree :=
  (PlaneTree.ofDegrees? (blockDegrees ω r)).getD (PlaneTree.node [])

private theorem block_sum_take (ω : ℕ → ℕ) (r i : ℕ)
    (hi : i ≤ ladderTime ω (r + 1) - ladderTime ω r) :
    (((blockDegrees ω r).map (fun d : ℕ => (d : ℤ) - 1)).take i).sum =
      walk (shiftSeq (ladderTime ω r) ω) i := by
  simp only [blockDegrees, List.map_map, ← List.map_take, List.take_range,
    min_eq_left hi, walk, shiftSeq, Function.comp_def]
  have hsum (f : ℕ → ℤ) (n : ℕ) : (List.map f (List.range n)).sum =
      ∑ j ∈ Finset.range n, f j := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ, List.map_append, List.sum_append,
        Finset.sum_range_succ, ih]
  exact hsum _ _

private theorem block_is_excursion {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    IsTreeExcursion ((blockDegrees ω r).map (fun d : ℕ => (d : ℤ) - 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
    omega
  · have hi := block_sum_take ω r (ladderTime ω (r + 1) - ladderTime ω r) le_rfl
    have hlen : ((blockDegrees ω r).map (fun d : ℕ => (d : ℤ) - 1)).length =
        ladderTime ω (r + 1) - ladderTime ω r := by simp [blockDegrees]
    have htake : (((blockDegrees ω r).map (fun d : ℕ => (d : ℤ) - 1)).take
        (ladderTime ω (r + 1) - ladderTime ω r)) =
        (blockDegrees ω r).map (fun d : ℕ => (d : ℤ) - 1) := by
      rw [← hlen, List.take_length]
    rw [htake] at hi
    rw [hi, walk_shiftSeq,
      Nat.add_sub_of_le (ladderTime_lt_succ hω r).le, walk_ladderTime hω,
      walk_ladderTime hω]
    omega
  · intro i hi
    simp only [List.length_map, blockDegrees, List.length_range] at hi
    rw [block_sum_take ω r i hi.le, walk_shiftSeq, walk_ladderTime hω]
    have hgt := walk_gt_of_lt_ladderTime hω
      (r := r + 1) (k := ladderTime ω r + i) (by omega)
    omega

/-- On `LadderFinite`, the block decodes to a tree with the block's degrees. -/
theorem degrees_blockTree {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    (blockTree ω r).degrees = blockDegrees ω r := by
  obtain ⟨t, ht, _⟩ := (PlaneTree.isTreeExcursion_iff_existsUnique _).mp
    (block_is_excursion hω r)
  have hd : t.degrees = blockDegrees ω r := by
    have h := congrArg (List.map (fun x : ℤ => (x + 1).toNat)) ht
    simp only [PlaneTree.increments, List.map_map, Function.comp_def,
      Int.sub_add_cancel, Int.toNat_natCast] at h
    change t.degrees.map id = (blockDegrees ω r).map id at h
    simpa only [List.map_id] using h
  have hparse := PlaneTree.ofDegrees?_eq_some_iff.mpr hd
  simp only [blockTree, hparse, Option.getD_some]
  exact hd

/-- The size of the `r`-th block tree is `L (r+1) - L r`. -/
theorem size_blockTree {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    (blockTree ω r).size = ladderTime ω (r + 1) - ladderTime ω r := by
  rw [← PlaneTree.length_degrees, degrees_blockTree hω]
  simp [blockDegrees]

private theorem height_ladderTime {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    forestHeight ω (ladderTime ω r) = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro j hj hrecord
  have hjlt := Finset.mem_range.mp hj
  have hle := hrecord (ladderTime ω r) hjlt.le le_rfl
  rw [walk_ladderTime hω] at hle
  have hgt := walk_gt_of_lt_ladderTime hω hjlt
  omega

/-- The record-count height of the forest equals the tree height on each block. -/
theorem forestHeight_eq_treeHeight {ω : ℕ → ℕ} (hω : LadderFinite ω) (r i : ℕ)
    (hi : i < (blockTree ω r).size) :
    forestHeight ω (ladderTime ω r + i) = (blockTree ω r).height ⟨i, hi⟩ := by
  have hmin : minHeight ω (ladderTime ω r) i = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact (Finset.inf'_le _ (by simp : 0 ∈ Finset.range (i + 1))).trans_eq
      (by simpa using height_ladderTime hω r)
  have hshift := shiftedHeight_eq ω (ladderTime ω r) i
  simp only [shiftedHeight, hmin, Int.natCast_zero, sub_zero] at hshift
  have heq : forestHeight ω (ladderTime ω r + i) =
      forestHeight (shiftSeq (ladderTime ω r) ω) i := by exact_mod_cast hshift
  rw [heq, PlaneTree.height_eq_card_recordMin]
  have hw (k : ℕ) (hk : k ≤ i) :
      walk (shiftSeq (ladderTime ω r) ω) k = (blockTree ω r).lukasiewicz k := by
    have hklen : k ≤ ladderTime ω (r + 1) - ladderTime ω r := by
      rw [← size_blockTree hω r]
      omega
    rw [← block_sum_take ω r k hklen]
    simp only [PlaneTree.lukasiewicz, PlaneTree.increments, degrees_blockTree hω]
  unfold forestHeight
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j hj
  have hji := Finset.mem_range.mp hj
  constructor <;> intro h l hjl hli
  · rw [← hw j hji.le, ← hw l hli]
    exact h l hjl hli
  · rw [hw j hji.le, hw l hli]
    exact h l hjl hli

/-- The block as a point of the locally finite tree space. -/
noncomputable def blockLF (ω : ℕ → ℕ) (r : ℕ) : BGW.LocallyFinite.Tree :=
  (blockTree ω r).toLocallyFinite

end BGW.StableTrees.DiscreteForest
