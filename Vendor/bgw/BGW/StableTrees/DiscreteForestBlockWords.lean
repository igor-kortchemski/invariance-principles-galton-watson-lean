/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestBlocks
public import BGW.StableTrees.DiscreteForestLadder
public import BGW.StableTrees.DiscreteForestWordMass
import BGW.Tree.Forest

/-!
# Finite cylinders of consecutive ladder blocks

Concatenated degree words locate each ladder boundary without using a random
restart. Conversely the first finitely many ladder blocks concatenate to the
corresponding initial offspring word.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Classical

namespace BGW.StableTrees.DiscreteForest

/-- Splitting an offspring prefix at a deterministic time concatenates degree words. -/
theorem seqPrefix_add (m n : ℕ) (ω : ℕ → ℕ) :
    seqPrefix (m + n) ω = seqPrefix m ω ++ seqPrefix n (shiftSeq m ω) := by
  simp [seqPrefix, List.range_add, List.map_append, List.map_map, shiftSeq, Function.comp_def]

private theorem forest_degrees_length (ts : PlaneForest) :
    (PlaneForest.degrees ts).length = PlaneForest.size ts := by
  simp only [PlaneForest.degrees, List.length_flatten, List.map_map]
  change (ts.map (fun t => t.degrees.length)).sum = (ts.map PlaneTree.size).sum
  congr 1
  exact List.map_congr_left fun t _ => PlaneTree.length_degrees t

private theorem forest_steps_degrees (ts : PlaneForest) :
    (PlaneForest.degrees ts).map (fun d : ℕ => (d : ℤ) - 1) = PlaneForest.increments ts := by
  simp only [PlaneForest.degrees, List.map_flatten, List.map_map, Function.comp_def]
  rfl

/-- A finite forest word ends at the first hitting of minus its number of roots. -/
theorem ladderTime_of_forest_prefix (ω : ℕ → ℕ) (ts : PlaneForest)
    (hpre : seqPrefix (PlaneForest.size ts) ω = PlaneForest.degrees ts) :
    ladderTime ω ts.length = PlaneForest.size ts := by
  have hw (i : ℕ) (hi : i ≤ PlaneForest.size ts) :
      walk ω i = ((PlaneForest.increments ts).take i).sum := by
    rw [← forest_steps_degrees, ← hpre, ← List.map_take,
      take_seqPrefix _ _ _ hi, sum_seqPrefix]
  have hend : walk ω (PlaneForest.size ts) = -(ts.length : ℤ) := by
    rw [hw _ le_rfl, ← PlaneForest.length_increments ts, List.take_length,
      PlaneForest.sum_increments]
  have hle : ladderTime ω ts.length ≤ PlaneForest.size ts := Nat.sInf_le hend
  have hhit : walk ω (ladderTime ω ts.length) = -(ts.length : ℤ) :=
    Nat.sInf_mem (s := {k | walk ω k = -(ts.length : ℤ)}) ⟨_, hend⟩
  apply le_antisymm hle
  by_contra hn
  have hlt : ladderTime ω ts.length < PlaneForest.size ts := by omega
  have hgt := PlaneForest.sum_take_increments_gt ts
    (i := ladderTime ω ts.length) (by simpa using hlt)
  rw [← hw _ hle, hhit] at hgt
  omega

/-- The first `r` decoded trees in component order. -/
noncomputable def blockPrefix (r : ℕ) (ω : ℕ → ℕ) : PlaneForest :=
  List.ofFn (fun i : Fin r => blockTree ω i)

/-- The first finitely many blocks concatenate to the initial offspring word. -/
theorem degrees_blockPrefix {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    PlaneForest.degrees (blockPrefix r ω) = seqPrefix (ladderTime ω r) ω := by
  induction r with
  | zero => simp [blockPrefix, ladderTime_zero, seqPrefix]
  | succ r ih =>
    have hs : blockPrefix (r + 1) ω = blockPrefix r ω ++ [blockTree ω r] := by
      change List.ofFn (fun i : Fin (r + 1) => blockTree ω i) = _
      rw [List.ofFn_succ', List.concat_eq_append]
      rfl
    rw [hs, PlaneForest.degrees_append, PlaneForest.degrees_cons,
      PlaneForest.degrees_nil, List.append_nil, ih, degrees_blockTree hω]
    have hle := (ladderTime_lt_succ hω r).le
    rw [show ladderTime ω (r + 1) = ladderTime ω r +
      (ladderTime ω (r + 1) - ladderTime ω r) by omega, seqPrefix_add]
    rfl

/-- A forest degree-word cylinder is exactly a cylinder of initial ladder trees. -/
theorem blockPrefix_eq_iff {ω : ℕ → ℕ} (hω : LadderFinite ω) (ts : PlaneForest) :
    blockPrefix ts.length ω = ts ↔
      seqPrefix (PlaneForest.size ts) ω = PlaneForest.degrees ts := by
  constructor
  · intro h
    have hd := degrees_blockPrefix hω ts.length
    rw [h] at hd
    have hl := congrArg List.length hd
    simp only [forest_degrees_length, seqPrefix, List.length_map, List.length_range] at hl
    rw [← hl] at hd
    exact hd.symm
  · intro h
    apply PlaneForest.degrees_injective
    rw [degrees_blockPrefix hω, ladderTime_of_forest_prefix ω ts h]
    exact h

/-- The mass of a cylinder prescribing the first finitely many tree blocks. -/
theorem blockPrefix_mass (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (ts : PlaneForest) :
    (offspringSeqLaw μ).toMeasure {ω | blockPrefix ts.length ω = ts} =
      (ts.map (PlaneTree.weight μ)).prod := by
  have heq : {ω | blockPrefix ts.length ω = ts} =ᵐ[(offspringSeqLaw μ).toMeasure]
      {ω | seqPrefix (PlaneForest.size ts) ω = PlaneForest.degrees ts} := by
    filter_upwards [ae_ladderFinite μ hc hne] with ω hω
    exact propext (blockPrefix_eq_iff hω ts)
  rw [measure_congr heq, ← forest_degrees_length ts, seqPrefix_mass]
  simp only [PlaneForest.degrees, List.map_flatten, List.prod_flatten,
    List.map_map, Function.comp_def]
  rfl

end BGW.StableTrees.DiscreteForest
