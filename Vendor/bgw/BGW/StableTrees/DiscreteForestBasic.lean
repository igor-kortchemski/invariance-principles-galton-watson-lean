/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.RealAttraction
public import BGW.Tree.Height
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Discrete forest walks and record counts

The walk is indexed before exploration of a vertex. Heights count weak minima
among strictly preceding times, with both endpoints included in each tested interval.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical

namespace BGW.StableTrees.DiscreteForest

/-- The law of an iid sequence of offspring numbers with law `μ`, indexed from `0`. -/
noncomputable def offspringSeqLaw (μ : PMF ℕ) : ProbabilityMeasure (ℕ → ℕ) :=
  ⟨Measure.infinitePi (fun _ : ℕ => μ.toMeasure), inferInstance⟩

/-- The walk `W ω k = ∑_{i<k} (ω i - 1)`, with `W ω 0 = 0`. -/
def walk (ω : ℕ → ℕ) (k : ℕ) : ℤ := ∑ i ∈ Finset.range k, ((ω i : ℤ) - 1)

/-- The shifted offspring sequence `i ↦ ω (m + i)`. -/
def shiftSeq (m : ℕ) (ω : ℕ → ℕ) : ℕ → ℕ := fun i => ω (m + i)

/-- The record-count height of the infinite forest coded by `ω` at time `k`: the number of
weak running minima `j < k` of the walk seen from `k`, namely
`#{j < k | ∀ l ∈ [j,k], W_j ≤ W_l}`. -/
noncomputable def forestHeight (ω : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.range k).filter
    (fun j => ∀ l, j ≤ l → l ≤ k → walk ω j ≤ walk ω l)).card

/-- The minimum of the heights `H_m, ..., H_{m+k}`. -/
noncomputable def minHeight (ω : ℕ → ℕ) (m k : ℕ) : ℕ :=
  (Finset.range (k + 1)).inf' ⟨0, by simp⟩ (fun i => forestHeight ω (m + i))

/-- The height seen from time `m`: `H_{m+k} - min_{m≤j≤m+k} H_j` (an integer). -/
noncomputable def shiftedHeight (ω : ℕ → ℕ) (m k : ℕ) : ℤ :=
  (forestHeight ω (m + k) : ℤ) - (minHeight ω m k : ℤ)

/-- The walk of the shifted sequence is the increment of the walk after time `m`. -/
theorem walk_shiftSeq (ω : ℕ → ℕ) (m i : ℕ) :
    walk (shiftSeq m ω) i = walk ω (m + i) - walk ω m := by
  simp only [walk, shiftSeq, Finset.sum_range_add]
  omega

/-- The shifted path process is a measurable function of the shifted sequence. -/
theorem measurable_shiftSeq (m : ℕ) : Measurable (shiftSeq m) :=
  Measurable.of_eval fun i => measurable_pi_apply (m + i)

/-- Ladder times `L r = inf {k | W_k = -r}` (junk `0` if the set is empty). -/
noncomputable def ladderTime (ω : ℕ → ℕ) (r : ℕ) : ℕ := sInf {k | walk ω k = -(r : ℤ)}

/-- All ladder levels are reached. -/
def LadderFinite (ω : ℕ → ℕ) : Prop := ∀ r : ℕ, ∃ k, walk ω k = -(r : ℤ)

/-- `L 0 = 0`. -/
theorem ladderTime_zero (ω : ℕ → ℕ) : ladderTime ω 0 = 0 := by
  apply Nat.sInf_eq_zero.mpr
  left
  simp [walk]

/-- On `LadderFinite`, the walk at `L r` equals `-r`. -/
theorem walk_ladderTime {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    walk ω (ladderTime ω r) = -(r : ℤ) := Nat.sInf_mem (hω r)

private theorem walk_succ (ω : ℕ → ℕ) (k : ℕ) :
    walk ω (k + 1) = walk ω k + (ω k : ℤ) - 1 := by
  simp only [walk, Finset.sum_range_succ]
  ring

private theorem hit_level_of_le (ω : ℕ → ℕ) (r k : ℕ)
    (hk : walk ω k ≤ -(r : ℤ)) : ∃ i ≤ k, walk ω i = -(r : ℤ) := by
  induction k with
  | zero =>
    refine ⟨0, le_refl _, ?_⟩
    simp only [walk, Finset.range_zero, Finset.sum_empty] at hk ⊢
    omega
  | succ k ih =>
    by_cases h : walk ω k ≤ -(r : ℤ)
    · obtain ⟨i, hi, he⟩ := ih h
      exact ⟨i, hi.trans (Nat.le_succ _), he⟩
    · refine ⟨k + 1, le_refl _, ?_⟩
      have hs := walk_succ ω k
      have hn : (0 : ℤ) ≤ ω k := Int.natCast_nonneg _
      omega

/-- Before `L r`, the walk is strictly above `-r`. -/
theorem walk_gt_of_lt_ladderTime {ω : ℕ → ℕ} (hω : LadderFinite ω) {r k : ℕ}
    (hk : k < ladderTime ω r) : -(r : ℤ) < walk ω k := by
  by_contra h
  obtain ⟨i, hi, he⟩ := hit_level_of_le ω r k (by omega)
  have hglb := isGLB_csInf (s := {k | walk ω k = -(r : ℤ)}) (hω r)
    (OrderBot.bddBelow _)
  have hle : ladderTime ω r ≤ i := hglb.1 he
  omega

/-- Ladder times are strictly increasing (skip-free descent). -/
theorem ladderTime_lt_succ {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    ladderTime ω r < ladderTime ω (r + 1) := by
  have h := hit_level_of_le ω r (ladderTime ω (r + 1)) (by
    rw [walk_ladderTime hω]; omega)
  obtain ⟨i, hi, he⟩ := h
  have hle : ladderTime ω r ≤ i := Nat.sInf_le he
  have he' := walk_ladderTime hω (r + 1)
  have hne : i ≠ ladderTime ω (r + 1) := by
    intro heq
    rw [heq, he'] at he
    omega
  omega

/-- The `r`-th ladder time is at least `r`. -/
theorem le_ladderTime {ω : ℕ → ℕ} (hω : LadderFinite ω) (r : ℕ) :
    r ≤ ladderTime ω r :=
  (strictMono_nat_of_lt_succ (ladderTime_lt_succ hω)).le_apply

/-- Block exhaustion: every time lies in exactly one block `[L r, L (r+1))`. -/
theorem exists_ladderTime_le_lt {ω : ℕ → ℕ} (hω : LadderFinite ω) (k : ℕ) :
    ∃ r, ladderTime ω r ≤ k ∧ k < ladderTime ω (r + 1) := by
  have hstrict : StrictMono (ladderTime ω) := strictMono_nat_of_lt_succ (ladderTime_lt_succ hω)
  have hbound : k + 1 ≤ ladderTime ω (k + 1) := hstrict.id_le (k + 1)
  have hex : ∃ r, k < ladderTime ω r := ⟨k + 1, by omega⟩
  let r := Nat.find hex
  have hr : k < ladderTime ω r := Nat.find_spec hex
  have hrpos : 0 < r := by
    by_contra hn
    have hz : r = 0 := by omega
    rw [hz, ladderTime_zero] at hr
    omega
  refine ⟨r - 1, ?_, ?_⟩
  · have hn := Nat.find_min hex (show r - 1 < r by omega)
    omega
  · simpa only [Nat.sub_add_cancel hrpos] using hr

end BGW.StableTrees.DiscreteForest
